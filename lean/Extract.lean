-- Appended after a trusted source file (import Lean is added by the driver).
-- The output is an explanatory tree, NOT a lossless Expr serialization.
namespace LeanDuetExtract
open Lean Meta Elab Command

def node (path : String) (editable : Bool) (scope : Array Json) (kind term type : String) (children : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("kind", toJson kind), ("term", toJson term), ("type", toJson type),
    ("children", Json.arr children), ("path", toJson path), ("editable", toJson editable), ("scope", Json.arr scope)] ++ extra)

-- Preserve variable occurrences and proof constructors: not definitional equality.
-- Alpha-renaming and source metadata are intentionally ignored.
partial def shape (e : Expr) : Expr :=
  match e with
  | .mdata _ b => shape b
  | .lam _ t b bi => .lam .anonymous (shape t) (shape b) bi
  | .forallE _ t b bi => .forallE .anonymous (shape t) (shape b) bi
  | .letE _ t v b _ => .letE .anonymous (shape t) (shape v) (shape b) false
  | .app f a => .app (shape f) (shape a)
  | .proj n i b => .proj n i (shape b)
  | _ => e

def sameShape (a b : Expr) : Bool := Expr.equal (shape a) (shape b)

/-- A declaration depends on an earlier declaration through its type or let value.
    This is a syntactic relation on local free-variable identities. -/
def declDepends (d : LocalDecl) (id : FVarId) : Bool :=
  d.type.containsFVar id || (match d.value? with
    | some v => v.containsFVar id
    | none => false)

/-- The local context is ordered by introduction. Close the used declarations
    backwards through their dependent types and local definitions. -/
def referencedContext (goal term : Expr) : MetaM (Array LocalDecl × Array FVarId) := do
  let mut locals : Array LocalDecl := #[]
  for d in (← getLCtx) do
    locals := locals.push d
  let mut needed : Array FVarId := #[]
  for d in locals do
    if term.containsFVar d.fvarId || goal.containsFVar d.fvarId then
      needed := needed.push d.fvarId
  for d in locals.reverse do
    if needed.contains d.fvarId then
      for earlier in locals do
        if earlier.index < d.index && declDepends d earlier.fvarId && !needed.contains earlier.fvarId then
          needed := needed.push earlier.fvarId
  return (locals, needed)

/-- Display the same dependency closure used for proof abstraction. -/
def localScope (goal : Expr) (editable : Bool) (term : Expr) : MetaM (Array Json) := do
  let (locals, needed) ← referencedContext goal term
  let mut entries := #[]
  for d in locals do
    if !d.isImplementationDetail then
      let matchesType ← if editable then isDefEq d.type goal else pure false
      let mut dependencies : Array Json := #[]
      let mut hiddenDependencies := 0
      for earlier in locals do
        if earlier.index < d.index && declDepends d earlier.fvarId then
          if earlier.isImplementationDetail then
            hiddenDependencies := hiddenDependencies + 1
          else
            dependencies := dependencies.push (toJson earlier.index)
      entries := entries.push (Json.mkObj [
        ("matchesGoal", toJson matchesType), ("name", toJson d.userName.toString),
        ("contextIndex", toJson d.index), ("dependsOn", Json.arr dependencies),
        ("hiddenDependencies", toJson hiddenDependencies),
        ("usedInTerm", toJson (term.containsFVar d.fvarId)),
        ("usedInType", toJson (goal.containsFVar d.fvarId)),
        ("neededForContext", toJson (needed.contains d.fvarId)),
        ("type", toJson (← ppExpr d.type).pretty)])
  return entries

-- Bounded local application search. Instantiate a single explicit dependent
-- binder with a local object, then compare the resulting proposition in Lean.
def localApplications (goal : Expr) : MetaM (Array Json) := do
  let mut locals : Array LocalDecl := #[]
  for d in (← getLCtx) do
    if !d.isImplementationDetail && locals.size < 24 then
      locals := locals.push d
  let mut results := #[]
  for f in locals do
    let ty ← whnf f.type
    match ty with
    | .forallE _ domain body .default =>
      for a in locals do
        if results.size < 8 then
          if ← isDefEq a.type domain then
            let resultType := body.instantiate1 (mkFVar a.fvarId)
            if ← isDefEq resultType goal then
              results := results.push (Json.mkObj [
                ("function", toJson f.userName.toString),
                ("argument", toJson a.userName.toString),
                ("type", toJson (← ppExpr resultType).pretty)])
    | _ => pure ()
  return results

def isWitnessArg (head : Expr) (i : Nat) : Bool :=
  match head with
  | .const n _ => n == `Exists.intro && i == 2
  | _ => false

partial def inspect (e : Expr) (fuel : Nat) (path : String := "root") (suggestions : Bool := true) : MetaM Json := do
  let term := (← ppExpr e).pretty
  let ty ← inferType e
  let typ := (← ppExpr ty).pretty
  let editable ← isProp ty
  let scope ← localScope ty editable e
  if fuel == 0 then return node path editable scope "opaque" term typ #[] [("truncated", toJson true)]
  match e with
  | .lam n t b bi =>
      let binderType := (← ppExpr t).pretty
      let kind := if ← isProp t then "assume" else "introduce"
      withLocalDecl n bi t fun x => do
        let child ← inspect (b.instantiate1 x) (fuel - 1) (path ++ "/body") suggestions
        return node path editable scope kind term typ #[child]
          [("binder", toJson n.toString), ("binderType", toJson binderType)]
  | .letE n t v b _ =>
      let binderType := (← ppExpr t).pretty
      let value ← inspect v (fuel - 1) (path ++ "/value") suggestions
      withLetDecl n t v fun x => do
        let body ← inspect (b.instantiate1 x) (fuel - 1) (path ++ "/body") suggestions
        return node path editable scope "let" term typ #[value, body]
          [("binder", toJson n.toString), ("binderType", toJson binderType)]
  | .app .. =>
      let alternatives ← if editable && suggestions then localApplications ty else pure #[]
      let head := e.getAppFn
      let headText := (← ppExpr head).pretty
      let headType := (← ppExpr (← inferType head)).pretty
      let mut children := #[]
      let mut omittedProofArguments := 0
      let args := e.getAppArgs
      for i in [:args.size] do
        let a := args[i]!
        let argPath := path ++ "/arg" ++ toString i
        if isWitnessArg head i then
          let aType ← inferType a
          let aScope ← localScope aType true a
          children := children.push (node argPath true aScope "witness"
            (← ppExpr a).pretty (← ppExpr aType).pretty)
        else if ← isProp (← inferType a) then
          if children.size < 8 then
            children := children.push (← inspect a (fuel - 1) argPath suggestions)
          else
            omittedProofArguments := omittedProofArguments + 1
      let ref := match head with
        | .const n _ => n.toString
        | _ => headText
      return node path editable scope "apply" term typ children
        [("reference", toJson ref), ("referenceType", toJson headType), ("applications", Json.arr alternatives), ("argumentCount", toJson args.size),
          ("omittedProofArguments", toJson omittedProofArguments)]
  | .const n _ => return node path editable scope "reference" term typ #[] [("reference", toJson n.toString)]
  | .fvar _ => return node path editable scope "hypothesis" term typ
  | .mdata _ body => inspect body (fuel - 1) path suggestions
  | _ => return node path editable scope "opaque" term typ

elab "#duet_extract " n:ident : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      let result ← inspect v.value 10
      let j := Json.mkObj [("schema", toJson (1 : Nat)), ("declaration", toJson n.getId.toString),
        ("tree", result)]
      logInfo m!"LEANDUET_JSON:{j.compress}"
    | _ => throwError "Expected a theorem"

/-- Reading-only profile: do not search alternative local applications at every occurrence. -/
elab "#duet_extract_fast " n:ident : command => do
  liftTermElabM do
    let .thmInfo v ← getConstInfo n.getId | throwError "Expected a theorem"
    let result ← inspect v.value 10 "root" false
    let j := Json.mkObj [("schema", toJson (1 : Nat)), ("declaration", toJson n.getId.toString),
      ("profile", toJson "reading"), ("tree", result)]
    logInfo m!"LEANDUET_JSON:{j.compress}"

/-- Rebuild exactly one expression path, elaborating the replacement in its actual scope. -/
partial def replaceAt (e : Expr) (path : List String) (stx : Syntax)
    (allowWitness : Bool := false) : TermElabM (Expr × String × String) := do
  match path with
  | [] =>
    let ty ← inferType e
    unless allowWitness || (← isProp ty) do throwError "Only proofs and existential witness positions are editable"
    let value ← Term.elabTermEnsuringType stx (some ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then throwError "Unresolved metavariables in replacement"
    Lean.Meta.check value
    unless ← isDefEq (← inferType value) ty do throwError "Replacement has the wrong local type"
    return (value, (← ppExpr ty).pretty, (← ppExpr e).pretty)
  | p :: rest =>
    match e with
    | .mdata md body =>
      let (v, ty, old) ← replaceAt body path stx
      return (.mdata md v, ty, old)
    | .lam n t b bi =>
      unless p == "body" do throwError "Invalid lambda path"
      withLocalDecl n bi t fun x => do
        let (v, ty, old) ← replaceAt (b.instantiate1 x) rest stx
        return (.lam n t (v.abstract #[x]) bi, ty, old)
    | .letE n t v b nd =>
      if p == "value" then
        let (v', ty, old) ← replaceAt v rest stx
        return (.letE n t v' b nd, ty, old)
      else if p == "body" then
        withLetDecl n t v fun x => do
          let (b', ty, old) ← replaceAt (b.instantiate1 x) rest stx
          return (.letE n t v (b'.abstract #[x]) nd, ty, old)
      else throwError "Invalid let path"
    | .app .. =>
      unless p.startsWith "arg" do throwError "Invalid application path"
      let some i := (String.mk (p.toList.drop 3)).toNat? | throwError "Invalid argument index"
      let args := e.getAppArgs
      unless i < args.size do throwError "Argument index out of bounds"
      let (v, ty, old) ← replaceAt args[i]! rest stx (isWitnessArg e.getAppFn i && rest.isEmpty)
      return (mkAppN e.getAppFn (args.set! i v), ty, old)
    | _ => throwError "Invalid expression path"

/-- No self-reference, including auxiliary declarations under the theorem name. -/
partial def mentions (e : Expr) (forbidden : Name) : Bool :=
  match e with
  | .const n _ => forbidden.isPrefixOf n
  | .app f a => mentions f forbidden || mentions a forbidden
  | .lam _ t b _ | .forallE _ t b _ => mentions t forbidden || mentions b forbidden
  | .letE _ t v b _ => mentions t forbidden || mentions v forbidden || mentions b forbidden
  | .mdata _ b | .proj _ _ b => mentions b forbidden
  | _ => false

/-- Read the actual type of an intermediate fact after Lean elaborates it.
    This tactic only inspects the local context; it does not solve a goal. -/
elab "duet_trace " n:ident : tactic => Elab.Tactic.withMainContext do
  let mut found : Array LocalDecl := #[]
  for d in (← getLCtx) do
    if !d.isImplementationDetail && d.userName == n.getId then
      found := found.push d
  unless found.size == 1 do throwError "Intermediate fact is missing or ambiguous: {n.getId}"
  let ty ← instantiateMVars found[0]!.type
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "The intermediate fact has unresolved type information: {n.getId}"
  unless ← isProp ty do throwError "An intermediate fact must be a proposition: {n.getId}"
  let j := Json.mkObj [("name", toJson n.getId.toString), ("type", toJson (← ppExpr ty).pretty)]
  logInfo m!"LEANDUET_BINDING:{j.compress}"

elab "#duet_patch " n:ident path:str replacement:str : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      unless v.levelParams.isEmpty do
        throwError "Universe-polymorphic theorem export is not yet supported"
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      let stx ← match Parser.runParserCategory (← getEnv) `term replacement.getString with
        | .ok stx => pure stx
        | .error err => throwError "{err}"
      let (newProof, localType, oldTerm) ← replaceAt v.value (parts.drop 1) stx
      if newProof.hasMVar || newProof.hasLevelMVar || newProof.hasFVar || newProof.hasLooseBVars then
        throwError "Rebuilt proof is not closed"
      if mentions newProof n.getId || mentions newProof `sorryAx then
        throwError "Replacement refers to the original theorem or an incomplete proof"
      Lean.Meta.check newProof
      unless ← isDefEq (← inferType newProof) v.type do
        throwError "The entire proof no longer has the original type"
      -- Declaration types must stand alone, without expected-type information.
      let typeText ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true |>.setBool `pp.piBinderTypes true |>.setBool `pp.explicit true |>.setBool `pp.notation false) do
        pure (← ppExpr v.type).pretty
      let termText ← withOptions (fun o => o.setBool `pp.fullNames true) do
        pure (← ppExpr newProof).pretty
      let j := Json.mkObj [("schema", toJson (1 : Nat)), ("type", toJson typeText),
        ("term", toJson termText), ("localType", toJson localType), ("oldTerm", toJson oldTerm),
        ("unchanged", toJson (sameShape newProof v.value))]
      logInfo m!"LEANDUET_JSON:{j.compress}"
    | _ => throwError "Expected a theorem"

elab "#duet_compare " n:ident m:ident path:str replacement:str : command => do
  liftTermElabM do
    let a ← getConstInfo n.getId
    let b ← getConstInfo m.getId
    unless ← isDefEq a.type b.type do throwError "Candidate declaration type changed"
    match a, b with
    | .thmInfo x, .thmInfo y =>
      let stx ← match Parser.runParserCategory (← getEnv) `term replacement.getString with
        | .ok stx => pure stx
        | .error err => throwError "{err}"
      let (expected, _, _) ← replaceAt x.value ((path.getString.splitOn "/").drop 1) stx
      unless sameShape expected y.value do
        throwError "Re-elaborated export does not preserve the requested proof structure"
      logInfo "LEANDUET_TYPE_AND_SHAPE_MATCH"
    | _, _ => throwError "Expected two theorems"


/-- Traverse a selected occurrence under exactly its original binders. -/
partial def withNodeAt {α : Type} (e : Expr) (path : List String)
    (k : Expr → TermElabM α) : TermElabM α := do
  match path with
  | [] => k e
  | p :: rest =>
    match e with
    | .mdata _ b => withNodeAt b path k
    | .lam n t b bi =>
      unless p == "body" do throwError "Invalid lambda path"
      withLocalDecl n bi t fun x => withNodeAt (b.instantiate1 x) rest k
    | .letE n t v b _ =>
      if p == "value" then withNodeAt v rest k
      else if p == "body" then
        withLetDecl n t v fun x => withNodeAt (b.instantiate1 x) rest k
      else throwError "Invalid let path"
    | .app .. =>
      unless p.startsWith "arg" do throwError "Invalid application path"
      let some i := (String.mk (p.toList.drop 3)).toNat? | throwError "Invalid argument index"
      let args := e.getAppArgs
      unless i < args.size do throwError "Argument index out of bounds"
      withNodeAt args[i]! rest k
    | _ => throwError "Invalid expression path"


/-- Structural names preserve numeric components and dots inside individual
    components; display strings alone do not suffice for serialization. -/
def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[encodeName p, toJson "str", toJson s]
  | .num p n => Json.arr #[encodeName p, toJson "num", toJson (toString n)]

def encodeLevel : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", encodeLevel u]
  | .max u v => Json.arr #[toJson "max", encodeLevel u, encodeLevel v]
  | .imax u v => Json.arr #[toJson "imax", encodeLevel u, encodeLevel v]
  | .param n => Json.arr #[toJson "param", encodeName n]
  | .mvar _ => Json.arr #[toJson "unresolved"]

def binderTag : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

-- A separate on-demand representation, not the bounded explanatory tree.
-- All kernel constructors are preserved except source metadata; unresolved
-- variables and exhausted budgets are rejected, not represented as proofs.
partial def encodeExpr (e : Expr) (fuel : Nat := 96) (depth : Nat := 0) :
    StateT Nat MetaM Json := do
  let budget ← get
  if fuel == 0 || budget == 0 then
    throwError "Semantic IR exceeds the structural inspection limit"
  set (budget - 1)
  let next := fuel - 1
  let tag (s : String) (a : Array Json) := Json.arr (#[toJson s] ++ a)
  match e with
  | .bvar i =>
    unless i < depth do throwError "Loose bound variable in IR"
    return tag "bound" #[toJson i]
  | .fvar id =>
    for d in (← getLCtx) do
      if d.fvarId == id then return tag "local" #[toJson d.index]
    throwError "Unknown free variable in IR"
  | .mvar _ => throwError "Unresolved metavariable in IR"
  | .sort u => return tag "sort" #[encodeLevel u]
  | .const n us => return tag "const" #[encodeName n, Json.arr (us.toArray.map encodeLevel)]
  | .app f a => return tag "app" #[← encodeExpr f next depth, ← encodeExpr a next depth]
  | .lam n t b bi =>
    return tag "lambda" #[encodeName n, toJson (binderTag bi), ← encodeExpr t next depth,
      ← encodeExpr b next (depth + 1)]
  | .forallE n t b bi =>
    return tag "pi" #[encodeName n, toJson (binderTag bi), ← encodeExpr t next depth,
      ← encodeExpr b next (depth + 1)]
  | .letE n t v b nd =>
    return tag "let" #[encodeName n, ← encodeExpr t next depth, ← encodeExpr v next depth,
      ← encodeExpr b next (depth + 1), toJson nd]
  | .lit (.natVal n) => return tag "nat" #[toJson (toString n)]
  | .lit (.strVal s) => return tag "string" #[toJson s]
  | .mdata _ b => encodeExpr b next depth
  | .proj n i b => return tag "projection" #[encodeName n, toJson i, ← encodeExpr b next depth]

def checkedEncode (e : Expr) : StateT Nat MetaM Json := do
  if e.hasMVar || e.hasLevelMVar then
    throwError "Unresolved term or universe metavariable in IR"
  encodeExpr e


/-- Decode only the schema's exact constructors. Slots are resolved against
    the selected local context, never by pretty-printed identifier. -/
def parseDecimal (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "Invalid decimal natural"
  unless toString n == s do throw "Noncanonical decimal natural"
  return n

def decodeName (j : Json) (fuel : Nat := 96) : Except String Name :=
  match fuel with
  | 0 => throw "Name nesting limit"
  | fuel + 1 => do
    let a ← j.getArr?
    if a.isEmpty then return .anonymous
    unless a.size == 3 do throw "Invalid structural name"
    let p ← decodeName a[0]! fuel
    match ← a[1]!.getStr? with
    | "str" => return .str p (← a[2]!.getStr?)
    | "num" => return .num p (← parseDecimal a[2]!)
    | _ => throw "Unknown name constructor"
termination_by structural fuel

def decodeLevel (j : Json) (fuel : Nat := 96) : Except String Level :=
  match fuel with
  | 0 => throw "Universe nesting limit"
  | fuel + 1 => do
    let a ← j.getArr?
    if a.isEmpty then throw "Missing universe constructor"
    let tag ← a[0]!.getStr?
    match tag, a.size with
    | "zero", 1 => return .zero
    | "succ", 2 => return .succ (← decodeLevel a[1]! fuel)
    | "max", 3 => return .max (← decodeLevel a[1]! fuel) (← decodeLevel a[2]! fuel)
    | "imax", 3 => return .imax (← decodeLevel a[1]! fuel) (← decodeLevel a[2]! fuel)
    | "param", 2 => return .param (← decodeName a[1]!)
    | _, _ => throw "Unknown or unresolved universe constructor"
termination_by structural fuel

def decodeBinder (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "explicit" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instance" => return .instImplicit
  | _ => throw "Unknown binder mode"

partial def decodeExpr (slots : Array (Nat × Expr)) (j : Json)
    (fuel : Nat := 96) (depth : Nat := 0) : StateT Nat (Except String) Expr := do
  let budget ← get
  if fuel == 0 || budget == 0 then throw "Semantic IR exceeds decoding limit"
  set (budget - 1)
  let a ← j.getArr?
  if a.isEmpty then throw "Missing expression constructor"
  let tag ← a[0]!.getStr?
  let child (i : Nat) (d : Nat := depth) := decodeExpr slots a[i]! (fuel - 1) d
  match tag, a.size with
  | "bound", 2 =>
    let i ← a[1]!.getNat?
    unless i < depth do throw "Loose bound variable in IR"
    return .bvar i
  | "local", 2 =>
    let i ← a[1]!.getNat?
    for (k, v) in slots do
      if k == i then return v
    throw "Unknown local slot in IR"
  | "sort", 2 => return .sort (← decodeLevel a[1]!)
  | "const", 3 =>
    let us ← a[2]!.getArr?
    let levels ← us.toList.mapM fun u => decodeLevel u
    return .const (← decodeName a[1]!) levels
  | "app", 3 => return .app (← child 1) (← child 2)
  | "lambda", 5 =>
    return .lam (← decodeName a[1]!) (← child 3) (← child 4 (depth + 1)) (← decodeBinder a[2]!)
  | "pi", 5 =>
    return .forallE (← decodeName a[1]!) (← child 3) (← child 4 (depth + 1)) (← decodeBinder a[2]!)
  | "let", 6 =>
    return .letE (← decodeName a[1]!) (← child 2) (← child 3) (← child 4 (depth + 1)) (← a[5]!.getBool?)
  | "nat", 2 => return .lit (.natVal (← parseDecimal a[1]!))
  | "string", 2 => return .lit (.strVal (← a[1]!.getStr?))
  | "projection", 4 => return .proj (← decodeName a[1]!) (← a[2]!.getNat?) (← child 3)
  | _, _ => throw "Unknown or malformed expression constructor"

def decodeChecked (slots : Array (Nat × Expr)) (j : Json) : MetaM Expr := do
  let (e, _) ← match (decodeExpr slots j).run 12000 with
    | .ok r => pure r
    | .error err => throwError "Semantic IR decode: {err}"
  Lean.Meta.check e
  return e

/-- Verify the actual exported syntax, not merely equality of propositions.
    Re-encoding checks all preserved fields (including names and let flags);
    shape equality independently checks the original term modulo metadata. -/
def roundTripExpr (slots : Array (Nat × Expr)) (original : Expr) (j : Json) :
    StateT Nat MetaM Expr := do
  let decoded ← decodeChecked slots j
  unless sameShape original decoded do throwError "IR round trip changed expression shape"
  let encoded ← checkedEncode decoded
  unless encoded == j do throwError "IR round trip changed encoded fields"
  return decoded


def jsonField (j : Json) (key : String) : MetaM Json :=
  match j.getObjVal? key with
  | .ok v => pure v
  | .error err => throwError "Invalid IR context field: {err}"

def fromDecoded {α : Type} (r : Except String α) : MetaM α :=
  match r with
  | .ok v => pure v
  | .error err => throwError "IR context decode: {err}"

/-- Rebuild the local telescope with fresh free variables. The original slot
    numbers identify declarations only within the serialized judgment. -/
partial def withDecodedContext {α : Type} (entries : List Json)
    (slots : Array (Nat × Expr)) (k : Array (Nat × Expr) → MetaM α) : MetaM α := do
  match entries with
  | [] => k slots
  | entry :: rest =>
    let slot ← fromDecoded (← jsonField entry "slot").getNat?
    if let some (previous, _) := slots.back? then
      unless previous < slot do throwError "IR context slots are not strictly increasing"
    let name ← fromDecoded (decodeName (← jsonField entry "name"))
    let binder ← fromDecoded (decodeBinder (← jsonField entry "binder"))
    let ty ← decodeChecked slots (← jsonField entry "type")
    unless (← whnf (← inferType ty)).isSort do
      throwError "IR declaration is not a type"
    let value ← jsonField entry "value"
    let next (x : Expr) := withDecodedContext rest (slots.push (slot, x)) k
    match value with
    | .null => withLocalDecl name binder ty next
    | _ =>
      let v ← decodeChecked slots value
      unless ← isDefEq (← inferType v) ty do
        throwError "IR let value has the wrong type"
      withLetDecl name ty v next

/-- Check the reconstructed judgment in an empty initial local context.
    Compare both term and type after abstracting old/new variable identities.
    The global environment and universe parameter names remain the same. -/
def checkFreshContext (context : Array Json) (oldSlots : Array (Nat × Expr))
    (original originalType : Expr) (termIR typeIR : Json) : MetaM Unit :=
  withLCtx {} #[] do
    withDecodedContext context.toList #[] fun slots => do
      let term ← decodeChecked slots termIR
      let ty ← decodeChecked slots typeIR
      unless ← isDefEq (← inferType term) ty do
        throwError "Fresh-context judgment has the wrong type"
      let oldVars := oldSlots.map Prod.snd
      let newVars := slots.map Prod.snd
      unless sameShape (original.abstract oldVars) (term.abstract newVars) &&
          sameShape (originalType.abstract oldVars) (ty.abstract newVars) do
        throwError "Fresh-context round trip changed variable binding structure"

def encodeJudgment (e ty : Expr) (proposed : Option Expr) : StateT Nat MetaM Json := do
  let mut context : Array Json := #[]
  let mut slots : Array (Nat × Expr) := #[]
  for d in (← getLCtx) do
    if context.size >= 128 then throwError "IR context exceeds 128 declarations"
    let encodedType ← checkedEncode d.type
    let _ ← roundTripExpr slots d.type encodedType
    let value ← match d.value? with
      | some v => do
        let j ← checkedEncode v
        let _ ← roundTripExpr slots v j
        pure j
      | none => pure Json.null
    context := context.push (Json.mkObj [
      ("slot", toJson d.index), ("name", encodeName d.userName), ("display", toJson d.userName.toString),
      ("binder", toJson (binderTag d.binderInfo)), ("internal", toJson d.isImplementationDetail),
      ("type", encodedType), ("value", value)])
    slots := slots.push (d.index, mkFVar d.fvarId)
  let formula ← match proposed with
    | none => pure Json.null
    | some p => do
      let equal ← isDefEq p ty
      let j ← checkedEncode p
      let _ ← roundTripExpr slots p j
      pure (Json.mkObj [("term", j),
        ("display", toJson (← ppExpr p).pretty), ("matchesGoal", toJson equal)])
  let proof ← isProp ty
  let proposition ← isProp e
  let kind := if proof then "proof" else if proposition then "proposition" else "expression"
  let termIR ← checkedEncode e
  let typeIR ← checkedEncode ty
  let decoded ← roundTripExpr slots e termIR
  let decodedType ← roundTripExpr slots ty typeIR
  unless ← isDefEq (← inferType decoded) decodedType do
    throwError "Decoded judgment is not well typed"
  checkFreshContext context slots e ty termIR typeIR
  return Json.mkObj [("context", Json.arr context), ("term", termIR),
    ("type", typeIR), ("kind", toJson kind), ("formula", formula),
    ("roundTrip", Json.mkObj [("checked", toJson true), ("shapePreserved", toJson true),
      ("encodingPreserved", toJson true), ("typeDefEq", toJson true),
      ("freshContextChecked", toJson true),
      ("mode", toJson "same-environment-fresh-context")]),
    ("termDisplay", toJson (← ppExpr e).pretty), ("typeDisplay", toJson (← ppExpr ty).pretty)]

def elaborateProposition (input : String) : TermElabM Expr := do
  let stx ← match Parser.runParserCategory (← getEnv) `term input with
    | .ok stx => pure stx
    | .error err => throwError "{err}"
  let p ← Term.elabTermEnsuringType stx (some (mkSort Level.zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then throwError "Formula contains unresolved type information"
  Lean.Meta.check p
  return p

elab "#duet_ir " n:ident path:str formula:str : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      let result ← withNodeAt v.value (parts.drop 1) fun e => do
        let ty ← inferType e
        let proposed ← if formula.getString.isEmpty then pure none
          else some <$> elaborateProposition formula.getString
        let (judgment, _) ← (encodeJudgment e ty proposed).run 12000
        pure (Json.mkObj [("schema", toJson (1 : Nat)), ("format", toJson "leanduet.kernel-judgment"),
          ("declaration", encodeName n.getId), ("path", toJson path.getString),
          ("universes", Json.arr (v.levelParams.toArray.map encodeName)), ("judgment", judgment)])
      logInfo m!"LEANDUET_JSON:{result.compress}"
    | _ => throwError "Expected a theorem"


/-- Close a selected proof over its dependency-closed telescope. Local
    definitions remain lets, not unconstrained parameters. This is an
    abstraction of an existing proof, not discovery of a stronger theorem. -/
def abstractProof (e : Expr) : MetaM (Expr × Expr × Array LocalDecl) := do
  let goal ← inferType e
  unless ← isProp goal do throwError "Abstraction requires a proof of a proposition"
  let (locals, needed) ← referencedContext goal e
  let deps := locals.filter (fun d => needed.contains d.fvarId)
  if deps.size > 128 then throwError "Abstraction context exceeds 128 declarations"
  let mut term := e
  let mut statement := goal
  for d in deps.reverse do
    let x := mkFVar d.fvarId
    let body := term.abstract #[x]
    let target := statement.abstract #[x]
    match d.value? with
    | some v =>
      term := .letE d.userName d.type v body false
      statement := .letE d.userName d.type v target false
    | none =>
      term := .lam d.userName d.type body d.binderInfo
      statement := .forallE d.userName d.type target d.binderInfo
  if term.hasFVar || statement.hasFVar || term.hasLooseBVars || statement.hasLooseBVars ||
      term.hasMVar || statement.hasMVar || term.hasLevelMVar || statement.hasLevelMVar then
    throwError "Abstraction did not produce a closed judgment"
  withLCtx {} #[] do
    Lean.Meta.check statement
    Lean.Meta.check term
    unless ← isProp statement do throwError "Abstracted statement is not a proposition"
    unless ← isDefEq (← inferType term) statement do
      throwError "Abstracted proof has the wrong type"
  -- Reopen the exact binders (including let-bound identities). This is an
  -- occurrence-level check, stronger than comparing proof types alone.
  let mut opened := term
  let mut openedType := statement
  for d in deps do
    let x := mkFVar d.fvarId
    match opened, openedType, d.value? with
    | .lam _ _ b _, .forallE _ _ q _, none =>
      opened := b.instantiate1 x
      openedType := q.instantiate1 x
    | .letE _ _ _ b _, .letE _ _ _ q _, some _ =>
      opened := b.instantiate1 x
      openedType := q.instantiate1 x
    | _, _, _ => throwError "Abstraction telescope does not reopen"
  unless sameShape opened e && sameShape openedType goal do
    throwError "Abstraction changed the selected proof occurrence"
  return (term, statement, deps)

elab "#duet_abstract " n:ident path:str : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      let result ← withNodeAt v.value (parts.drop 1) fun e => do
        let (term, statement, deps) ← abstractProof e
        if mentions term n.getId || mentions statement n.getId || mentions term `sorryAx then
          throwError "Abstraction relies on the original theorem or an incomplete proof"
        let typeText ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true |>.setBool `pp.piBinderTypes true |>.setBool `pp.explicit true |>.setBool `pp.notation false |>.setBool `pp.universes true |>.setBool `pp.coercions true |>.setBool `pp.proofs true |>.setBool `pp.numericTypes true) do
          pure (← ppExpr statement).pretty
        let termText ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true |>.setBool `pp.piBinderTypes true |>.setBool `pp.explicit true |>.setBool `pp.notation false |>.setBool `pp.universes true |>.setBool `pp.coercions true |>.setBool `pp.proofs true |>.setBool `pp.numericTypes true) do
          pure (← ppExpr term).pretty
        let ctx := deps.map fun d => Json.mkObj [("slot", toJson d.index),
          ("name", toJson d.userName.toString), ("isLet", toJson d.value?.isSome),
          ("internal", toJson d.isImplementationDetail)]
        return Json.mkObj [("schema", toJson (1 : Nat)), ("type", toJson typeText),
          ("term", toJson termText), ("parameters", Json.arr ctx),
          ("universes", toJson (v.levelParams.map Name.toString)),
          ("closedChecked", toJson true), ("reopenedShape", toJson true)]
      logInfo m!"LEANDUET_JSON:{result.compress}"
    | _ => throwError "Expected a theorem"

elab "#duet_compare_abstraction " n:ident m:ident path:str : command => do
  liftTermElabM do
    match ← getConstInfo n.getId, ← getConstInfo m.getId with
    | .thmInfo v, .thmInfo candidate =>
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      withNodeAt v.value (parts.drop 1) fun e => do
        let (term, statement, _) ← abstractProof e
        unless ← isDefEq candidate.type statement do throwError "Abstracted theorem type changed on export"
        unless sameShape term candidate.value do
          throwError "Abstracted theorem proof changed on export\nExpected: {repr (shape term)}\nActual: {repr (shape candidate.value)}"
        logInfo "LEANDUET_ABSTRACTION_MATCH"
    | _, _ => throwError "Expected two theorems"


/-- Rebuild a single path using an Expr produced in that exact scope.
    Unlike textual replacement, this never resolves arguments by names. -/
partial def replaceExprAt (e : Expr) (path : List String)
    (k : Expr → MetaM Expr) : MetaM Expr := do
  match path with
  | [] =>
    let new ← k e
    Lean.Meta.check new
    unless ← isDefEq (← inferType e) (← inferType new) do
      throwError "Refactoring changed the local type"
    return new
  | p :: rest =>
    match e with
    | .mdata md b => return .mdata md (← replaceExprAt b path k)
    | .lam n t b bi =>
      unless p == "body" do throwError "Invalid lambda path"
      withLocalDecl n bi t fun x => do
        let b' ← replaceExprAt (b.instantiate1 x) rest k
        return .lam n t (b'.abstract #[x]) bi
    | .letE n t v b nd =>
      if p == "value" then
        return .letE n t (← replaceExprAt v rest k) b nd
      else if p == "body" then
        withLetDecl n t v fun x => do
          let b' ← replaceExprAt (b.instantiate1 x) rest k
          return .letE n t v (b'.abstract #[x]) nd
      else throwError "Invalid let path"
    | .app .. =>
      unless p.startsWith "arg" do throwError "Invalid application path"
      let some i := (String.mk (p.toList.drop 3)).toNat? | throwError "Invalid argument index"
      let args := e.getAppArgs
      unless i < args.size do throwError "Argument index out of bounds"
      let v ← replaceExprAt args[i]! rest k
      return mkAppN e.getAppFn (args.set! i v)
    | _ => throwError "Invalid expression path"

/-- Build the exact lemma call using local-variable identities. Check its
    actual definition against the abstraction; theorem proof irrelevance
    is insufficient for this purpose. -/
def factorProof (original : Expr) (path : List String) (lemmaName : Name) :
    MetaM Expr := do
  let ci ← getConstInfo lemmaName
  let .thmInfo auxiliary := ci | throwError "Expected an extracted theorem"
  unless auxiliary.levelParams.isEmpty do throwError "Polymorphic factoring is not supported yet"
  replaceExprAt original path fun e => do
    let (t, statement, deps) ← abstractProof e
    unless ← isDefEq auxiliary.type statement do throwError "Extracted lemma statement mismatch"
    unless sameShape t auxiliary.value do throwError "Extracted lemma proof mismatch"
    -- A local definition is preserved as a let in the extracted theorem,
    -- so it is not an argument to the lemma.
    let args := (deps.filter (fun d => d.value?.isNone)).map (fun d => mkFVar d.fvarId)
    let call := mkAppN (mkConst lemmaName) args
    Lean.Meta.check call
    unless ← isDefEq (← inferType call) (← inferType e) do
      throwError "Extracted lemma application has the wrong dependent type"
    return call

elab "#duet_factor " n:ident auxiliary:ident path:str : command => do
  liftTermElabM do
    let .thmInfo v ← getConstInfo n.getId | throwError "Expected a theorem"
    unless v.levelParams.isEmpty do throwError "Polymorphic factoring is not supported yet"
    let parts := path.getString.splitOn "/"
    unless parts.head? == some "root" do throwError "Invalid root path"
    let proof ← factorProof v.value (parts.drop 1) auxiliary.getId
    Lean.Meta.check proof
    unless ← isDefEq (← inferType proof) v.type do throwError "Factored proof changes theorem type"
    if mentions proof n.getId || mentions proof `sorryAx then throwError "Invalid factored proof"
    let typeText ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true |>.setBool `pp.piBinderTypes true |>.setBool `pp.explicit true |>.setBool `pp.notation false |>.setBool `pp.universes true |>.setBool `pp.coercions true |>.setBool `pp.proofs true |>.setBool `pp.numericTypes true) do
      pure (← ppExpr v.type).pretty
    let termText ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true |>.setBool `pp.piBinderTypes true |>.setBool `pp.explicit true |>.setBool `pp.notation false |>.setBool `pp.universes true |>.setBool `pp.coercions true |>.setBool `pp.proofs true |>.setBool `pp.numericTypes true) do
      pure (← ppExpr proof).pretty
    logInfo m!"LEANDUET_JSON:{(Json.mkObj [("type", toJson typeText), ("term", toJson termText)]).compress}"

elab "#duet_compare_factor " n:ident m:ident auxiliary:ident path:str : command => do
  liftTermElabM do
    match ← getConstInfo n.getId, ← getConstInfo m.getId with
    | .thmInfo v, .thmInfo candidate =>
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      let expected ← factorProof v.value (parts.drop 1) auxiliary.getId
      unless ← isDefEq v.type candidate.type do throwError "Factored export changed the statement"
      unless sameShape expected candidate.value do
        throwError "Factored export changed the proof complement or call\nExpected: {repr (shape expected)}\nActual: {repr (shape candidate.value)}"
      logInfo "LEANDUET_FACTOR_MATCH"
    | _, _ => throwError "Expected two theorems"

def finishCandidate (goal : Expr) (expected : Expr) (forbidden : Name)
    (label : String) (required : List FVarId) : MetaM (Option Json) := do
  let p ← instantiateMVars goal
  if p.hasMVar || p.hasLevelMVar || mentions p forbidden || mentions p `sorryAx then
    return none
  unless required.all (fun id => p.containsFVar id) do return none
  Lean.Meta.check p
  unless ← isDefEq (← inferType p) expected do return none
  let term ← withOptions (fun o => o.setBool `pp.fullNames true) do
    pure (← ppExpr p).pretty
  return some (Json.mkObj [("rule", toJson label), ("term", toJson term),
    ("type", toJson (← ppExpr expected).pretty)])

/-- Each attempt starts with a fresh metavariable and rolls back all assignments.
    The imported declaration index is Lean's own, including Mathlib when imported. -/
def findProofs (goalType : Expr) (forbidden : Name) (only : String) (required : List FVarId) : MetaM (Array Json) := do
  let saved ← getMCtx
  let mut results : Array Json := #[]
  if only.isEmpty then
    let localResult ← observing? do
      let goal ← mkFreshExprMVar goalType
      let remaining ← LibrarySearch.solveByElim (required.map mkFVar) false [goal.mvarId!] 4
      unless remaining.isEmpty do throwError "Unsolved premises"
      finishCandidate goal goalType forbidden "local elimination" required
    setMCtx saved
    if let some (some j) := localResult then results := results.push j
  let candidates ← if only.isEmpty then
    LibrarySearch.libSearchFindDecls goalType
  else
    let n := only.toName
    if (← getEnv).contains n then
      pure #[(n, LibrarySearch.DeclMod.none), (n, .mp), (n, .mpr)]
    else pure #[]
  let mut attempts := 0
  for (n, direction) in candidates do
    if results.size >= 6 || attempts >= 48 then break
    if !forbidden.isPrefixOf n && n != `sorryAx then
      attempts := attempts + 1
      let found ← observing? do
        let goal ← mkFreshExprMVar goalType
        let rule ← LibrarySearch.mkLibrarySearchLemma n direction
        let pending ← goal.mvarId!.apply rule
        let partialProof ← instantiateMVars goal
        let missing := required.filter (fun id => !partialProof.containsFVar id)
        let remaining ← LibrarySearch.solveByElim (missing.map mkFVar) false pending 4
        unless remaining.isEmpty do throwError "Unsolved premises"
        let label := n.toString ++ (match direction with
          | .none => ""
          | .mp => " (forward)"
          | .mpr => " (backward)")
        finishCandidate goal goalType forbidden label required
      setMCtx saved
      if let some (some j) := found then
        unless results.contains j do results := results.push j
  return results

def resolveRequired (names : String) : MetaM (List FVarId) := do
  if names.isEmpty then return []
  let mut resolved := []
  for name in names.splitOn "," do
    let mut ids : Array FVarId := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && d.userName.toString == name then
        ids := ids.push d.fvarId
    unless ids.size == 1 do throwError "Unknown or ambiguous local premise: {name}"
    resolved := ids[0]! :: resolved
  return resolved.reverse

elab "#duet_search " n:ident path:str rule:str required:str formula:str : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      let j ← withNodeAt v.value (parts.drop 1) fun e => do
        let goal ← inferType e
        unless ← isProp goal do throwError "Search requires a proposition"
        if !formula.getString.isEmpty then
          let proposed ← elaborateProposition formula.getString
          unless ← isDefEq proposed goal do
            throwError "Formula does not match the selected proposition"
        let premises ← resolveRequired required.getString
        let candidates ← findProofs goal n.getId rule.getString premises
        pure (Json.mkObj [("schema", toJson (1 : Nat)),
          ("goal", toJson (← ppExpr goal).pretty), ("candidates", Json.arr candidates)])
      logInfo m!"LEANDUET_JSON:{j.compress}"
    | _ => throwError "Expected a theorem"


/-- Test several interpretations in the same selected scope, restoring the
    elaboration state between alternatives. Acceptance is local only. -/
elab "#duet_interpret " n:ident path:str payload:str : command => do
  liftTermElabM do
    let .thmInfo v ← getConstInfo n.getId | throwError "Expected a theorem"
    let parts := path.getString.splitOn "/"
    unless parts.head? == some "root" do throwError "Invalid root path"
    let rows ← fromDecoded ((← fromDecoded (Json.parse payload.getString)).getArr?)
    unless rows.size > 0 && rows.size ≤ 8 do throwError "Expected 1–8 interpretations"
    let result ← withNodeAt v.value (parts.drop 1) fun e => do
      let goal ← inferType e
      unless ← isProp goal do throwError "Interpretation requires a proof goal"
      let mut output : Array Json := #[]
      for i in [:rows.size] do
        let row := rows[i]!
        let formula ← fromDecoded (← jsonField row "formula").getStr?
        let rule ← fromDecoded (← jsonField row "rule").getStr?
        let required ← fromDecoded (← jsonField row "required").getStr?
        let term ← fromDecoded (← jsonField row "term").getStr?
        let saved ← Term.saveState
        let attempt ← observing? do
          if !formula.isEmpty then
            let p ← elaborateProposition formula
            unless ← isDefEq p goal do throwError "Formula does not match goal"
          let premises ← resolveRequired required
          if term.isEmpty then
            findProofs goal n.getId rule premises
          else
            let stx ← fromDecoded (Parser.runParserCategory (← getEnv) `term term)
            let p ← Term.elabTermEnsuringType stx (some goal)
            Term.synthesizeSyntheticMVarsNoPostponing
            let p ← instantiateMVars p
            if p.hasMVar || p.hasLevelMVar || mentions p n.getId || mentions p `sorryAx then
              throwError "Unresolved or invalid proof"
            unless premises.all (fun id => p.containsFVar id) do
              throwError "Required premise not used"
            Lean.Meta.check p
            unless ← isDefEq (← inferType p) goal do throwError "Wrong local type"
            return #[Json.mkObj [("rule",toJson "explicit term"),("term",toJson term),
              ("type",toJson (← ppExpr goal).pretty)]]
        saved.restore true
        let candidates := attempt.getD #[]
        let status := if attempt.isNone then "rejected" else if candidates.isEmpty then "not-found" else "locally-checked"
        output := output.push (Json.mkObj [("index",toJson i),("status",toJson status),("candidates",Json.arr candidates)])
      return Json.mkObj [("goal",toJson (← ppExpr goal).pretty),("interpretations",Json.arr output)]
    logInfo m!"LEANDUET_JSON:{result.compress}"

end LeanDuetExtract
