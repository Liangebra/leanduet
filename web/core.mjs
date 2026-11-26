const rules = [["intro","Introduce"],["exact","Conclude using"],["apply","Apply"],["rw","Rewrite using"],["simp","Simplify using"],["have","Establish"],["show","Show"],["refine","Refine using"],["change","Change goal to"],["constructor","Construct using"],["cases","Split cases of"],["induction","Induct on"]];
const atoms = [["rfl","By reflexivity."],["assumption","By assumption."],["simp","Simplify."],["constructor","Apply a constructor."],["trivial","By triviality."]];
function classify(s){
  const atom=atoms.find(([k])=>k===s);
  if(atom)return {kind:atom[0],label:atom[1],argument:null};
  const r=rules.find(([k])=>s.startsWith(k+" "));
  if(r)return {kind:r[0],label:r[1],argument:s.slice(r[0].length+1)};
  return {kind:"opaque",label:"Lean step",argument:s};
}

function parseLean(source){
  if(typeof source!=="string"||source.includes("\r"))throw Error("Use LF line endings.");
  const lines=source.split("\n"); if(lines.at(-1)==="")lines.pop();
  let i=0;const prelude=[];
  while(i<lines.length&&(/^(import\s+\S.*)$/.test(lines[i])||lines[i]===""))prelude.push(lines[i++]);
  const header=lines[i++];
  if(!header||!/^(theorem|lemma)\s+\S.*:= by$/.test(header))throw Error("Expected one single-line theorem or lemma ending in := by.");
  const nodes=[];const stack=[];
  for(;i<lines.length;i++){
    const line=lines[i];
    if(line===""){nodes.push({id:`line-${i+1}`,kind:"blank",indent:0,lean:"",leanLine:i+1,parent:null});continue;}
    const m=/^( +)(\S.*)$/.exec(line);
    if(!m||m[1].length<2||m[1].length>256||line.includes("\t"))throw Error(`Line ${i+1}: expected a space-indented proof line; multiple declarations are unsupported.`);
    if(/\/-|-\//.test(m[2]))throw Error(`Line ${i+1}: block comments are not supported.`);
    const indent=m[1].length;
    while(stack.length&&stack.at(-1).indent>=indent)stack.pop();
    const n={id:`line-${i+1}`,indent,lean:m[2],leanLine:i+1,parent:stack.at(-1)?.id??null,...classify(m[2])};
    nodes.push(n);stack.push(n);
  }
  if(!nodes.some(n=>n.kind!=="blank"))throw Error("The proof is empty.");
  return {version:2,prelude,header,nodes,finalNewline:source.endsWith("\n")};
}

function renderLean(ir){
  return [...ir.prelude,ir.header,...ir.nodes.map(n=>n.kind==="blank"?"":" ".repeat(n.indent)+n.lean)].join("\n")+(ir.finalNewline?"\n":"");
}

function renderProse(ir){
  return ["Environment "+JSON.stringify(ir.prelude),"Theorem "+JSON.stringify(ir.header),
    ...ir.nodes.map(n=>n.kind==="blank"?"Blank":`${n.indent} | ${n.label}${n.argument===null?"":" "+JSON.stringify(n.argument)}`),
    "Final newline "+String(ir.finalNewline)].join("\n");
}

function parseProse(text){
  const lines=text.split("\n");if(lines.at(-1)==="")lines.pop();
  const extract=(line,prefix)=>{if(!line?.startsWith(prefix))throw Error("Expected "+prefix);return JSON.parse(line.slice(prefix.length));};
  const prelude=extract(lines.shift(),"Environment "),header=extract(lines.shift(),"Theorem ");
  if(!Array.isArray(prelude)||prelude.some(s=>typeof s!=="string"||s.includes("\n")||!(/^(import\s+\S.*)$/.test(s)||s===""))||typeof header!=="string"||header.includes("\n"))throw Error("Invalid environment or theorem header.");
  const finalNewline=extract(lines.pop(),"Final newline ");if(typeof finalNewline!=="boolean")throw Error("Invalid newline flag.");
  const body=lines.map((line,i)=>{
    if(line==="Blank")return "";
    const m=/^([0-9]+) \| (.+)$/.exec(line);
    if(!m||+m[1]<2||+m[1]>256)throw Error(`Prose line ${i+3}: invalid indentation.`);
    const expr=m[2];const atom=atoms.find(([,label])=>label===expr);
    let lean;
    if(atom)lean=atom[0];
    else{
      const rule=rules.find(([,label])=>expr.startsWith(label+" "));
      const label=rule?.[1]??"Lean step";
      if(!expr.startsWith(label+" "))throw Error(`Prose line ${i+3}: unsupported sentence.`);
      const arg=JSON.parse(expr.slice(label.length+1));
      if(typeof arg!=="string"||!arg||/[\r\n]/.test(arg))throw Error("Expected one Lean fragment.");
      lean=rule?rule[0]+" "+arg:arg;
    }
    return " ".repeat(+m[1])+lean;
  });
  return parseLean([...prelude,header,...body].join("\n")+(finalNewline?"\n":""));
}

function sameStatement(a,b){return a.header===b.header&&JSON.stringify(a.prelude)===JSON.stringify(b.prelude);}

function planSync(base,lean,prose,side){
  if(!["lean","prose"].includes(side))throw Error("Unknown sync direction.");
  if(lean!==base.lean&&prose!==base.prose)throw Error("Both sides changed. Save or explicitly revert one side before synchronizing.");
  const ir=side==="lean"?parseLean(lean):parseProse(prose);
  if(!sameStatement(parseLean(base.lean),ir))throw Error("Statement or imports changed. Start a new document explicitly.");
  return {ir,lean:renderLean(ir),prose:renderProse(ir)};
}
const EXAMPLES = [
  {
    "name": "Implication composition",
    "source": "theorem compose_imp (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by\n  intro hp\n  have hq : Q := hpq hp\n  exact hqr hq\n"
  },
  {
    "name": "Conjunction symmetry",
    "source": "theorem swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by\n  constructor\n  · exact h.2\n  · exact h.1\n"
  },
  {
    "name": "Nested proof",
    "source": "theorem nested (P : Prop) (h : P) : P ∧ P := by\n  have h' : P := by\n    exact h\n  exact ⟨h', h⟩\n"
  },
  {
    "name": "Equality symmetry",
    "source": "theorem reverse_eq (a b : Nat) (h : a = b) : b = a := by\n  exact h.symm\n"
  }
];
export { parseLean, renderLean, renderProse, parseProse, sameStatement, planSync, EXAMPLES };
