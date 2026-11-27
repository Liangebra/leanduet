import test from 'node:test';
import assert from 'node:assert/strict';
import {compileFormula,sameScopedFormula} from '../web/math-formula.mjs';
test('math expression grammar preserves precedence and binder structure',()=>{
 assert.equal(compileFormula(String.raw`$b = a$`).lean,'(b = a)');
 assert.equal(compileFormula(String.raw`P \land Q \to R`).lean,'((P ∧ Q) → R)');
 assert.equal(compileFormula(String.raw`\forall n : \mathbb{N}, P(n)`).lean,'(∀ n : Nat, (P n))');
 assert.equal(compileFormula(String.raw`\frac{a+b}{c} = d`).lean,'(((a + b) / c) = d)');
 assert.equal(compileFormula('f(g(x), y) = z').lean,'((f (g x) y) = z)');
});
test('unsupported, ambiguous and malformed formulas fail rather than guess',()=>{
 for(const t of ['2x','a < b < c',String.raw`\unknown{x}`,'a = (b','by exact h','a; b','x_{i}'])assert.throws(()=>compileFormula(t),undefined,t);
});

test('canonical scoped view is invariant under alpha-renaming but not capture',()=>{
 const a=compileFormula(String.raw`\forall x : \mathbb{N}, P(x)`).scoped;
 const b=compileFormula(String.raw`\forall y : \mathbb{N}, P(y)`).scoped;
 const c=compileFormula(String.raw`\forall y : \mathbb{N}, P(x)`).scoped;
 assert.deepEqual(a,b);assert.notDeepEqual(a,c);
 const nested=compileFormula(String.raw`\forall x : \mathbb{N}, \exists y : \mathbb{N}, x = y`).scoped;
 assert.equal(nested.body.body.left.index,1);assert.equal(nested.body.body.right.index,0);
});

test('the built-in Lean negation spelling has one scoped form',()=>{
 assert.equal(sameScopedFormula('Not P','¬ P'),true);
 assert.equal(sameScopedFormula('Not (P ∧ Q)','¬ (P ∧ Q)'),true);
 assert.equal(sameScopedFormula('P','False'),false);
});

test('Lean quantifier groups become nested binders with stable object references',()=>{
 const text='∀ (A : List Nat) (P : Nat → Prop), ∀ (x : Nat), x ∈ A → P x';
 const target=compileFormula(text,{syntax:'lean'});
 assert.equal(target.scoped.kind,'binder');
 assert.equal(target.scoped.body.kind,'binder');
 assert.equal(target.scoped.body.body.kind,'binder');
 const body=target.scoped.body.body.body;
 assert.equal(body.left.left.index,0,'x refers to the innermost binder');
 assert.equal(body.left.right.index,2,'A refers across x and P to the outer binder');
 assert.equal(body.right.fn.index,1,'P keeps a distinct binder identity from A and x');
 assert.deepEqual(compileFormula(target.lean,{syntax:'lean'}).scoped,target.scoped);
 assert.throws(()=>compileFormula(text),/(Expected|Unsupported)/,'presentation syntax does not accept Lean binder groups');
 const groupedNames=compileFormula('∀ (x y : Nat), R x y',{syntax:'lean'});
 assert.equal(groupedNames.scoped.body.kind,'binder');
 assert.equal(groupedNames.scoped.body.body.args[0].index,1);
 assert.equal(groupedNames.scoped.body.body.args[1].index,0);
 assert.throws(()=>compileFormula('∀ (x y : x), R x y',{syntax:'lean'}),/capture/);
 const untyped=compileFormula('∀ x y, R x y',{syntax:'lean'});
 assert.equal(untyped.scoped.body.body.args[0].index,1);
 assert.equal(untyped.scoped.body.body.args[1].index,0);
});
test('Lean targets accept Prop and Type as binder sorts without widening math input',()=>{
 const target=compileFormula('∀ (P : Nat → Prop), ∀ (x : Nat), P x',{syntax:'lean'});
 assert.equal(target.lean,'(∀ P : (Nat → Prop), (∀ x : Nat, (P x)))');
 assert.equal(target.scoped.domain.left.name,'Nat');
 assert.equal(target.scoped.domain.right.name,'Prop');
 assert.throws(()=>compileFormula('∀ (P : Nat → Prop), ∀ (x : Nat), P x'));
 assert.equal(compileFormula('∀ (α : Type), α → α',{syntax:'lean'}).lean,'(∀ α : Type, (α → α))');
});

test('bounded quantifiers preserve membership and reject capture',()=>{
 assert.equal(compileFormula('\\forall x \\in S, P(x)').lean,'(∀ x, (x ∈ S) → (P x))');
 assert.equal(compileFormula('\\exists x \\in S, P(x)').lean,'(∃ x, (x ∈ S) ∧ (P x))');
 assert.throws(()=>compileFormula('∀ x ∈ f(x), P(x)'));
});

test('set intersection and union bind inside membership and subset relations',()=>{
 const intersection=compileFormula(String.raw`x \in A \cap B`);
 assert.equal(intersection.lean,'(x ∈ (A ∩ B))');
 assert.deepEqual(intersection.scoped,{kind:'binary',op:'∈',left:{kind:'free',name:'x'},right:{kind:'binary',op:'∩',left:{kind:'free',name:'A'},right:{kind:'free',name:'B'}}});
 assert.equal(compileFormula(String.raw`A \cap B \subseteq C`).lean,'((A ∩ B) ⊆ C)');
 assert.equal(compileFormula(String.raw`A \cup B \cap C`).lean,'(A ∪ (B ∩ C))');
 assert.equal(compileFormula(String.raw`a + b \cap c`).lean,'(a + (b ∩ c))');
 assert.equal(compileFormula(String.raw`A \cup B + C`).lean,'((A ∪ B) + C)','equal-precedence Lean operators associate to the left');
 assert.equal(compileFormula(String.raw`a + b * c`).lean,'(a + (b * c))');
 for(const input of [String.raw`x \in A \cap B`,String.raw`A \cup B \subseteq C`])
  assert.deepEqual(compileFormula(compileFormula(input).lean,{syntax:'lean'}).scoped,compileFormula(input).scoped,input);
});

test('set image uses Lean precedence and retains its operation in the scoped tree',()=>{
 const image=compileFormula("f '' s");
 assert.equal(image.lean,"(f '' s)");
 assert.deepEqual(image.scoped,{kind:'binary',op:"''",left:{kind:'free',name:'f'},right:{kind:'free',name:'s'}});
 assert.equal(compileFormula("f '' s ∩ t").lean,"((f '' s) ∩ t)");
 assert.equal(compileFormula("f '' (s ∩ t)").lean,"(f '' (s ∩ t))");
 assert.equal(compileFormula("f' '' s").lean,"(f' '' s)",'prime-suffixed identifiers remain separate from the image token');
 assert.deepEqual(compileFormula(image.lean,{syntax:'lean'}).scoped,image.scoped);
});

test('Lean presentation round trips preserve application and binder structure',()=>{
 for(const input of ['P(x)','f(g(x), y)=z','f(x)(y)','∀ x : Nat, P(x)','∀ x ∈ S, P(x)','∃ x ∈ S, P(x)','∀ S : Set, ∀ x ∈ S, P(x)']){
  const math=compileFormula(input);
  assert.deepEqual(compileFormula(math.lean,{syntax:'lean'}).scoped,math.scoped,input);
 }
 assert.throws(()=>compileFormula('P x'));
 assert.throws(()=>compileFormula('f (x,y)',{syntax:'lean'}));
});
