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

test('bounded quantifiers preserve membership and reject capture',()=>{
 assert.equal(compileFormula('\\forall x \\in S, P(x)').lean,'(∀ x, (x ∈ S) → (P x))');
 assert.equal(compileFormula('\\exists x \\in S, P(x)').lean,'(∃ x, (x ∈ S) ∧ (P x))');
 assert.throws(()=>compileFormula('∀ x ∈ f(x), P(x)'));
});

test('Lean presentation round trips preserve application and binder structure',()=>{
 for(const input of ['P(x)','f(g(x), y)=z','f(x)(y)','∀ x : Nat, P(x)','∀ x ∈ S, P(x)','∃ x ∈ S, P(x)','∀ S : Set, ∀ x ∈ S, P(x)']){
  const math=compileFormula(input);
  assert.deepEqual(compileFormula(math.lean,{syntax:'lean'}).scoped,math.scoped,input);
 }
 assert.throws(()=>compileFormula('P x'));
 assert.throws(()=>compileFormula('f (x,y)',{syntax:'lean'}));
});
