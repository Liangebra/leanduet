import test from 'node:test';
import assert from 'node:assert/strict';
import {compileChain} from '../web/proof-chain.mjs';
const scope=['P','Q','R','f','g','p'];
test('ordered intermediate conclusions compile in the extended context',()=>{
  const r=compileChain('建立 hq : Q | f using p\n结论 | g using hq',scope);
  assert.equal(r.term,'by\n  have hq : Q := f p\n  exact g hq');
  assert.equal(r.steps.length,2);
});
test('reject forward references, duplicates, missing conclusion',()=>{
  assert.throws(()=>compileChain('Establish hq : Q | f using later\nConclude | g using hq',scope));
  assert.throws(()=>compileChain('Establish p : Q | f using p\nConclude | g using p',scope));
  assert.throws(()=>compileChain('Establish hq : Q | f using p',scope));
  assert.throws(()=>compileChain('Conclude | f using p\nConclude | g using p',scope));
});
test('ordered arguments and mathematical concepts are preserved',()=>{
  assert.equal(compileChain('Conclude | 等式传递性 using hab and hbc',['hab','hbc']).term,'by\n  exact Eq.trans hab hbc');
  assert.equal(compileChain('結論 | 等式の対称性 using h',['h']).term,'by\n  exact Eq.symm h');
});

test('positional applications may reuse a premise; search constraint sets may not',()=>{
  assert.equal(compileChain('Conclude | conjunction introduction using h and h',['h']).term,'by\n  exact And.intro h h');
});
test('Japanese rule phrases support natural evidence separator',()=>{
  assert.equal(compileChain('結論 | 等式の推移性を用いて hab、hbc',['hab','hbc']).term,'by\n  exact Eq.trans hab hbc');
});
test('forward local rules are rejected as well as forward arguments',()=>{
  assert.throws(()=>compileChain('Establish hq : Q | later using p\nEstablish later : P → Q | f\nConclude | g using hq',scope));
});

test('type annotations may be omitted, without dropping scope checks',()=>{
  const r=compileChain('建立 hq | f 使用 p\n结论 | g 使用 hq',scope);
  assert.equal(r.steps[0].type,null);
  assert.equal(r.term,'by\n  have hq := f p\n  exact g hq');
  assert.throws(()=>compileChain('Establish hq | later using p\nEstablish later | f\nConclude | g using hq',scope));
});

test('LaTeX annotation passes through the formula AST and retains rule scope',()=>{
 const r=compileChain('Establish hq : $Q$ | f using p\nConclude | g using hq',scope);
 assert.equal(r.steps[0].type,'Q');
 assert.equal(r.term,'by\n  have hq : Q := f p\n  exact g hq');
});

test('formula holes emit Lean proof search rather than sorry',()=>{
 const r=compileChain('Establish hq : $Q$ | ?\nConclude | ?',scope);
 assert.equal(r.term,'by\n  have hq : Q := by exact?\n  exact?');
 assert.throws(()=>compileChain('Establish hq | ?\nConclude | ?',scope));
});
