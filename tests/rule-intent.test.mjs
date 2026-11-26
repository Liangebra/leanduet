import test from 'node:test';
import assert from 'node:assert/strict';
import {resolveIntent,parseRuleIntent} from '../web/rule-intent.mjs';
test('bilingual mathematical aliases resolve to exact declaration identifiers',()=>{
  assert.equal(resolveIntent('由等式对称性。'),'Eq.symm');
  assert.equal(resolveIntent('by transitivity of equality'),'Eq.trans');
  assert.equal(resolveIntent('紧集的连续像'),'IsCompact.image');
  assert.equal(resolveIntent('Nat.add_comm'),'Nat.add_comm');
});
test('automatic mode is explicit and unsupported free language is rejected',()=>{
  assert.equal(resolveIntent(''),'');
  assert.equal(resolveIntent('自动检索'),'');
  assert.throws(()=>resolveIntent('then the conclusion follows obviously'));
});

test('controlled phrases retain required premise identities',()=>{
  assert.deepEqual(parseRuleIntent('由等式传递性，使用 hab、hbc。'),{rule:'Eq.trans',required:['hab','hbc']});
  assert.deepEqual(parseRuleIntent('by symmetry of equality, using h'),{rule:'Eq.symm',required:['h']});
  assert.deepEqual(parseRuleIntent('using h1 and h2'),{rule:'',required:['h1','h2']});
  assert.throws(()=>parseRuleIntent('using h and h'));
  assert.throws(()=>parseRuleIntent('using h; run'));
});
