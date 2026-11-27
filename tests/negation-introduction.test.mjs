import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof} from '../web/natural-draft.mjs';
import {extendGoal,inferIntroduction} from '../web/context-extension.mjs';

test('negation introduction opens only the negated proposition and leaves False as the goal',()=>{
 for(const goal of ['¬ P','Not P','P → False']){
  const result=draftProof('假设 hp\n$False$ | hnot hp',['P','hnot'],new Map([['hnot','P → False']]),{goal});
  assert.equal(result.complete,true,goal);
  assert.equal(result.remainingGoal,'False',goal);
  assert.match(result.term,/intro hp[\s\S]*show False[\s\S]*exact hnot hp/);
 }
 assert.equal(inferIntroduction('¬ P','assume'),'P');
 assert.equal(extendGoal('¬ P',{kind:'assume',name:'hp',type:'P'}),'False');
});

test('negation introduction rejects an unrelated assumption and never changes a positive goal',()=>{
 assert.throws(()=>extendGoal('¬ P',{kind:'assume',name:'hq',type:'Q'}),/matching implication or negation/);
 assert.throws(()=>inferIntroduction('P','assume'),/does not determine/);
 const invalid=draftProof('假设 hp\n$False$ | hp',['P'],new Map(),{goal:'¬ P'});
 assert.equal(invalid.complete,false);
 assert.equal(invalid.term,null);
 assert.match(invalid.rows.at(-1).reason,/Known local premise hp has type P, not False/);
});
