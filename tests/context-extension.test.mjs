import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession} from '../web/natural-draft.mjs';
import {extendGoal} from '../web/context-extension.mjs';
const scope=['P'],facts=new Map();
const input='任取 x : $Nat$\n假设 hp : $P(x)$\n$P(x)$ | hp';
const goal='∀ z : Nat, P z → P z';
test('universal and implication introductions consume the current goal',()=>{
 const r=draftProof(input,scope,facts,{goal});
 assert.equal(r.complete,true);
 assert.equal(r.remainingGoal,'(P x)');
 assert.equal(r.term,'by\n  intro x\n  change Nat at x\n  intro hp\n  change (P x) at hp\n  show (P x)\n  exact hp');
 assert.deepEqual(r.graph.nodes.map(n=>n.kind),['context','introduce','assume','conclude']);
});
test('an unrelated hypothesis cannot be introduced',()=>{
 for(const g of [null,'P a','∀ z : Int, P z → P z','∀ z : Nat, Q z → P z']){
  const r=draftProof(input,scope,facts,{goal:g});
  assert.equal(r.term,null);
 }
});
test('capture is rejected while inner shadowing remains intact',()=>{
 assert.throws(()=>extendGoal('∀ z : Nat, ∀ x : Nat, z = x',{kind:'introduce',name:'x',type:'Nat'}));
 assert.equal(extendGoal('∀ z : Nat, ∀ z : Nat, z = z',{kind:'introduce',name:'x',type:'Nat'}),'(∀ z : Nat, (z = z))');
});
test('incremental replay restores the consumed goal',()=>{
 const s=createDraftSession();
 s.evaluate(input,scope,facts,{goal});
 const edited=input.replace('| hp','| from hp');
 const r=s.evaluate(edited,scope,facts,{goal});
 assert.equal(r.reusedRows,2);
 assert.deepEqual(r.rows,draftProof(edited,scope,facts,{goal}).rows);
 assert.equal(s.evaluate(edited,scope,facts,{goal:'P a'}).reusedRows,0);
});

test('Lean pretty-printed binders and inferred domains accept explicit user annotations',()=>{
 const r=draftProof('任取 x : $Nat$\n假设 hx : $x ∈ s$\n$x ∈ s$ | hx',['s'],new Map(),{goal:'∀ z, z ∈ s → z ∈ s'});
 assert.equal(r.complete,true);
 assert.equal(r.remainingGoal,'(x ∈ s)');
 assert.equal(extendGoal('∀ (z : Nat), P z',{kind:'introduce',name:'x',type:'Nat'}),'(P x)');
});
test('scope dependencies exist even when a proof does not mention its binder',()=>{
 const r=draftProof('任取 x : $Nat$\n$P$ | p',['P','p'],new Map([['p','P']]),{goal:'∀ z : Nat, P'});
 assert.deepEqual(r.graph.nodes.at(-1).scopeRefs,['line:1']);
 assert.ok(r.graph.nodes.at(-1).dependencies.includes('line:1'));
});
