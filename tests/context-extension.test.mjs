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

test('implicit introductions are determined by the current goal, never by guessing',()=>{
 const r=draftProof('任取 x\n假设 hx\n$P(x)$ | hx',['P'],new Map(),{goal:'∀ z : Nat, P z → P z'});
 assert.equal(r.complete,true);assert.equal(r.rows[0].step.type,'Nat');
 assert.equal(r.rows[1].step.type,'(P x)');
 assert.equal(draftProof('任取 x\n$P(x)$',['P'],new Map(),{goal:'∀ z, P z'}).term,null);
});
test('existential elimination creates distinct witness and evidence objects',()=>{
 const ctx=new Map([['h','∃ z : Nat, P z'],['f','∀ z : Nat, P z → R']]);
 const text='由 h 取 x，记 hx\n由 f、x、hx 得到 $R$';
 const r=draftProof(text,['P','R',...ctx.keys()],ctx);
 assert.equal(r.complete,true);
 assert.equal(r.rows[0].step.type,'Nat');assert.equal(r.rows[0].step.evidenceType,'(P x)');
 const witness=r.graph.nodes.find(n=>n.kind==='witness'),evidence=r.graph.nodes.find(n=>n.kind==='evidence');
 assert.notEqual(witness.id,evidence.id);assert.ok(evidence.dependencies.includes(witness.id));
 assert.ok(r.graph.nodes.at(-1).dependencies.includes(evidence.id));
 assert.match(r.term,/rcases duet_exists_x with ⟨x, hx⟩/);
});
test('existential elimination rejects nonexistentials, collisions and capture',()=>{
 for(const [type,phrase] of [['P','由 h 取 x，记 hx'],['∃ z : Nat, P z','由 h 取 x，记 x'],['∃ z : Nat, P x','由 h 取 x，记 hx'],['∃ z, P z','由 h 取 x，记 hx']]){
  const r=draftProof(phrase+'\n$R$',['h'],new Map([['h',type]]));
  assert.equal(r.term,null);assert.equal(r.rows[0].step,undefined);
 }
});
test('explicit witness annotation handles an implicit existential domain',()=>{
 const r=draftProof('由 h 取 x : $Nat$，记 hx\n$P(x)$ | hx',['P','h'],new Map([['h','∃ z, P z']]));
 assert.equal(r.rows[0].step.evidenceType,'(P x)');
 assert.equal(r.complete,true);
});
test('existential scope replay restores both bindings and preserves the original premise',()=>{
 const ctx=new Map([['h','∃ z : Nat, P z']]),scope=['P','h'];
 const input='由 h 取 x，记 hx\n$P(x)$ | hx',session=createDraftSession();
 session.evaluate(input,scope,ctx);
 const edited=input.replace('| hx','| from hx');
 const r=session.evaluate(edited,scope,ctx);
 assert.equal(r.reusedRows,1);assert.deepEqual(r.rows,draftProof(edited,scope,ctx).rows);
 const original=draftProof('由 h 取 x，记 hx\n$∃ z : Nat, P(z)$ | h',scope,ctx);
 assert.equal(original.complete,true);assert.match(original.term,/exact h$/);
});
test('an existential witness inherits the open source dependency',()=>{
 const r=draftProof('建立 h : $∃ z : Nat, P(z)$\n由 h 取 x，记 hx\n$P(x)$ | hx',['P']);
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.equal(r.rows[2].proofStatus,'depends-on-open');
});
