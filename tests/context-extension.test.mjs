import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession,compileNaturalDraft} from '../web/natural-draft.mjs';
import {extendGoal} from '../web/context-extension.mjs';
import {dependentNodes} from '../web/draft-graph.mjs';
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

test('generated existential copy avoids source and planned names and stays backend-compatible',()=>{
 const witness='x'.repeat(64),stem='duet_exists_'+witness.slice(0,40);
 const ctx=new Map([['h','∃ z : Nat, P z'],[stem,'Nat']]);
 const text='由 h 取 '+witness+'，记 hx\n$P('+witness+')$ | hx';
 const r=draftProof(text,['P',...ctx.keys()],ctx);
 assert.equal(r.complete,true);
 assert.equal(r.rows[0].step.copy,stem+'_1');
 assert.ok(r.rows[0].step.copy.length<=64);
});

test('disjunction elimination forks branch identities and returns only its common result',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['f','P → R'],['g','Q → R']]);
 const input='分情况讨论 h，建立 hR : $R$\n  左支 hp\n    $R$ | f hp\n  右支 hq\n    $R$ | g hq\n$R$ | hR';
 const r=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'R'});
 assert.equal(r.complete,true);
 assert.equal(r.steps[0].kind,'cases');
 assert.match(r.term,/cases h with[\s\S]*exact f hp[\s\S]*exact g hq/);
 const node=r.graph.nodes.find(n=>n.kind==='cases');
 assert.equal(node.branches.length,2);
 assert.notEqual(node.branches[0].binding.id,node.branches[1].binding.id);
 assert.deepEqual(node.branches.map(b=>b.constructor),['inl','inr']);
 assert.ok(node.dependencies.includes('context:3'),'the parent split depends on its source disjunction');
 assert.ok(dependentNodes(r.graph,['context:0']).includes(node.id),'changes to a declaration used by a branch invalidate the parent case result');
 const affectedByBranchProof=dependentNodes(r.graph,[node.branches[0].resultId]);
 assert.ok(affectedByBranchProof.includes(node.id),'editing a branch proof invalidates the common result');
 assert.ok(affectedByBranchProof.includes('line:6'),'editing a branch proof invalidates the parent continuation');
 assert.equal(r.graph.nodes.some(n=>['hp','hq'].includes(n.name)),false,'branch binders stay inside branch graphs');
 assert.ok(r.graph.nodes.find(n=>n.kind==='conclude').dependencies.includes(node.id),'the common result is available to the continuation');
});

test('sibling branches may reuse display names without sharing object identity',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['f','P → R'],['g','Q → R']]);
 const input='cases h, establish hR : $R$\n  left case hp\n    $R$ | f hp\n  right case hp\n    $R$ | g hp\n$R$ | hR';
 const r=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'R'});
 const branches=r.graph.nodes.find(n=>n.kind==='cases').branches;
 assert.equal(r.complete,true);
 assert.equal(branches[0].name,branches[1].name);
 assert.notEqual(branches[0].binding.id,branches[1].binding.id);
});

test('a branch-local hypothesis cannot leak to a sibling or parent continuation',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['f','P → R'],['g','Q → R']]);
 const sibling='cases h, establish hR : $R$\n  left case hp\n    $R$ | g hq\n  right case hq\n    $R$ | g hq\n$R$ | hR';
 assert.throws(()=>compileNaturalDraft(sibling,[...facts.keys()],facts,{goal:'R'}),/Line 3:/);
 const escaped='cases h, establish hR : $R$\n  left case hp\n    $R$ | f hp\n  right case hq\n    $R$ | g hq\n$R$ | hp';
 assert.throws(()=>compileNaturalDraft(escaped,[...facts.keys()],facts,{goal:'R'}));
});

test('an open case branch does not hide the other branch semantic graph',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['g','Q → R']]);
 const input='cases h, establish hR : $R$\n  left case hp\n    unsupported ⊛\n  right case hq\n    $R$ | g hq\n$R$ | hR';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'R'});
 const node=result.graph.nodes.find(n=>n.kind==='cases');
 assert.equal(result.complete,false);
 assert.deepEqual(node.branches.map(branch=>branch.status),['open','complete']);
 assert.ok(node.branches.every(branch=>branch.graph));
});

test('nested disjunctions preserve lexical branch scopes and match full recomputation',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['R','Prop'],['h','P ∨ Q'],['j','U ∨ V'],['f','P → U → R'],['g','P → V → R'],['k','Q → R']]);
 const input='分情况讨论 h，建立 hR : $R$\n  左支 hp\n    分情况讨论 j，建立 hpR : $R$\n      左支 hu\n        $R$ | f hp hu\n      右支 hv\n        $R$ | g hp hv\n    $R$ | hpR\n  右支 hq\n    $R$ | k hq\n$R$ | hR';
 const session=createDraftSession();
 const incremental=session.evaluate(input,[...facts.keys()],facts,{goal:'R'});
 const complete=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'R'});
 assert.equal(incremental.complete,true);
 assert.equal(incremental.reusedRows,0);
 assert.equal(incremental.term,complete.term);
 assert.deepEqual(incremental.graph,complete.graph);
 const outer=incremental.graph.nodes.find(n=>n.kind==='cases');
 const inner=outer.branches[0].graph.nodes.find(n=>n.kind==='cases');
 assert.ok(inner);
 assert.notEqual(outer.branches[0].binding.id,outer.branches[1].binding.id);
 assert.equal(outer.branches[0].graph.nodes.some(n=>n.name==='hq'),false);
});

test('case branches check their actual terminal annotations against the remaining goal',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ Q'],['p','P']]);
 const input='cases h, establish hR : $P$\n  left case hp\n    $P$ | hp\n  right case hq\n    $Q$ | hq\n$P$ | hR';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'P'});
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 const node=result.graph.nodes.find(n=>n.kind==='cases');
 assert.deepEqual(node.branches.map(branch=>branch.status),['complete','open']);
 assert.ok(result.rows.some(row=>row.line===5&&row.status==='unresolved'));
});
test('case branch introduction checks the residual goal, not the original universal',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ Q']]);
 const input='cases h, establish hR : $∀ z : Nat, P → P$\n  left case hp\n    任取 x\n    假设 ha\n    $P$ | ha\n  right case hq\n    任取 x\n    假设 hb\n    $P$ | hb';
 const r=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'∀ z : Nat, P → P'});
 assert.equal(r.complete,true);
 assert.match(r.term,/intro x/);
});
test('a case result different from the parent goal requires a continuation',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ Q'],['p','P']]);
 const input='cases h, establish hR : $P$\n  left case hp\n    $P$ | hp\n  right case hq\n    $P$ | p';
 const r=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'Q'});
 assert.equal(r.complete,false);assert.equal(r.term,null);
 assert.match(r.rows[0].reason,/enclosing goal/);
});

test('a parent continuation must establish the enclosing goal after a case split',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ P'],['p','P']]);
 const input='cases h, establish hR : $P$\n  left case hp\n    $P$ | hp\n  right case hq\n    $P$ | p\n$P$ | hR';
 const r=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'Q'});
 assert.equal(r.complete,false);
 assert.equal(r.term,null);
 assert.match(r.rows.at(-1).reason,/remaining goal/);
});

test('all branch-local declarations, not only case binders, expire after closure',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ Q'],['p','P']]);
 const prefix='cases h, establish hR : $P$\n  left case hp\n    establish temporary : $P$ | hp\n    $P$ | temporary\n  right case hq\n    $P$ | p\n';
 const scope=[...facts.keys()],session=createDraftSession();
 const bad=session.evaluate(prefix+'$P$ | temporary',scope,facts,{goal:'P'});
 assert.equal(bad.complete,false);
 assert.match(bad.rows.at(-1).reason,/forward local rule reference/);
 assert.equal(bad.term,null);
 const reuse=session.evaluate(prefix+'establish temporary : $P$ | hR\n$P$ | temporary',scope,facts,{goal:'P'});
 assert.equal(reuse.complete,true);
 assert.match(reuse.term,/exact temporary$/);
 const bound=session.evaluate(prefix+'$∀ temporary : Nat, P$ | external_rule',scope,facts,{goal:'∀ temporary : Nat, P'});
 assert.equal(bound.complete,true,'a bound variable with the same spelling is not an escaping reference');
});
