import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession,compileNaturalDraft} from '../web/natural-draft.mjs';
import {extendGoal} from '../web/context-extension.mjs';
import {dependentNodes} from '../web/draft-graph.mjs';
import {forkProofScope,proofScopeFacts,proofScopeNames,resolveProofName,rootProofScope} from '../web/proof-scope.mjs';
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
 assert.equal(r.completionKind,'structural-export-ready');
 assert.equal(r.leanVerification,'not-run');
 assert.equal(node.resolutionStatus,'candidate-unverified');
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

test('ordinary proof lines can surround sequential scoped case blocks',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['R','Prop'],['T','Prop'],
  ['h','P ∨ Q'],['j','U ∨ V'],['p','P'],['f','P → R'],['g','P → T'],['k','Q → T'],['l','U → T'],['m','V → T']]);
 const input='establish hr : $R$ | f p\n'+
  'cases h, establish hT : $T$\n  left case hp\n    $T$ | g hp\n  right case hq\n    $T$ | k hq\n'+
  'establish ht : $T$ | hT\n'+
  'cases j, establish jT : $T$\n  left case hu\n    $T$ | l hu\n  right case hv\n    $T$ | m hv\n'+
  '$T$ | jT';
 const session=createDraftSession(),scope=[...facts.keys()];
 const result=session.evaluate(input,scope,facts,{goal:'T'});
 assert.equal(result.complete,true);
 assert.deepEqual(result.steps.map(step=>step.kind),['establish','cases','establish','cases','conclude']);
 assert.deepEqual(result.graph.nodes.filter(node=>node.kind==='cases').map(node=>node.id),['line:2','line:8']);
 assert.match(result.term,/have hr : R := f p[\s\S]*cases h with[\s\S]*have ht : T := hT[\s\S]*cases j with[\s\S]*exact jT/);
 const edited=input.replace('$T$ | jT','$T$ | ht');
 const incremental=session.evaluate(edited,scope,facts,{goal:'T'});
 const cold=createDraftSession().evaluate(edited,scope,facts,{goal:'T'});
 assert.ok(incremental.reusedRows>0,'the unchanged linear prefix should survive the later edit');
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.steps,cold.steps);
 assert.deepEqual(incremental.graph,cold.graph);
});

test('a failed prose prefix still leaves later sequential case structure available',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['T','Prop'],
  ['h','P ∨ Q'],['j','U ∨ V'],['k','Q → T'],['l','U → T'],['m','V → T']]);
 const input='unsupported ⊛\n'+
  'cases h, establish hT : $T$\n  left case hp\n    unsupported ⊛\n  right case hq\n    $T$ | k hq\n'+
  'establish ht : $T$ | hT\n'+
  'cases j, establish jT : $T$\n  left case hu\n    $T$ | l hu\n  right case hv\n    $T$ | m hv\n$T$ | jT';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'T'});
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 assert.equal(result.graph.nodes.filter(node=>node.kind==='cases').length,2);
 assert.ok(result.rows.some(row=>row.raw==='establish ht : $T$ | hT'));
 assert.equal(result.rows.find(row=>row.raw==='unsupported ⊛').resolutionStatus,'unsupported');
});

test('a branch may establish a local fact before a nested case block',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['T','Prop'],
  ['h','P ∨ Q'],['j','U ∨ V'],['f','P → U'],['g','U → T'],['k','V → T'],['m','Q → T']]);
 const input='cases h, establish ht : $T$\n'+
  '  left case hp\n    establish hu : $U$ | f hp\n'+
  '    cases j, establish jt : $T$\n      left case hj\n        $T$ | g hu\n      right case hv\n        $T$ | k hv\n'+
  '    $T$ | jt\n  right case hq\n    $T$ | m hq\n$T$ | ht';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'T'});
 assert.equal(result.complete,true);
 const countCases=graph=>(graph.nodes||[]).reduce((count,node)=>count+(node.kind==='cases'?1:0)+
  (node.branches||[]).reduce((nested,branch)=>nested+countCases(branch.graph||{nodes:[]}),0),0);
 assert.equal(countCases(result.graph),2);
 assert.match(result.term,/have hu : U := f hp[\s\S]*cases j with[\s\S]*exact ht/);
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

test('a branch-local name shadows only inside its child scope',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['hp','Q'],['f','P → R'],['g','Q → R']]);
 const input='cases h, establish hR : $R$\n  left case hp\n    $R$ | f hp\n  right case hp\n    $R$ | g hp\n$Q$ | hp';
 const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'Q'});
 const node=result.graph.nodes.find(n=>n.kind==='cases');
 const [left,right]=node.branches;
 assert.equal(result.complete,true);
 assert.equal(left.name,'hp');assert.equal(right.name,'hp');
 assert.notEqual(left.binding.id,right.binding.id);
 assert.notEqual(left.binding.id,'context:4');assert.notEqual(right.binding.id,'context:4');
 assert.ok(left.graph.nodes.some(n=>n.id===left.binding.id&&n.type==='P'));
 assert.ok(right.graph.nodes.some(n=>n.id===right.binding.id&&n.type==='Q'));
 assert.ok(result.graph.nodes.find(n=>n.kind==='conclude').dependencies.includes('context:4'),
  'the parent continuation resolves the original hp after both branches close');
});

test('root duplicates remain ambiguous but a child may shadow their spelling',()=>{
 const root=rootProofScope(['h','h'],new Map([['h','P']]));
 assert.equal(resolveProofName(root,'h').status,'ambiguous');
 const child=forkProofScope(root,{id:'branch',goal:'Q',binding:{id:'branch:hp',name:'h',type:'Q'},allowShadow:true});
 assert.equal(resolveProofName(root,'h').status,'ambiguous','the child must not mutate its parent context');
 assert.equal(resolveProofName(child,'h').binding.id,'branch:hp');
 assert.deepEqual(proofScopeNames(child),['h']);
 assert.equal(proofScopeFacts(child).get('h'),'Q');
});

test('branch shadowing rejects parent references that the bounded formula view cannot capture safely',()=>{
 const facts=new Map([['P','Nat → Prop'],['Q','Prop'],['h','P z ∨ Q'],['z','Nat'],['f','P z']]);
 const input='cases h, establish hz : $P(z)$\n  left case z\n    $P(z)$ | f\n  right case hq\n    $P(z)$ | f';
 assert.throws(()=>compileNaturalDraft(input,[...facts.keys()],facts,{goal:'P(z)'}),/would capture a parent reference/);
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
 assert.equal(node.resolutionStatus,'open-obligation');
 assert.equal(result.completionKind,'incomplete');
 assert.equal(result.leanVerification,'not-run');
 assert.equal(result.rows.find(row=>row.raw==='unsupported ⊛').resolutionStatus,'unsupported');
 assert.equal(result.complete,false);
 assert.deepEqual(node.branches.map(branch=>branch.status),['open','complete']);
 assert.ok(node.branches.every(branch=>branch.graph));
});

test('an open branch preserves the parent continuation as dependent semantic structure',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['S','Prop'],['h','P ∨ Q'],['g','Q → R'],['k','R → S']]);
 const input='cases h, establish hR : $R$\n  left case hp\n    unsupported ⊛\n  right case hq\n    $R$ | g hq\n\nestablish r : $R$ | hR\n$S$ | from r and k';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'S'});
 const node=result.graph.nodes.find(n=>n.kind==='cases');
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 assert.deepEqual(node.branches.map(branch=>branch.status),['open','complete']);
 assert.deepEqual(result.rows.filter(row=>row.line>=7).map(row=>row.line),[7,8]);
 assert.equal(result.rows.find(row=>row.line===7).proofStatus,'depends-on-open');
 assert.equal(result.rows.find(row=>row.line===8).proofStatus,'depends-on-open');
 const intermediate=result.graph.nodes.find(n=>n.id==='line:7');
 const conclusion=result.graph.nodes.find(n=>n.id==='line:8');
 assert.ok(intermediate.dependencies.includes(node.id),'the continuation cites the provisional common result');
 assert.ok(conclusion.dependencies.includes(intermediate.id),'later prose remains connected to its local result');
});

test('resolving an open branch closes the provisional dependency and matches a cold evaluation',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['f','P → R'],['g','Q → R']]);
 const open='cases h, establish hR : $R$\n  left case hp\n    unsupported ⊛\n  right case hq\n    $R$ | g hq\n$R$ | hR';
 const resolved=open.replace('unsupported ⊛','$R$ | f hp');
 const session=createDraftSession();
 assert.equal(session.evaluate(open,[...facts.keys()],facts,{goal:'R'}).complete,false);
 const incremental=session.evaluate(resolved,[...facts.keys()],facts,{goal:'R'});
 const cold=createDraftSession().evaluate(resolved,[...facts.keys()],facts,{goal:'R'});
 assert.equal(incremental.complete,true);
 assert.ok(incremental.term);
 assert.equal(incremental.rows.at(-1).proofStatus,'candidate');
 assert.equal(incremental.reusedRows,1,'the unaffected sibling branch is reused');
 assert.deepEqual(incremental.graph,cold.graph);
 assert.deepEqual(incremental.rows,cold.rows);
});

test('editing a branch conclusion reuses its unchanged scoped prefix and matches cold evaluation',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['R','Prop'],['h','P ∨ Q'],
  ['toU','P → U'],['f','P → U → R'],['f2','P → U → R'],['q','Q → R']]);
 const scope=[...facts.keys()];
 const input='cases h, establish hR : $R$\n  left case hp\n    establish hu : $U$ | toU hp\n    establish rr : $R$ | f hp hu\n    $R$ | rr\n  right case hq\n    $R$ | q hq\n$R$ | hR';
 const edited=input.replace('$R$ | rr','$R$ | f2 hp hu');
 const session=createDraftSession();
 assert.equal(session.evaluate(input,scope,facts,{goal:'R'}).complete,true);
 const incremental=session.evaluate(edited,scope,facts,{goal:'R'});
 const cold=compileNaturalDraft(edited,scope,facts,{goal:'R'});
 assert.equal(incremental.complete,true);
 assert.ok(incremental.reusedRows>=3,'two unchanged rows in the edited branch and its sibling should be reused');
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.steps,cold.steps);
 assert.deepEqual(incremental.graph,cold.graph);
 assert.equal(incremental.term,cold.term);
});

test('adding a same-typed premise invalidates branch candidates that depended on absence',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['r1','R']]);
 const scope=[...facts.keys()];
 const input='cases h, establish hR : $R$\n  left case hp\n    $R$\n  right case hq\n    $R$\n$R$ | r1';
 const session=createDraftSession();
 const first=session.evaluate(input,scope,facts,{goal:'R'});
 assert.deepEqual(first.rows.filter(row=>row.raw==='$R$').map(row=>row.candidates.map(c=>c.term)),[['r1'],['r1']]);
 facts.set('r2','R');scope.push('r2');
 const updated=session.evaluate(input,scope,facts,{goal:'R'});
 const cold=compileNaturalDraft(input,scope,facts,{goal:'R'});
 assert.equal(updated.reusedRows,0,'the branch context changed, so cached candidate sets must be rebuilt');
 assert.deepEqual(updated.rows.filter(row=>row.raw==='$R$').map(row=>row.candidates.map(c=>c.term)),[['r1','r2'],['r1','r2']]);
 assert.deepEqual(updated.rows,cold.rows);
 assert.deepEqual(updated.graph,cold.graph);
});

test('a memoized scoped result is isolated from caller mutation',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['f','P → R'],['g','Q → R']]);
 const scope=[...facts.keys()];
 const input='cases h, establish hR : $R$\n  left case hp\n    $R$ | f hp\n  right case hq\n    $R$ | g hq\n$R$ | hR';
 const session=createDraftSession(),first=session.evaluate(input,scope,facts,{goal:'R'});
 first.rows[0].name='mutated by caller';first.graph.nodes.find(node=>node.kind==='cases').name='mutated graph';
 const replay=session.evaluate(input,scope,facts,{goal:'R'}),cold=compileNaturalDraft(input,scope,facts,{goal:'R'});
 assert.equal(replay.reusedRows,replay.rows.length);
 assert.deepEqual(replay.rows,cold.rows);
 assert.deepEqual(replay.graph,cold.graph);
});

test('changing only a parent object identity invalidates the scoped memo',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['f','P → R'],['g','Q → R']]);
 const scope=[...facts.keys()];
 const input='cases h, establish hR : $R$\n  left case hp\n    $R$ | f hp\n  right case hq\n    $R$ | g hq\n$R$ | hR';
 const original=rootProofScope(scope,facts,{goal:'R'});
 const revised={...original,bindings:original.bindings.map((binding,index)=>({...binding,id:'context:'+(index+20)}))};
 const session=createDraftSession();
 session.evaluate(input,scope,facts,{goal:'R',_proofScope:original});
 const incremental=session.evaluate(input,scope,facts,{goal:'R',_proofScope:revised});
 const cold=compileNaturalDraft(input,scope,facts,{goal:'R',_proofScope:revised});
 assert.equal(incremental.reusedRows,0);
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.graph,cold.graph);
});

test('a branch local name remains unavailable in a continuation after its branch is open',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['g','Q → R']]);
 const input='cases h, establish hR : $R$\n  left case hp\n    unsupported ⊛\n  right case hq\n    $R$ | g hq\n$R$ | hp';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'R'});
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 assert.match(result.rows.at(-1).reason,/unavailable local rule|forward local rule reference/);
});

test('an open upstream branch does not suppress final goal consistency checks',()=>{
 const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['g','Q → R'],['q','Q']]);
 const input='cases h, establish hR : $R$\n  left case hp\n    unsupported ⊛\n  right case hq\n    $R$ | g hq\n$Q$ | q';
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'R'});
 assert.equal(result.complete,false);
 assert.match(result.rows.at(-1).reason,/remaining goal/);
 assert.equal(result.rows.at(-1).status,'unresolved');
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
