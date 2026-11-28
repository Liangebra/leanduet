import test from 'node:test';
import assert from 'node:assert/strict';
import {compileNaturalDraft,createDraftSession} from '../web/natural-draft.mjs';
import {planGoalOperation} from '../web/context-extension.mjs';

const pair=(first,second='hq')=>`split conjunction\n  first goal\n    ${first}\n  second goal\n    $Q$ | ${second}`;

test('goal operations distinguish intuitionistic negation from a two-child conjunction',()=>{
 const negation=planGoalOperation('¬ P',{kind:'assume',name:'hp',type:'P'});
 assert.equal(negation.kind,'negation-introduction');
 assert.equal(negation.logic,'intuitionistic');
 assert.deepEqual(negation.subgoals.map(goal=>goal.goal),['False']);
 assert.deepEqual(negation.subgoals[0].contextDelta.map(binding=>binding.type),['P']);
 const conjunction=planGoalOperation('P ∧ Q',{kind:'conjunction-introduction'});
 assert.equal(conjunction.closure.name,'And.intro');
 assert.deepEqual(conjunction.subgoals.map(goal=>goal.goal),['P','Q']);
 assert.deepEqual(conjunction.subgoals.map(goal=>goal.contextDelta),[[],[]]);
 assert.throws(()=>planGoalOperation('P → Q',{kind:'conjunction-introduction'}),/not a supported conjunction/);
 const cases=planGoalOperation('R',{kind:'disjunction-elimination',source:'h',sourceType:'P ∨ Q',branchNames:['hp','hq']});
 assert.equal(cases.logic,'intuitionistic');
 assert.equal(cases.closure.name,'Or.elim');
 assert.deepEqual(cases.subgoals.map(subgoal=>subgoal.contextDelta[0].type),['P','Q']);
});

test('classical reductio is explicit and its temporary negation stays local',()=>{
 const operation=planGoalOperation('P',{kind:'classical-reductio',name:'hnot'});
 assert.equal(operation.logic,'classical');
 assert.equal(operation.closure.name,'Classical.byContradiction');
 assert.deepEqual(operation.subgoals.map(goal=>goal.goal),['False']);
 assert.deepEqual(operation.subgoals[0].contextDelta.map(binding=>binding.type),['(¬ P)']);
 assert.equal(planGoalOperation('¬ P',{kind:'assume',name:'hp',type:'P'}).logic,'intuitionistic');
 const input='classical reductio hnot\n  contradiction\n    $False$ | h hnot';
 const facts=new Map([['h','¬ ¬ P']]);
 const result=compileNaturalDraft(input,['h'],facts,{goal:'P'});
 assert.equal(result.complete,true,JSON.stringify(result.rows,null,2));
 assert.equal(result.steps.at(-1).kind,'classical-reductio');
 assert.equal(result.steps.at(-1).goalOperation.logic,'classical');
 assert.match(result.term,/Classical\.byContradiction[\s\S]*intro hnot[\s\S]*change \(¬ P\) at hnot[\s\S]*exact h hnot/);
 const node=result.graph.nodes.find(item=>item.kind==='classical-reductio');
 assert.ok(node);
 assert.equal(node.subgoals[0].goal,'False');
 assert.ok(node.subgoals[0].graph.nodes.some(item=>item.name==='hnot'&&item.kind==='context'));
 assert.ok(!result.graph.nodes.some(item=>item.name==='hnot'),'the temporary negation must not escape to the parent graph');
 const unresolved=compileNaturalDraft('$P$ | ?', ['h'],facts,{goal:'P'});
 assert.ok(!unresolved.term?.includes('Classical.byContradiction'),'ordinary candidate generation must not insert classical reasoning');
 assert.throws(()=>compileNaturalDraft(input,['h','hnot'],new Map([['h','¬ ¬ P'],['hnot','Q']]),{goal:'P'}),/must be fresh/);
});

test('classical reductio composes in isolated disjunction branches',()=>{
 const input='cases h, establish result : $P$\n  left case hp\n    classical reductio hnot\n      contradiction\n        $False$ | hnot hp\n  right case hq\n    classical reductio hnot\n      contradiction\n        $False$ | hnot hq\n$P$ | result';
 const result=compileNaturalDraft(input,['h'],new Map([['h','P ∨ P']]),{goal:'P'});
 assert.equal(result.complete,true,JSON.stringify(result.rows,null,2));
 assert.match(result.term,/Classical\.byContradiction[\s\S]*inr hq[\s\S]*Classical\.byContradiction/);
 assert.ok(!result.graph.nodes.some(item=>item.name==='hnot'));
});

test('equivalence introduction opens both directions without a classical principle',()=>{
 const operation=planGoalOperation('P ↔ Q',{kind:'iff-introduction'});
 assert.equal(operation.logic,'intuitionistic');
 assert.equal(operation.closure.name,'Iff.intro');
 assert.deepEqual(operation.subgoals.map(goal=>goal.goal),['(P → Q)','(Q → P)']);
 const facts=new Map([['f','P → Q'],['g','Q → P']]);
 const input=`prove equivalence
  forward direction
    assume hp : $P$
    $Q$ | f hp
  reverse direction
    assume hq : $Q$
    $P$ | g hq`;
 const result=compileNaturalDraft(input,['f','g'],facts,{goal:'P ↔ Q'});
 assert.equal(result.complete,true);
 assert.equal(result.steps.at(-1).kind,'iff-intro');
 assert.equal(result.rows[0].proofStatus,'candidate');
 assert.match(result.term,/constructor[\s\S]*intro hp[\s\S]*exact f hp[\s\S]*intro hq[\s\S]*exact g hq/);
 const node=result.graph.nodes.find(item=>item.kind==='iff-intro');
 assert.deepEqual(node.subgoals.map(item=>item.status),['complete','complete']);
 assert.notEqual(node.subgoals[0].id,node.subgoals[1].id);
 assert.throws(()=>planGoalOperation('P → Q',{kind:'iff-introduction'}),/not a supported equivalence/);
});

test('existential introduction requires an explicit visible witness with a matching type',()=>{
 const operation=planGoalOperation('∃ x : Nat, P x',{kind:'existential-introduction',witness:'a',witnessType:'Nat',witnessId:'context:0'});
 assert.equal(operation.logic,'dependent-function');
 assert.equal(operation.closure.name,'Exists.intro');
 assert.deepEqual(operation.subgoals.map(goal=>goal.goal),['(P a)']);
 const input=`construct witness a
  witness property
    $P(a)$ | ha`;
 const facts=new Map([['a','Nat'],['ha','P a']]);
 const result=compileNaturalDraft(input,['a','ha'],facts,{goal:'∃ x : Nat, P x'});
 assert.equal(result.complete,true);
 assert.equal(result.steps.at(-1).kind,'exists-intro');
 assert.equal(result.steps.at(-1).goalOperation.witnessId,'context:0');
 assert.match(result.term,/refine ⟨a, \?_⟩[\s\S]*exact ha/);
 const node=result.graph.nodes.find(item=>item.kind==='exists-intro');
 assert.ok(node.dependencies.includes('context:0'),'the witness identity is an operation dependency');
 assert.deepEqual(node.subgoals.map(item=>item.status),['complete']);
 assert.throws(()=>compileNaturalDraft(input,['ha'],new Map([['ha','P Nat']]),{goal:'∃ x : Nat, P x'}),/uniquely visible typed local witness/);
 assert.throws(()=>compileNaturalDraft(input,['a','ha'],new Map([['a','Int'],['ha','P a']]),{goal:'∃ x : Nat, P x'}),/does not match the existential domain/);
 assert.throws(()=>planGoalOperation('∃ x : Nat, ∀ a : Nat, R x a',{
  kind:'existential-introduction',witness:'a',witnessType:'Nat'
 }),/captured/);
 assert.throws(()=>planGoalOperation('P',{kind:'existential-introduction',witness:'a',witnessType:'Nat'}),/not a supported existential/);
 const dependent=compileNaturalDraft(`construct witness a
  witness property
    $True$ | ht`,['α','a','ht'],new Map([['a','α'],['ht','True']]),{
  goal:'∃ x : α, True',openBindings:['α']
 });
 assert.equal(dependent.complete,true);
 assert.equal(dependent.rows[0].proofStatus,'depends-on-open',
  'a witness operation inherits dependencies from the witness type even when the predicate proof does not mention it');
});

test('explicit witness construction composes inside isolated disjunction branches',()=>{
 const input=`cases h, establish hex : $∃ x : Nat, P(x)$
  left case hpa
    construct witness a
      witness property
        $P(a)$ | hpa
  right case hq
    construct witness a
      witness property
        $P(a)$ | ha`;
 const result=compileNaturalDraft(input,['a','ha','h'],new Map([['a','Nat'],['ha','P a'],['h','P a ∨ Q']]),{goal:'∃ x : Nat, P x'});
 assert.equal(result.complete,true);
 assert.match(result.term,/cases h with[\s\S]*refine ⟨a, \?_⟩[\s\S]*exact hpa[\s\S]*refine ⟨a, \?_⟩[\s\S]*exact ha/);
 const cases=result.graph.nodes.find(node=>node.kind==='cases');
 assert.ok(cases.branches.every(branch=>branch.graph.nodes.some(node=>node.kind==='exists-intro')));
 assert.ok(cases.branches.every(branch=>branch.status==='complete'));
});

test('goal-operation child edits agree with a cold rebuild and retain later child structure',()=>{
 const scope=['f','g'],facts=new Map([['f','P → Q'],['g','Q → P']]);
 const input=`prove equivalence
  forward direction
    assume hp : $P$
    $Q$ | f hp
  reverse direction
    assume hq : $Q$
    $P$ | g hq`;
 const edited=input.replace('$P$ | g hq','显然 $P$ | g hq');
 const session=createDraftSession();
 session.evaluate(input,scope,facts,{goal:'P ↔ Q'});
 const incremental=session.evaluate(edited,scope,facts,{goal:'P ↔ Q'});
 const cold=compileNaturalDraft(edited,scope,facts,{goal:'P ↔ Q'});
 assert.ok(incremental.reusedRows>=1);
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.steps,cold.steps);
 assert.deepEqual(incremental.graph,cold.graph);
 assert.equal(incremental.term,cold.term);
 assert.ok(incremental.graph.nodes.find(node=>node.kind==='iff-intro').subgoals.every(goal=>goal.status==='complete'));
});

test('conjunction goal closes only after both isolated child proofs close',()=>{
 const context=new Map([['hp','P'],['hq','Q']]);
 const result=compileNaturalDraft(pair('$P$ | hp'),['hp','hq'],context,{goal:'P ∧ Q'});
 assert.equal(result.complete,true);
 assert.equal(result.leanVerification,'not-run');
 assert.equal(result.semanticFidelity,'not-assessed');
 assert.equal(result.steps.at(-1).kind,'and-intro');
 assert.deepEqual(result.steps.at(-1).subgoals.map(subgoal=>subgoal.goal),['P','Q']);
 assert.match(result.term,/constructor[\s\S]*·[\s\S]*exact hp[\s\S]*·[\s\S]*exact hq/);
 const node=result.graph.nodes.find(item=>item.kind==='and-intro');
 assert.equal(node.subgoals.length,2);
 assert.deepEqual(node.subgoals.map(subgoal=>subgoal.status),['complete','complete']);
 assert.notEqual(node.subgoals[0].id,node.subgoals[1].id);
 assert.deepEqual(node.goalOperation.subgoals.map(subgoal=>subgoal.scopeId),node.subgoals.map(subgoal=>subgoal.id));
});

test('subgoal-local assumptions are discharged and do not become sibling facts',()=>{
 const input=`split conjunction\n  first goal\n    假设 hp : $P$\n    $P$ | hp\n  second goal\n    $P$ | hp`;
 const facts=new Map([['hQ','Q']]);
 const result=createDraftSession().evaluate(input,['hQ'],facts,{goal:'(P → P) ∧ P'});
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 const operation=result.graph.nodes.find(item=>item.kind==='and-intro');
 assert.deepEqual(operation.subgoals.map(subgoal=>subgoal.status),['complete','open']);
 assert.ok(result.rows.some(row=>row.status==='unresolved'&&row.raw==='$P$ | hp'));
 assert.equal(result.leanVerification,'not-run');
});

test('a nested conjunction split returns through the enclosing disjunction scope',()=>{
 const input=`cases h, establish hab : $A ∧ B$\n  left case hp\n    split conjunction\n      first goal\n        $A$ | fa hp\n      second goal\n        $B$ | fb hp\n  right case hq\n    split conjunction\n      first goal\n        $A$ | ga hq\n      second goal\n        $B$ | gb hq\n$A ∧ B$ | hab`;
 const facts=new Map([['h','P ∨ Q'],['fa','P → A'],['fb','P → B'],['ga','Q → A'],['gb','Q → B']]);
 const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'A ∧ B'});
 assert.equal(result.complete,true);
 assert.match(result.term,/cases h with[\s\S]*constructor[\s\S]*constructor/);
 const cases=result.graph.nodes.find(item=>item.kind==='cases');
 assert.ok(cases.branches.every(branch=>branch.status==='complete'));
 assert.ok(cases.branches.every(branch=>branch.graph.nodes.some(node=>node.kind==='and-intro')));
 assert.equal(cases.goalOperation.kind,'disjunction-elimination');
 assert.deepEqual(cases.goalOperation.subgoals.map(subgoal=>subgoal.contextDelta[0].scopeId),cases.branches.map(branch=>branch.id));
});

test('nested subgoal declarations are discharged before an enclosing case returns',()=>{
 const input=`cases h, establish hab : $((P → P) ∧ (P → P))$
  left case hleft
    split conjunction
      first goal
        assume hp : $P$
        $P$ | hp
      second goal
        assume hp : $P$
        $P$ | hp
  right case hright
    split conjunction
      first goal
        assume hp : $P$
        $P$ | hp
      second goal
        assume hp : $P$
        $P$ | hp`;
 const result=compileNaturalDraft(input,['h'],new Map([['h','P ∨ P']]),{goal:'(P → P) ∧ (P → P)'});
 assert.equal(result.complete,true);
 assert.equal(result.rows[0].proofStatus,'candidate');
 const cases=result.graph.nodes.find(node=>node.kind==='cases');
 assert.ok(cases.branches.every(branch=>branch.status==='complete'));
 for(const branch of cases.branches){
  const conjunction=branch.graph.nodes.find(node=>node.kind==='and-intro');
  assert.ok(conjunction);
  assert.deepEqual(conjunction.subgoals.map(subgoal=>subgoal.status),['complete','complete']);
  const nestedIds=conjunction.subgoals.flatMap(subgoal=>subgoal.graph.nodes.filter(node=>node.kind!=='context').map(node=>node.id));
  assert.ok(nestedIds.every(id=>id.startsWith(branch.id+'/subgoal:')),'nested identity paths retain their child scope');
 }
});

test('an open exact-search obligation stays distinct from a closed conjunction proof',()=>{
 const input=`split conjunction\n  first goal\n    $P$\n  second goal\n    $Q$ | hq`;
 const result=createDraftSession().evaluate(input,['hq'],new Map([['hq','Q']]),{goal:'P ∧ Q'});
 assert.equal(result.complete,true,'the bounded draft is renderable even though the first proof is open');
 assert.equal(result.rows[0].proofStatus,'open');
 assert.equal(result.leanVerification,'not-run');
 assert.match(result.term,/exact\?/);
 const node=result.graph.nodes.find(item=>item.kind==='and-intro');
 assert.deepEqual(node.subgoals.map(subgoal=>subgoal.status),['open-obligation','complete']);
 assert.ok(result.rows.some(row=>row.raw==='$Q$ | hq'&&row.proofStatus==='candidate'));
});

test('child-local open declarations are discharged at the goal boundary',()=>{
 const input=`split conjunction
  first goal
    establish hx : $P$ | ?
    $P$ | hx
  second goal
    $Q$ | hq`;
 const result=createDraftSession().evaluate(input,['hq'],new Map([['hq','Q']]),{goal:'P ∧ Q'});
 assert.equal(result.complete,true);
 assert.equal(result.rows[0].proofStatus,'open');
 assert.deepEqual(result.openBindings,[],'hx belongs to the first child scope and must not escape');
 const node=result.graph.nodes.find(item=>item.kind==='and-intro');
 assert.deepEqual(node.subgoals.map(subgoal=>subgoal.status),['open-obligation','complete']);
});

test('an unparseable first subgoal leaves the second subgoal graph available',()=>{
 const input=`split conjunction\n  first goal\n    unsupported sentence\n  second goal\n    $Q$ | hq`;
 const result=createDraftSession().evaluate(input,['hq'],new Map([['hq','Q']]),{goal:'P ∧ Q'});
 assert.equal(result.complete,false);
 const node=result.graph.nodes.find(item=>item.kind==='and-intro');
 assert.deepEqual(node.subgoals.map(subgoal=>subgoal.status),['open','complete']);
 assert.ok(result.rows.some(row=>row.raw==='$Q$ | hq'&&row.proofStatus==='candidate'));
});

test('edited child drafts preserve physical addresses and match a cold evaluation',()=>{
 const context=new Map([['hp','P'],['hq','Q']]),scope=['hp','hq'];
 const input=`split conjunction\n  first goal\n\n    $P$ | hp\n  second goal\n    $Q$ | hq`;
 const edited=input.replace('$Q$ | hq','显然 $Q$ | hq');
 const session=createDraftSession();
 const initial=session.evaluate(input,scope,context,{goal:'P ∧ Q'});
 const incremental=session.evaluate(edited,scope,context,{goal:'P ∧ Q'});
 const cold=compileNaturalDraft(edited,scope,context,{goal:'P ∧ Q'});
 assert.equal(initial.complete,true);
 assert.ok(incremental.reusedRows>=1);
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.steps,cold.steps);
 assert.deepEqual(incremental.graph,cold.graph);
 assert.equal(incremental.term,cold.term);
 const first=incremental.graph.nodes.find(node=>node.kind==='and-intro').subgoals[0];
 assert.ok(first.graph.nodes.some(node=>node.id.endsWith('/line:4')),'blank lines retain physical row addresses');
});

test('conjunction parser enforces the same bounded nonblank-line budget as case proofs',()=>{
 const body=Array.from({length:62},()=> '    unsupported sentence').join('\n');
 const input=`split conjunction\n  first goal\n${body}\n  second goal\n    $Q$ | hq`;
 assert.throws(()=>compileNaturalDraft(input,['hq'],new Map([['hq','Q']]),{goal:'P ∧ Q'}),/at most 64 nonblank lines/);
});
