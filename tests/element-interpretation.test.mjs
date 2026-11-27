import test from 'node:test';
import assert from 'node:assert/strict';
import {compileNaturalDraft,createDraftSession,draftProof} from '../web/natural-draft.mjs';
import {elementInterpretationCandidates,parseElementRequest} from '../web/element-interpretation.mjs';
import {planGoalOperation} from '../web/context-extension.mjs';
import {reconcileDraftIdentity,migrateDraftChoices} from '../web/draft-identity.mjs';

test('element requests keep a shared utterance and expose universal and existential operations',()=>{
 const request=parseElementRequest('take an element x satisfying $P(x)$');
 assert.equal(request.kind,'element-request');
 assert.equal(request.name,'x');
 assert.equal(request.property,'(P x)');
 const result=elementInterpretationCandidates(request,{goal:'∀ x : Nat, P x',scope:['hall','he'],
  facts:new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]),scopeIds:['context:0','context:1']});
 assert.equal(result.status,'ambiguous');
 assert.deepEqual(result.candidates.map(candidate=>candidate.operation),['universal-introduction','existential-elimination']);
 assert.notEqual(result.candidates[0].choice,result.candidates[1].choice);
 assert.equal(result.candidates[1].sourceId,'context:1');
});

test('a typed element request recognizes Lean’s nondependent Pi arrow as universal introduction',()=>{
 const request=parseElementRequest('take an element z : $Nat$ satisfying $P$');
 const result=elementInterpretationCandidates(request,{goal:'Nat → P',scope:['P','he'],
  facts:new Map([['P','Prop'],['he','∃ y : Nat, P']])});
 assert.equal(result.status,'ambiguous');
 assert.deepEqual(result.candidates.map(candidate=>candidate.operation),['universal-introduction','existential-elimination']);
 assert.equal(result.candidates[0].type,'Nat');
 const operation=planGoalOperation('Nat → P',{kind:'introduce',name:'z',type:'Nat'});
 assert.equal(operation.subgoals[0].goal,'P');
 assert.equal(operation.subgoals[0].contextDelta[0].name,'z');
 assert.equal(operation.subgoals[0].contextDelta[0].kind,'universal-variable');
});
test('an explicit element type can fill an omitted printed existential domain',()=>{
 const request=parseElementRequest('take an element z : $Nat$ satisfying $P$');
 const result=elementInterpretationCandidates(request,{goal:'Nat → P',scope:['P','he'],
  facts:new Map([['P','Prop'],['he','∃ y, P']])});
 assert.equal(result.status,'ambiguous');
 assert.deepEqual(result.candidates.map(candidate=>candidate.operation),['universal-introduction','existential-elimination']);
 assert.equal(result.candidates[1].type,'Nat');
 const mismatch=elementInterpretationCandidates(request,{goal:'Nat → P',scope:['P','he'],
  facts:new Map([['P','Prop'],['he','∃ y : Int, P']])});
 assert.deepEqual(mismatch.candidates.map(candidate=>candidate.operation),['universal-introduction']);
});

test('Chinese arbitrary wording rules out existential extraction',()=>{
 const request=parseElementRequest('取任意元素 x：$Nat$ 满足 $P(x)$');
 const result=elementInterpretationCandidates(request,{goal:'∀ y : Nat, P y',scope:['he'],facts:new Map([['he','∃ y : Nat, P y']])});
 assert.equal(result.status,'unique');
 assert.equal(result.candidates[0].operation,'universal-introduction');
 assert.equal(result.candidates[0].type,'Nat');
});

test('an explicit source constrains an element request to a matching existential witness',()=>{
 const request=parseElementRequest('take an element x satisfying $P(x)$ from he');
 const result=elementInterpretationCandidates(request,{goal:'Q',scope:['he','he2'],
  facts:new Map([['he','∃ y : Nat, P y'],['he2','∃ y : Int, P y']]),scopeIds:['context:4','context:5']});
 assert.equal(result.status,'unique');
 assert.equal(result.candidates[0].sourceId,'context:4');
 assert.equal(result.candidates[0].type,'Nat');
});

test('operation ambiguity remains unresolved without manufacturing a local binding',()=>{
 const session=createDraftSession();
 const result=session.evaluate('take an element x satisfying $P(x)$\n$P(x)$ | hx',
  ['hall','he'],new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]),{goal:'∀ x : Nat, P x',continuation:true});
 assert.equal(result.rows[0].resolutionStatus,'ambiguous');
 assert.equal(result.rows[0].candidates.length,2);
 assert.equal(result.rows[0].step,undefined);
 assert.equal(result.rows[1].status,'unresolved');
 assert.match(result.rows[1].reason,/unavailable local object|forward reference|Ambiguous/i);
});

test('choosing the universal operation advances the dependent goal and retains alternatives',()=>{
 const facts=new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]);
 const input='take an element x satisfying $P(x)$\n$P(x)$ | hall x';
 const first=createDraftSession().evaluate(input,['hall','he'],facts,{goal:'∀ x : Nat, P x'});
 const candidate=first.rows[0].candidates.find(value=>value.operation==='universal-introduction');
 assert.ok(candidate);
 const chosen=createDraftSession().evaluate(input,['hall','he'],facts,{goal:'∀ x : Nat, P x',choices:new Map([[1,candidate.choice]])});
 assert.equal(chosen.complete,true);
 assert.equal(chosen.rows[0].step.kind,'introduce');
 assert.equal(chosen.rows[0].candidates.length,1,'the explicit final goal removes the witness reading');
 assert.equal(chosen.rows[0].candidates[0].constraints[0].kind,'remaining-goal');
 assert.match(chosen.term,/intro x[\s\S]*exact hall x/);
});

test('the explicit remaining goal can select a witness reading without asserting its proof relevance',()=>{
 const facts=new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]);
 const input='take an element x satisfying $P(x)$\n$∀ y : Nat, P(y)$ | hall';
 const result=createDraftSession().evaluate(input,['hall','he'],facts,{goal:'∀ y : Nat, P y'});
 assert.equal(result.complete,true);
 assert.equal(result.rows[0].step.kind,'obtain');
 assert.equal(result.rows[0].operationConstraint.status,'matched');
 assert.equal(result.rows[0].candidates[0].operation,'existential-elimination');
});

test('a contradictory explicit conclusion rejects every operation candidate',()=>{
 const result=createDraftSession().evaluate('take an element x satisfying $P(x)$\n$Q$ | hq',
  ['he','hq'],new Map([['he','∃ y : Nat, P y'],['hq','Q']]),{goal:'∀ x : Nat, P x'});
 assert.equal(result.rows[0].resolutionStatus,'incompatible-constraints');
 assert.equal(result.rows[0].rejectedCandidates.length,2);
 assert.equal(result.complete,false);
});

test('choosing existential extraction introduces the witness and its local evidence',()=>{
 const facts=new Map([['he','∃ y : Nat, P y'],['hq','Q']]);
 const input='take an element x satisfying $P(x)$ from he\n$Q$ | hq';
 const result=createDraftSession().evaluate(input,['he','hq'],facts,{goal:'Q'});
 assert.equal(result.complete,true);
 assert.equal(result.rows[0].step.kind,'obtain');
 assert.equal(result.rows[0].step.name,'x');
 assert.equal(result.rows[0].step.evidenceName,'h_x');
 assert.equal(result.rows[0].step.evidenceType,'(P x)');
 assert.equal(result.rows[0].candidates[0].operation,'existential-elimination');
 const witnessNode=result.graph.nodes.find(node=>node.kind==='witness');
 assert.equal(witnessNode.alternatives.length,1,'the graph keeps the operation candidate for revision matching');
 assert.equal(witnessNode.selectedCandidate,witnessNode.alternatives[0].id);
 assert.match(result.term,/rcases duet_exists_x with ⟨x, h_x⟩[\s\S]*exact hq/);
});

test('an existential operation choice migrates by premise identity after line movement',()=>{
 const facts=new Map([['he','∃ y : Nat, P y'],['hq','Q']]);
 const source='take an element x satisfying $P(x)$ from he\n$Q$ | hq';
 const oldResult=createDraftSession().evaluate(source,['he','hq'],facts,{goal:'Q'});
 const choice=oldResult.rows[0].candidates[0].choice;
 const previous=reconcileDraftIdentity(null,oldResult.graph);
 const shiftedResult=createDraftSession().evaluate('\n'+source,['he','hq'],facts,{goal:'Q',choices:new Map([[2,choice]])});
 const current=reconcileDraftIdentity(previous,shiftedResult.graph);
 assert.deepEqual([...migrateDraftChoices(previous,current,new Map([[1,choice]]))],[[2,choice]]);
});

test('a same-draft local existential source uses its object identity rather than its display name',()=>{
 const facts=new Map([['he','∃ y : Nat, P y'],['hq','Q']]);
 const source='$∃ y : Nat, P(y)$ | he\ntake an element x satisfying $P(x)$ from duet_h1\n$Q$ | hq';
 const oldResult=compileNaturalDraft(source,['he','hq'],facts,{goal:'Q'});
 const candidate=oldResult.rows[1].candidates[0];
 assert.equal(candidate.sourceId,'line:1');
 const choices=new Map([[2,candidate.choice]]),previous=reconcileDraftIdentity(null,oldResult.graph);
 const shifted=compileNaturalDraft('\n'+source,['he','hq'],facts,{goal:'Q'});
 const current=reconcileDraftIdentity(previous,shifted.graph);
 const migrated=migrateDraftChoices(previous,current,choices);
 assert.equal(migrated.get(3),shifted.rows[1].candidates[0].choice);
 assert.notEqual(migrated.get(3),candidate.choice,'the new line address changes while the matched source object identity is preserved');
});

test('unsupported matches, missing sources, and search budgets stay distinct',()=>{
 const request=parseElementRequest('take an element x satisfying $R(x)$ from he');
 const facts=new Map([['he','∃ y : Nat, P y']]);
 assert.equal(elementInterpretationCandidates(request,{goal:'Q',scope:['he'],facts}).status,'no-supported-match');
 assert.equal(elementInterpretationCandidates(request,{goal:'Q',scope:[],facts}).status,'needs-context');
 const many=Array.from({length:9},(_,index)=>'h'+index);
 const manyFacts=new Map(many.map(name=>[name,'∃ y : Nat, P y']));
 const unscoped=parseElementRequest('take an element x satisfying $P(x)$');
 assert.equal(elementInterpretationCandidates(unscoped,{goal:null,scope:many,facts:manyFacts,limit:8}).status,'budget-exhausted');
});

test('an element-operation choice survives unrelated text edits after selection',()=>{
 const session=createDraftSession(),goal='Nat → P',scope=['P','he'];
 const facts=new Map([['P','Prop'],['he','∃ y : Nat, P']]);
 const original='take an element z : $Nat$ satisfying $P$\nunsupported ⊛';
 const first=session.evaluate(original,scope,facts,{goal});
 const candidate=first.rows[0].candidates.find(value=>value.operation==='universal-introduction');
 assert.ok(candidate);
 const choices=new Map([[1,candidate.choice]]);
 const selected=session.evaluate(original,scope,facts,{goal,choices});
 assert.equal(selected.rows[0].step.kind,'introduce');
 const previous=reconcileDraftIdentity(null,selected.graph);
 const edited='take an element z : $Nat$ satisfying $P$\nchanged unsupported ⊛';
 const probe=session.evaluate(edited,scope,facts,{goal});
 const current=reconcileDraftIdentity(previous,probe.graph);
 assert.deepEqual([...migrateDraftChoices(previous,current,choices)],[[1,candidate.choice]]);
});

test('an element choice keeps its root identity when a later scoped block extends the draft',()=>{
 const session=createDraftSession(),goal='∀ x : Nat, P x',scope=['hall','he','h'];
 const facts=new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y'],['h','True ∨ True']]);
 const initial='take an element x : $Nat$ satisfying $P(x)$\\nunsupported ⊛';
 const first=session.evaluate(initial,scope,facts,{goal});
 const candidate=first.rows[0].candidates.find(value=>value.operation==='universal-introduction');
 assert.ok(candidate);
 const choice=candidate.choice,choices=new Map([[1,choice]]);
 const selected=session.evaluate(initial,scope,facts,{goal,choices});
 const previous=reconcileDraftIdentity(null,selected.graph);
 const expanded=initial.replace('unsupported ⊛',
  'cases h, establish hT : $True$\\n  left case ht\\n    $True$ | ht\\n  right case hu\\n    $True$ | hu\\n$True$ | hT');
 const probe=session.evaluate(expanded,scope,facts,{goal});
 assert.equal(probe.graph.goal,goal,'the full draft graph is anchored to the originally selected target');
 assert.deepEqual(probe.graph.nodes.filter(node=>node.kind==='context').map(node=>node.name),scope,
  'suffix locals remain proof nodes instead of becoming root context entries');
 const current=reconcileDraftIdentity(previous,probe.graph);
 const migrated=migrateDraftChoices(previous,current,choices);
 assert.deepEqual([...migrated],[[1,choice]]);
 const restored=session.evaluate(expanded,scope,facts,{goal,choices:migrated});
 assert.equal(restored.rows[0].step.kind,'introduce');
 assert.equal(restored.rows[0].selectedChoice,choice);
 const cold=compileNaturalDraft(expanded,scope,facts,{goal,choices:migrated});
 const {reusedRows,...actual}=restored,{reusedRows:coldReuse,...expected}=cold;
 assert.equal(coldReuse,0);
 assert.deepEqual(actual,expected);
});
test('stale operation choices are rejected after context edits',()=>{
 const session=createDraftSession();
 const input='take an element x satisfying $P(x)$ from he\n$Q$ | hq';
 const facts=new Map([['he','∃ y : Nat, P y'],['hq','Q']]);
 const initial=session.evaluate(input,['he','hq'],facts,{goal:'Q'});
 const choice=initial.rows[0].candidates[0].choice;
 const changed=session.evaluate(input,['he','hq'],new Map([['he','∃ y : Int, P y'],['hq','Q']]),
  {goal:'Q',choices:new Map([[1,choice]])});
 assert.equal(changed.rows[0].resolutionStatus,'incompatible-choice');
});

test('a newly visible witness invalidates old operation domains and matches a cold rebuild',()=>{
 const session=createDraftSession(),input='take an element x satisfying $P(x)$';
 const goal='∀ x : Nat, P x',beforeFacts=new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]);
 session.evaluate(input,['hall','he'],beforeFacts,{goal,continuation:true});
 const scope=['hall','he','he2'],facts=new Map([...beforeFacts,['he2','∃ z : Nat, P z']]);
 const incremental=session.evaluate(input,scope,facts,{goal,continuation:true});
 const cold=draftProof(input,scope,facts,{goal,continuation:true,scopeIds:scope.map((_,index)=>'context:'+index)});
 assert.equal(incremental.reusedRows,0,'the context change invalidates the whole operation candidate domain');
 assert.equal(incremental.rows[0].candidates.length,3);
 const {reusedRows,...actual}=incremental,{reusedRows:coldReuse,...expected}=cold;
 assert.equal(coldReuse,0);
 assert.deepEqual(actual,expected);
});
