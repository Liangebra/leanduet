import test from 'node:test';
import assert from 'node:assert/strict';
import {compileNaturalDraft,createDraftSession,draftProof} from '../web/natural-draft.mjs';
import {existentialBindings,planGoalOperation} from '../web/context-extension.mjs';
import {elementInterpretationCandidates,parseElementRequest} from '../web/element-interpretation.mjs';

test('English and Chinese restricted element requests preserve the set and the object type',()=>{
 const english=parseElementRequest('take an arbitrary element x : $Nat$ in A satisfying $P(x)$');
 const chinese=parseElementRequest('取任意元素 x：$Nat$ ∈ A 满足 $P(x)$');
 for(const request of [english,chinese]){
  assert.equal(request.name,'x');
  assert.equal(request.type,'Nat');
  assert.equal(request.restriction,'A');
  assert.equal(request.property,'(P x)');
  assert.equal(request.arbitrary,true);
 }
});

test('a bounded universal goal introduces x and leaves membership as a separate obligation',()=>{
 const request=parseElementRequest('take an arbitrary element x : $Nat$ in A satisfying $P(x)$');
 const result=elementInterpretationCandidates(request,{goal:'∀ x ∈ A, P x',scope:['A'],facts:new Map([['A','Set Nat']])});
 assert.equal(result.status,'unique');
 assert.equal(result.candidates[0].operation,'universal-introduction');
 assert.equal(result.candidates[0].requiredCondition,'(x ∈ A)');
 const plan=planGoalOperation('∀ x ∈ A, P x',{kind:'introduce',name:'x',type:'Nat'});
 assert.equal(plan.subgoals[0].goal,'((x ∈ A) → (P x))');
 assert.deepEqual(plan.subgoals[0].contextDelta,[{name:'x',type:'Nat',kind:'universal-variable'}]);
});

test('bounded introductions require a type and reject a type conflicting with a known set carrier',()=>{
 const missing=parseElementRequest('take an arbitrary element x in A satisfying $P(x)$');
 assert.equal(elementInterpretationCandidates(missing,{goal:'∀ x ∈ A, P x',scope:['A'],facts:new Map([['A','Set Nat']])}).status,'needs-type-annotation');
 const mismatched=parseElementRequest('take an arbitrary element x : $Int$ in A satisfying $P(x)$');
 const result=elementInterpretationCandidates(mismatched,{goal:'∀ x ∈ A, P x',scope:['A'],facts:new Map([['A','Set Nat']])});
 assert.equal(result.status,'incompatible-type');
 assert.equal(result.expectedType,'Nat');
 assert.equal(result.candidates.length,0);
});

test('bounded and unbounded requests are not silently interchanged',()=>{
 const unbounded=parseElementRequest('take an element x satisfying $P(x)$');
 const boundedContext={goal:'∀ x ∈ A, P x',scope:['A','h'],
  facts:new Map([['A','Set Nat'],['h','∃ y ∈ A, P y']])};
 assert.equal(elementInterpretationCandidates(unbounded,boundedContext).status,'no-supported-match');
 const wrongSet=parseElementRequest('take an element x : $Nat$ in B satisfying $P(x)$ from h');
 assert.equal(elementInterpretationCandidates(wrongSet,{...boundedContext,goal:'Q'}).status,'no-supported-match');
 const wrongCarrier=parseElementRequest('take an element x : $Int$ in A satisfying $P(x)$ from h');
 assert.equal(elementInterpretationCandidates(wrongCarrier,{...boundedContext,goal:'Q'}).status,'incompatible-type');
});

test('a bounded existential yields membership and predicate evidence, tied to its source identity',()=>{
 const request=parseElementRequest('take an element x : $Nat$ in A satisfying $P(x)$ from h');
 const result=elementInterpretationCandidates(request,{goal:'Q',scope:['A','h'],scopeIds:['context:A','branch:h'],
  facts:new Map([['A','Set Nat'],['h','∃ y ∈ A, P y']])});
 assert.equal(result.status,'unique');
 assert.equal(result.candidates[0].operation,'existential-elimination');
 assert.equal(result.candidates[0].sourceId,'branch:h');
 assert.equal(result.candidates[0].evidenceType,'((x ∈ A) ∧ (P x))');
 assert.equal(existentialBindings('∃ y ∈ A, P y',{name:'x',type:'Nat'}).propertyType,'(P x)');
 assert.throws(()=>existentialBindings('∃ y ∈ A, P y',{name:'x'}),/explicit witness type/);
});

test('element renaming cannot capture a set expression in a bounded quantifier',()=>{
 assert.throws(()=>planGoalOperation('∀ x ∈ s, P x',{kind:'introduce',name:'s',type:'Nat'}),/capture/);
 assert.throws(()=>existentialBindings('∃ x ∈ s, P x',{name:'s',type:'Nat'}),/capture/);
});

test('the restricted introduction consumes membership before proving the property',()=>{
 const facts=new Map([['A','Set Nat'],['hall','∀ x : Nat, x ∈ A → P x']]);
 const input='take an arbitrary element x : $Nat$ in A satisfying $P(x)$\n'+
  'assume hx : $x ∈ A$\n$P(x)$ | hall x hx';
 const result=compileNaturalDraft(input,['A','hall'],facts,{goal:'∀ x ∈ A, P x'});
 assert.equal(result.complete,true);
 assert.match(result.term,/intro x[\s\S]*intro hx[\s\S]*exact hall x hx/);
 assert.equal(result.rows[0].remainingGoal,'((x ∈ A) → (P x))');
});

test('bounded existential extraction keeps witness evidence local and source identity stable',()=>{
 const facts=new Map([['A','Set Nat'],['h','∃ x ∈ A, P x'],['hq','Q']]);
 const input='take an element x : $Nat$ in A satisfying $P(x)$\n$Q$ | hq';
 const first=compileNaturalDraft(input,['A','h','hq'],facts,{goal:'Q'});
 assert.equal(first.complete,true);
 assert.equal(first.rows[0].step.evidenceType,'((x ∈ A) ∧ (P x))');
 assert.match(first.term,/rcases duet_exists_x with ⟨x, h_x⟩[\s\S]*exact hq/);
 const session=createDraftSession();
 session.evaluate(input,['A','h','hq'],facts,{goal:'Q'});
 const changedFacts=new Map([...facts,['h2','∃ x ∈ A, P x']]);
 const expandedScope=['A','h','hq','h2'];
 const incremental=session.evaluate(input,expandedScope,changedFacts,{goal:'Q'});
 const cold=draftProof(input,expandedScope,changedFacts,{goal:'Q',scopeIds:expandedScope.map((_,index)=>'context:'+index)});
 assert.equal(incremental.reusedRows,0,'a newly visible bounded existential invalidates the candidate domain');
 assert.equal(incremental.rows[0].resolutionStatus,'ambiguous');
 assert.equal(incremental.rows[0].candidates.length,2);
 const {reusedRows,...actual}=incremental,{reusedRows:coldReuse,...expected}=cold;
 assert.equal(coldReuse,0);
 assert.deepEqual(actual,expected);
});

