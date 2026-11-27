import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {compileNaturalDraft} from '../web/natural-draft.mjs';

const cases=JSON.parse(readFileSync(new URL('./fixtures/real-math-cases.json',import.meta.url),'utf8'));
const mathlibCases=JSON.parse(readFileSync(new URL('./fixtures/mathlib-cases.json',import.meta.url),'utf8'));

test('aligned real-math fixtures preserve set operations and proof structure',()=>{
 assert.equal(cases.length,2);
 for(const example of cases){
  const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
  assert.equal(result.complete,true,example.id);
  assert.equal(result.rows.at(-1).type,example.expectedLastType,example.id);
  assert.deepEqual(result.steps.map(step=>step.kind),example.expectedStepKinds,example.id);
  assert.ok(result.term.includes(example.focusCandidate),example.id);
  assert.ok(result.rows.every(row=>row.proofStatus==='candidate'),example.id);
  assert.equal(result.rows.at(-1).proofStatus,'candidate','structural candidacy is not a Lean verification result');
 }
});

test('compact image preserves an explicitly named Mathlib rule and premises',()=>{
 const facts=new Map([['hs','IsCompact s'],['hf','Continuous f']]);
 const input=String.raw`因此 $IsCompact (f '' s)$，由紧集的连续像，使用 hs 和 hf`;
 const result=compileNaturalDraft(input,['f','s','hs','hf'],facts,{goal:"IsCompact (f '' s)"});
 assert.equal(result.complete,true);
 assert.equal(result.rows.at(-1).proofStatus,'candidate');
 assert.match(result.term,/IsCompact\.image hs hf/);
 assert.throws(()=>compileNaturalDraft(input,['f','s','hs'],new Map([['hs','IsCompact s']]),{goal:"IsCompact (f '' s)"}),
  'continuity is a required premise; the draft must not invent or omit hf');
});

test('Mathlib corpus seed matches the existing structural candidate',()=>{
 for(const id of ['compact-image-continuous','subgroup-multiplication-closure','linear-map-additivity'])
  assert.ok(mathlibCases.some(example=>example.id===id),`missing Mathlib fixture: ${id}`);
 for(const example of mathlibCases){
  const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
  assert.equal(result.complete,true,example.id);
  assert.deepEqual(result.steps.map(step=>({kind:step.kind,claim:step.type,application:step.application})),example.expectedStructure,example.id);
  assert.equal(result.rows.at(-1).proofStatus,'candidate',example.id);
  assert.match(example.alignmentStatus,/draft correspondence/);
 }
});

test('the subgroup fixture keeps its cited rule and both membership premises',()=>{
 const example=mathlibCases.find(value=>value.id==='subgroup-multiplication-closure');
 const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
 assert.equal(result.complete,true);
 assert.deepEqual(result.steps.map(step=>step.application),['Subgroup.mul_mem H hx hy']);
 const node=result.graph.nodes.find(value=>value.kind==='conclude');
 assert.ok(node.formula.refs.includes('context:1'),'the conclusion depends on the subgroup object');
 assert.ok(node.dependencies.includes('context:4'),'the proof cites the first membership fact');
 assert.ok(node.dependencies.includes('context:5'),'the proof cites the second membership fact');
 assert.match(example.alignmentStatus,/explicit rule and premises are checked/);
});

test('compact-image local lemma returns only its stated proposition',()=>{
 const example=mathlibCases[0];
 const result=compileNaturalDraft(example.localLemmaDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
 assert.equal(result.complete,true);
 assert.deepEqual(result.steps.map(step=>step.kind),['local-lemma','conclude']);
 assert.equal(result.steps[0].subgoals[0].goal,'(IsCompact (f \'\' s))');
 assert.match(result.term,/have himage : \(IsCompact \(f '' s\)\) := by[\s\S]*exact IsCompact\.image hs hf[\s\S]*exact himage/);
 assert.equal(result.rows[0].proofStatus,'candidate');
 assert.equal(result.rows.at(-1).proofStatus,'candidate');
});
