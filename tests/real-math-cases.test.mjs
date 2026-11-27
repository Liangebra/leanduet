import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {compileNaturalDraft} from '../web/natural-draft.mjs';

const cases=JSON.parse(readFileSync(new URL('./fixtures/real-math-cases.json',import.meta.url),'utf8'));

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
