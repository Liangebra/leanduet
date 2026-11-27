import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {compileNaturalDraft,createDraftSession} from '../web/natural-draft.mjs';

const cases=JSON.parse(readFileSync(new URL('./fixtures/mathlib-cases.json',import.meta.url),'utf8'));
const example=cases.find(item=>item.id==='linear-map-additivity');
const scope=example.scope;
const context=new Map(Object.entries(example.context));

test('linear-map prose candidate and local edit agree with full recomputation',()=>{
 const session=createDraftSession();
 const original=session.evaluate(example.naturalDraft,scope,context,{goal:example.goal});
 assert.equal(original.complete,true);
 assert.equal(original.steps.at(-1).application,example.expectedStructure[0].application);
 const edited=session.evaluate(example.editedNaturalDraft,scope,context,{goal:example.editedGoal});
 const cold=compileNaturalDraft(example.editedNaturalDraft,scope,context,{goal:example.editedGoal});
 const stripReuse=({reusedRows,...result})=>result;
 assert.deepEqual(stripReuse(edited),stripReuse(cold));
 assert.equal(edited.complete,true);
 assert.equal(edited.steps.at(-1).application,example.editedExpectedStructure[0].application);
});
