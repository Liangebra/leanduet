import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession} from '../web/natural-draft.mjs';
const facts=new Map([['h','P ∧ Q'],['f','P → R'],['g','Q → R']]);
const scope=[...facts.keys()];
const prefix='建立 hp : $?$,由 h\n';
test('later explicit inference narrows an earlier unknown proposition',()=>{
 const r=draftProof(prefix+'由 hp 与 f 得到 $R$',scope,facts);
 assert.equal(r.complete,true);
 assert.equal(r.rows[0].step.type,'P');
 assert.equal(r.rows[0].step.application,'And.left h');
 assert.equal(r.rows[0].domain.length,2);
 assert.equal(r.rows[1].step.application,'f hp');
 assert.equal(r.graph.nodes.at(-2).typeDomain.length,2);
});
test('ambiguity is not erased in the absence of a distinguishing constraint',()=>{
 const r=draftProof(prefix+'$R$',scope,facts);
 assert.equal(r.complete,false);
 assert.equal(r.rows[0].step,undefined);
 assert.equal(r.rows[0].candidates.length,2);
 const selected=draftProof(prefix+'$R$',scope,facts,{choices:new Map([[1,'And.right h']])});
 assert.equal(selected.rows[0].step.type,'Q');
});
test('incompatible later constraints do not silently choose a proposition',()=>{
 const r=draftProof(prefix+'由 hp 与 f 得到 $R$\n由 hp 与 g 得到 $R$',scope,facts);
 assert.equal(r.complete,false);
 assert.equal(r.rows[0].domain.length,2);
 assert.equal(r.rows[0].candidates.length,0);
 assert.match(r.rows[0].reason,/No joint/);
});
test('unsupported downstream schemas cannot eliminate all candidates',()=>{
 const r=draftProof(prefix+'由 hp 与 f 得到 $Z$',scope,facts);
 assert.equal(r.complete,false);
 assert.equal(r.rows[0].candidates.length,2);
 assert.equal(r.rows[0].constraints[0].status,'unsupported');
});
test('a downstream edit invalidates the earlier inferred type',()=>{
 const s=createDraftSession();
 const a=prefix+'由 hp 与 f 得到 $R$',b=prefix+'由 hp 与 g 得到 $R$';
 assert.equal(s.evaluate(a,scope,facts).rows[0].step.type,'P');
 const r=s.evaluate(b,scope,facts);
 assert.equal(r.reusedRows,0);assert.equal(r.rows[0].step.type,'Q');
 assert.deepEqual(r.rows,draftProof(b,scope,facts).rows);
});
