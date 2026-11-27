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

test('a binary relation constrains two unknown propositions jointly',()=>{
 const ctx=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)']]);
 const text='建立 hp : $?$,由 h\n建立 hf : $?$,由 k\n由 hp 与 hf 得到 $R$';
 const r=draftProof(text,[...ctx.keys()],ctx);
 assert.equal(r.complete,false);
 const group=r.graph.constraintGroups[0];
 assert.deepEqual(group.variables.map(v=>v.name),['hp','hf']);
 assert.deepEqual(group.assignments,[['And.left h','And.left k'],['And.right h','And.right k']]);
 assert.equal(r.rows[0].candidates.length,2);assert.equal(r.rows[1].candidates.length,2);
 const chosen=draftProof(text,[...ctx.keys()],ctx,{choices:new Map([[2,'And.right k']])});
 assert.equal(chosen.complete,true);
 assert.equal(chosen.rows[0].step.application,'And.right h');
 assert.equal(chosen.rows[1].step.application,'And.right k');
 assert.equal(chosen.rows[2].step.application,'hf hp');
 const conflict=draftProof(text,[...ctx.keys()],ctx,{choices:new Map([[1,'And.left h'],[2,'And.right k']])});
 assert.equal(conflict.complete,false);
 assert.equal(conflict.graph.constraintGroups[0].status,'contradiction');
});
test('an additional unary constraint selects the entire correlated component',()=>{
 const ctx=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)'],['g','P → S']]);
 const text='建立 hp : $?$,由 h\n建立 hf : $?$,由 k\n由 hp 与 hf 得到 $R$\n由 hp 与 g 得到 $S$';
 const r=draftProof(text,[...ctx.keys()],ctx);
 assert.equal(r.complete,true);
 assert.equal(r.rows[0].step.application,'And.left h');assert.equal(r.rows[1].step.application,'And.left k');
 assert.deepEqual(r.graph.constraintGroups[0].assignments,[['And.left h','And.left k']]);
});
test('future holes cannot constrain a relation before their introduction',()=>{
 const ctx=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)']]);
 const r=draftProof('建立 hp : $?$,由 h\n由 hp 与 hf 得到 $R$\n建立 hf : $?$,由 k\n$R$',[...ctx.keys()],ctx);
 assert.equal(r.complete,false);
 assert.equal(r.graph.constraintGroups.length,2);
 assert.equal(r.rows[0].candidates.length,2);
});
test('a backward constraint edit invalidates every correlated hole',async()=>{
 const {dependentNodes}=await import('../web/draft-graph.mjs');
 const ctx=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)']]);
 const r=draftProof('建立 hp : $?$,由 h\n建立 hf : $?$,由 k\n由 hp 与 hf 得到 $R$',[...ctx.keys()],ctx);
 assert.deepEqual(dependentNodes(r.graph,['line:3']),['line:1','line:2','line:3']);
});
test('finite relational search never treats truncated enumeration as a solution',async()=>{
 const {solveFiniteRelations}=await import('../web/proposition-constraints.mjs');
 const vars=Array.from({length:6},(_,i)=>({name:'v'+i,line:i+1,domain:[{term:'l'+i},{term:'r'+i}]}));
 const r=solveFiniteRelations(vars,[],new Map(),{limit:2});
 assert.equal(r.status,'overflow');assert.equal(r.assignments.length,0);
 assert.ok(r.candidates.every(c=>c.length===2));
});
test('a globally inconsistent cycle can have locally supported relations',async()=>{
 const {solveFiniteRelations}=await import('../web/proposition-constraints.mjs');
 const vars=['a','b','c'].map((name,i)=>({name,line:i+1,domain:[{term:'0'},{term:'1'}]}));
 const relations=[['a','b'],['b','c'],['a','c']].map((names,i)=>({names,status:'matched',tuples:i===2?[['0','1'],['1','0']]:[['0','0'],['1','1']]}));
 const r=solveFiniteRelations(vars,relations);
 assert.equal(r.status,'contradiction');assert.deepEqual(r.assignments,[]);
});

test('a later explicit choice migrates across harmless edits without losing correlation',async()=>{
 const {reconcileDraftIdentity,migrateDraftChoices}=await import('../web/draft-identity.mjs');
 const ctx=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)']]);
 const text='建立 hp : $?$,由 h\n建立 hf : $?$,由 k\n由 hp 与 hf 得到 $R$';
 const choices=new Map([[2,'And.right k']]);
 const old=reconcileDraftIdentity(null,draftProof(text,[...ctx.keys()],ctx,{choices}).graph);
 const next='\n'+text;
 const current=reconcileDraftIdentity(old,draftProof(next,[...ctx.keys()],ctx).graph);
 const migrated=migrateDraftChoices(old,current,choices);
 assert.deepEqual([...migrated],[[3,'And.right k']]);
 const r=draftProof(next,[...ctx.keys()],ctx,{choices:migrated});
 assert.equal(r.complete,true);
 assert.equal(r.rows[0].step.application,'And.right h');
});
test('a changed downstream choice invalidates earlier cached assignments',()=>{
 const ctx=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)']]);
 const text='建立 hp : $?$,由 h\n建立 hf : $?$,由 k\n由 hp 与 hf 得到 $R$';
 const s=createDraftSession(),scope=[...ctx.keys()];
 assert.equal(s.evaluate(text,scope,ctx,{choices:new Map([[2,'And.left k']])}).rows[0].step.type,'P');
 const r=s.evaluate(text,scope,ctx,{choices:new Map([[2,'And.right k']])});
 assert.equal(r.reusedRows,0);assert.equal(r.rows[0].step.type,'Q');
 assert.deepEqual(r.rows,draftProof(text,scope,ctx,{choices:new Map([[2,'And.right k']])}).rows);
});

test('known type survives unresolved proof alternatives without exporting a proof',()=>{
 const ctx=new Map([['h','P ∧ P'],['f','P → Q']]);
 const text='建立 hp : $?$,由 h\n由 hp 与 f 得到 $Q$';
 const r=draftProof(text,[...ctx.keys()],ctx);
 assert.equal(r.complete,false);
 assert.equal(r.term,null);
 assert.equal(r.rows[0].step.type,'P');
 assert.equal(r.rows[0].step.application,'?');
 assert.equal(r.rows[0].candidates.length,2);
 assert.equal(r.rows[0].proofStatus,'open');
 assert.equal(r.rows[1].step.application,'f hp');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 const resolved=draftProof(text,[...ctx.keys()],ctx,{choices:new Map([[1,'And.right h']])});
 assert.equal(resolved.complete,true);
 assert.equal(resolved.rows[0].step.application,'And.right h');
});
test('a typed open hole can provisionally supply a later projection source',()=>{
 const ctx=new Map([['h','(P ∧ Q) ∧ (P ∧ Q)'],['f','P → R']]);
 const text='建立 hpq : $?$,由 h\n建立 hp : $?$,由 hpq\n由 hp 与 f 得到 $R$';
 const r=draftProof(text,[...ctx.keys()],ctx);
 assert.equal(r.complete,false);
 assert.equal(r.rows[0].step.application,'?');
 assert.equal(r.rows[1].step.application,'And.left hpq');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.equal(r.rows[2].proofStatus,'depends-on-open');
});
