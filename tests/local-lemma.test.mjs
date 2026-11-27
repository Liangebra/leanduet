import test from 'node:test';
import assert from 'node:assert/strict';
import {compileNaturalDraft,createDraftSession} from '../web/natural-draft.mjs';
import {localLemmaHeader} from '../web/proof-subgoals.mjs';
import {reconcileDraftIdentity} from '../web/draft-identity.mjs';

test('a local lemma proves a child goal and returns only its proposition to the parent',()=>{
 const input=['local lemma hq : $Q$','  proof','    $Q$ | hq0','$R$ | gr hq'].join('\n');
 const result=compileNaturalDraft(input,['hq0','gr'],new Map([['hq0','Q'],['gr','Q → R']]),{goal:'R'});
 assert.equal(localLemmaHeader('local lemma hq : $Q$').kind,'local-lemma');
 assert.equal(localLemmaHeader('局部引理 hq：\\(Q\\)').type,'Q');
 assert.equal(result.complete,true);
 assert.deepEqual(result.steps.map(step=>step.kind),['local-lemma','conclude']);
 assert.match(result.term,/have hq : Q := by\n    show Q\n    exact hq0[\s\S]*exact gr hq/);
 const lemma=result.graph.nodes.find(node=>node.kind==='local-lemma');
 assert.ok(lemma.dependencies.includes('context:0'));
 assert.deepEqual(lemma.subgoals.map(goal=>goal.status),['complete']);
 assert.equal(result.graph.nodes.at(-1).dependencies.includes(lemma.id),true);
});

test('a local proof declaration expires when its child scope closes',()=>{
 const input=['local lemma id : $P → P$','  proof','    assume hp : $P$','    $P$ | hp','$P$ | hp'].join('\n');
 const result=createDraftSession().evaluate(input,[],new Map(),{goal:'P'});
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 assert.ok(result.rows.some(row=>row.raw==='$P$ | hp'&&row.status==='unresolved'),JSON.stringify(result.rows.map(row=>({raw:row.raw,status:row.status,reason:row.reason}))));
 const child=result.graph.nodes.find(node=>node.kind==='local-lemma').subgoals[0].graph;
 assert.ok(child.nodes.some(node=>node.name==='hp'));
 assert.ok(!result.graph.nodes.some(node=>node.name==='hp'),'the child binder is not returned to the parent graph');
});

test('an unfinished local lemma keeps a typed open dependency and later context',()=>{
 const input=['local lemma hq : $Q$','  proof','    unsupported sentence','$R$ | gr hq'].join('\n');
 const result=createDraftSession().evaluate(input,['gr'],new Map([['gr','Q → R']]),{goal:'R'});
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
 assert.equal(result.rows[0].resolutionStatus,'open-obligation');
 assert.equal(result.rows.at(-1).proofStatus,'depends-on-open');
 assert.deepEqual(result.openBindings,['hq']);
});

test('a renderable proof hole inside a local lemma is not exported as complete',()=>{
 const input=['local lemma hq : $Q
 const input=['local lemma hP : $P$','  proof','    $P$ | hp','$Q$ | g hP'].join('\n');
 const result=createDraftSession().evaluate(input,['hp','g'],new Map([['hp','P'],['g','P → Q']]),{goal:'Q',openBindings:['hp']});
 assert.equal(result.complete,true);
 assert.equal(result.rows.find(row=>row.kind==='local-lemma').proofStatus,'depends-on-open');
 assert.equal(result.rows.at(-1).proofStatus,'depends-on-open');
 assert.ok(result.openBindings.includes('hP'));
 assert.match(result.term,/exact g hP/);
});

test('a child goal can remain empty while its claim and parent continuation stay visible',()=>{
 const input=['local lemma hq : $Q$','  proof','$R$ | gr hq'].join('\n');
 const result=createDraftSession().evaluate(input,['gr'],new Map([['gr','Q → R']]),{goal:'R'});
 assert.equal(result.complete,false);
 assert.equal(result.rows[0].kind,'local-lemma');
 assert.equal(result.rows.at(-1).raw,'$R$ | gr hq');
 assert.equal(result.rows.at(-1).proofStatus,'depends-on-open');
});

test('local lemma children stay isolated inside each disjunction branch',()=>{
 const input=[
  'cases h, establish hR : $R$',
  '  left case hq0',
  '    local lemma hq : $Q$',
  '      proof',
  '        $Q$ | hq0',
  '    $R$ | f hq',
  '  right case ht',
  '    $R$ | g ht',
  '$R$ | hR'
 ].join('\n');
 const facts=new Map([['h','Q ∨ T'],['f','Q → R'],['g','T → R']]);
 const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'R'});
 assert.equal(result.complete,true);
 assert.match(result.term,/cases h with[\s\S]*have hq : Q := by[\s\S]*exact f hq[\s\S]*exact g ht/);
 const branches=result.graph.nodes.find(node=>node.kind==='cases').branches;
 assert.ok(branches[0].graph.nodes.some(node=>node.kind==='local-lemma'));
 assert.ok(!branches[1].graph.nodes.some(node=>node.name==='hq'));
});

test('a lemma name from one branch cannot resolve in its sibling',()=>{
 const input=[
  'cases h, establish hR : $R$',
  '  left case hq0',
  '    local lemma hq : $Q$',
  '      proof',
  '        $Q$ | hq0',
  '    $R$ | f hq',
  '  right case ht',
  '    $R$ | f hq',
  '$R$ | hR'
 ].join('\n');
 const facts=new Map([['h','Q ∨ T'],['f','Q → R']]);
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'R'});
 const branches=result.graph.nodes.find(node=>node.kind==='cases').branches;
 assert.equal(branches[0].status,'complete');
 assert.equal(branches[1].status,'open');
 assert.ok(result.rows.some(row=>row.raw==='$R$ | f hq'&&row.status==='unresolved'));
});

test('ordinary context and sequential local lemmas remain visible in source order',()=>{
 const input=[
  '$Q$ | hq',
  'local lemma localQ : $Q$',
  '  proof',
  '    $Q$ | hq',
  'local lemma localR : $R$',
  '  proof',
  '    $R$ | gr localQ',
  '$R$ | localR'
 ].join('\n');
 const result=compileNaturalDraft(input,['hq','gr'],new Map([['hq','Q'],['gr','Q → R']]),{goal:'R'});
 assert.equal(result.complete,true);
 assert.deepEqual(result.steps.map(step=>step.kind),['establish','local-lemma','local-lemma','conclude']);
 assert.deepEqual(result.rows.map(row=>row.line),[1,2,4,5,7,8]);
 assert.match(result.term,/have localQ : Q := by[\s\S]*exact hq[\s\S]*have localR : R[\s\S]*exact localR/);
});

test('a local lemma cannot shadow its parent or refer to itself in its type',()=>{
 const duplicate=['local lemma hq : $Q$','  proof','    $Q$ | hq0','$R$ | gr hq'].join('\n');
 assert.throws(()=>compileNaturalDraft(duplicate,['hq','hq0','gr'],new Map([['hq','Q'],['hq0','Q'],['gr','Q → R']]),{goal:'R'}),/must be fresh/);
 const self=['local lemma hq : $P(hq)$','  proof','    $P(hq)$ | h','$P(hq)$ | h'].join('\n');
 assert.throws(()=>compileNaturalDraft(self,['h'],new Map([['h','P hq']]),{goal:'P hq'}),/cannot refer to the name it is introducing/);
});

test('editing a lemma proof matches a cold rebuild and keeps occurrence identity',()=>{
 const source=['local lemma hq : $Q$','  proof','    $Q$ | hq0','$R$ | gr hq'].join('\n');
 const edited='\n'+source.replace('$Q$ | hq0','clearly $Q$ | hq0');
 const context=new Map([['hq0','Q'],['gr','Q → R']]);
 const session=createDraftSession();
 const initial=session.evaluate(source,['hq0','gr'],context,{goal:'R'});
 const previous=reconcileDraftIdentity(null,initial.graph);
 const incremental=session.evaluate(edited,['hq0','gr'],context,{goal:'R'});
 const cold=compileNaturalDraft(edited,['hq0','gr'],context,{goal:'R'});
 const current=reconcileDraftIdentity(previous,incremental.graph);
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.steps,cold.steps);
 assert.deepEqual(incremental.graph,cold.graph);
 assert.equal(incremental.term,cold.term);
 assert.equal(incremental.rows.find(row=>row.kind==='local-lemma').line,2);
 assert.equal(incremental.rows.find(row=>row.raw==='clearly $Q$ | hq0').line,4);
 const oldLemma=previous.graph.nodes.find(node=>node.kind==='local-lemma');
 const newLemma=current.graph.nodes.find(node=>node.kind==='local-lemma');
 assert.equal(previous.ids.get(oldLemma.id),current.ids.get(newLemma.id));
});
,'  proof','    $Q$ | ?','$R$ | gr hq'].join('\\n');
 const result=createDraftSession().evaluate(input,['gr'],new Map([['gr','Q → R']]),{goal:'R'});
 const lemma=result.rows.find(row=>row.kind==='local-lemma');
 const child=result.rows.find(row=>row.raw==='$Q$ | ?');
 assert.equal(lemma.proofStatus,'open');
 assert.equal(lemma.resolutionStatus,'open-obligation');
 assert.equal(child.status,'translated','the syntax can render even though the proof step remains open');
 assert.equal(child.proofStatus,'open');
 assert.equal(result.rows.at(-1).proofStatus,'depends-on-open');
 assert.equal(result.complete,false);
 assert.equal(result.term,null);
});

test('a completed local lemma propagates dependencies on open parent facts',()=>{
 const input=['local lemma hP : $P$','  proof','    $P$ | hp','$Q$ | g hP'].join('\n');
 const result=createDraftSession().evaluate(input,['hp','g'],new Map([['hp','P'],['g','P → Q']]),{goal:'Q',openBindings:['hp']});
 assert.equal(result.complete,true);
 assert.equal(result.rows.find(row=>row.kind==='local-lemma').proofStatus,'depends-on-open');
 assert.equal(result.rows.at(-1).proofStatus,'depends-on-open');
 assert.ok(result.openBindings.includes('hP'));
 assert.match(result.term,/exact g hP/);
});

test('a child goal can remain empty while its claim and parent continuation stay visible',()=>{
 const input=['local lemma hq : $Q$','  proof','$R$ | gr hq'].join('\n');
 const result=createDraftSession().evaluate(input,['gr'],new Map([['gr','Q → R']]),{goal:'R'});
 assert.equal(result.complete,false);
 assert.equal(result.rows[0].kind,'local-lemma');
 assert.equal(result.rows.at(-1).raw,'$R$ | gr hq');
 assert.equal(result.rows.at(-1).proofStatus,'depends-on-open');
});

test('local lemma children stay isolated inside each disjunction branch',()=>{
 const input=[
  'cases h, establish hR : $R$',
  '  left case hq0',
  '    local lemma hq : $Q$',
  '      proof',
  '        $Q$ | hq0',
  '    $R$ | f hq',
  '  right case ht',
  '    $R$ | g ht',
  '$R$ | hR'
 ].join('\n');
 const facts=new Map([['h','Q ∨ T'],['f','Q → R'],['g','T → R']]);
 const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'R'});
 assert.equal(result.complete,true);
 assert.match(result.term,/cases h with[\s\S]*have hq : Q := by[\s\S]*exact f hq[\s\S]*exact g ht/);
 const branches=result.graph.nodes.find(node=>node.kind==='cases').branches;
 assert.ok(branches[0].graph.nodes.some(node=>node.kind==='local-lemma'));
 assert.ok(!branches[1].graph.nodes.some(node=>node.name==='hq'));
});

test('a lemma name from one branch cannot resolve in its sibling',()=>{
 const input=[
  'cases h, establish hR : $R$',
  '  left case hq0',
  '    local lemma hq : $Q$',
  '      proof',
  '        $Q$ | hq0',
  '    $R$ | f hq',
  '  right case ht',
  '    $R$ | f hq',
  '$R$ | hR'
 ].join('\n');
 const facts=new Map([['h','Q ∨ T'],['f','Q → R']]);
 const result=createDraftSession().evaluate(input,[...facts.keys()],facts,{goal:'R'});
 const branches=result.graph.nodes.find(node=>node.kind==='cases').branches;
 assert.equal(branches[0].status,'complete');
 assert.equal(branches[1].status,'open');
 assert.ok(result.rows.some(row=>row.raw==='$R$ | f hq'&&row.status==='unresolved'));
});

test('ordinary context and sequential local lemmas remain visible in source order',()=>{
 const input=[
  '$Q$ | hq',
  'local lemma localQ : $Q$',
  '  proof',
  '    $Q$ | hq',
  'local lemma localR : $R$',
  '  proof',
  '    $R$ | gr localQ',
  '$R$ | localR'
 ].join('\n');
 const result=compileNaturalDraft(input,['hq','gr'],new Map([['hq','Q'],['gr','Q → R']]),{goal:'R'});
 assert.equal(result.complete,true);
 assert.deepEqual(result.steps.map(step=>step.kind),['establish','local-lemma','local-lemma','conclude']);
 assert.deepEqual(result.rows.map(row=>row.line),[1,2,4,5,7,8]);
 assert.match(result.term,/have localQ : Q := by[\s\S]*exact hq[\s\S]*have localR : R[\s\S]*exact localR/);
});

test('a local lemma cannot shadow its parent or refer to itself in its type',()=>{
 const duplicate=['local lemma hq : $Q$','  proof','    $Q$ | hq0','$R$ | gr hq'].join('\n');
 assert.throws(()=>compileNaturalDraft(duplicate,['hq','hq0','gr'],new Map([['hq','Q'],['hq0','Q'],['gr','Q → R']]),{goal:'R'}),/must be fresh/);
 const self=['local lemma hq : $P(hq)$','  proof','    $P(hq)$ | h','$P(hq)$ | h'].join('\n');
 assert.throws(()=>compileNaturalDraft(self,['h'],new Map([['h','P hq']]),{goal:'P hq'}),/cannot refer to the name it is introducing/);
});

test('editing a lemma proof matches a cold rebuild and keeps occurrence identity',()=>{
 const source=['local lemma hq : $Q$','  proof','    $Q$ | hq0','$R$ | gr hq'].join('\n');
 const edited='\n'+source.replace('$Q$ | hq0','clearly $Q$ | hq0');
 const context=new Map([['hq0','Q'],['gr','Q → R']]);
 const session=createDraftSession();
 const initial=session.evaluate(source,['hq0','gr'],context,{goal:'R'});
 const previous=reconcileDraftIdentity(null,initial.graph);
 const incremental=session.evaluate(edited,['hq0','gr'],context,{goal:'R'});
 const cold=compileNaturalDraft(edited,['hq0','gr'],context,{goal:'R'});
 const current=reconcileDraftIdentity(previous,incremental.graph);
 assert.deepEqual(incremental.rows,cold.rows);
 assert.deepEqual(incremental.steps,cold.steps);
 assert.deepEqual(incremental.graph,cold.graph);
 assert.equal(incremental.term,cold.term);
 assert.equal(incremental.rows.find(row=>row.kind==='local-lemma').line,2);
 assert.equal(incremental.rows.find(row=>row.raw==='clearly $Q$ | hq0').line,4);
 const oldLemma=previous.graph.nodes.find(node=>node.kind==='local-lemma');
 const newLemma=current.graph.nodes.find(node=>node.kind==='local-lemma');
 assert.equal(previous.ids.get(oldLemma.id),current.ids.get(newLemma.id));
});
