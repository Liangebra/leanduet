import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession} from '../web/natural-draft.mjs';
import {discourseFrame,discourseCandidates} from '../web/discourse.mjs';
const facts=new Map([['p','P'],['q','Q'],['f','P → R'],['g','Q → R']]);
const scope=[...facts.keys()];
test('the requested conclusion and explicit rule constrain an earlier referent',()=>{
 const r=draftProof('$P$ | p\n$Q$ | q\n由上述结论和 f 得到 $R$',scope,facts);
 assert.equal(r.complete,true);
 assert.equal(r.rows[2].step.application,'f duet_h1');
 assert.deepEqual(r.rows[2].candidates[0].referents,[['duet_h1'],['f']]);
});
test('two equally compatible earlier referents remain ambiguous',()=>{
 const r=draftProof('$P$ | p\n$P$ | p\n由上述结论与 f 得到 $R$',scope,facts);
 assert.equal(r.complete,false);
 assert.deepEqual(r.rows[2].candidates.map(c=>c.term),['f duet_h1','f duet_h2']);
});
test('previous and numbered result references respect source order',()=>{
 const r=draftProof('$P$ | p\n\n$Q$ | q\n由第1行与 f 得到 $R$',scope,facts);
 assert.equal(r.rows[2].step.application,'f duet_h1');
 assert.equal(draftProof('$P$ | p\n$Q$ | q\n由上一结论与 f 得到 $R$',scope,facts).complete,false);
 assert.equal(draftProof('$P$ | p\n$Q$ | q\n由前两步结论得到 $P ∧ Q$',scope,facts).rows[2].step.application,'And.intro duet_h1 duet_h2');
});
test('an earlier unresolved proof is still a tentative referent',()=>{
 const ctx=new Map([...facts,['h','P ∧ P']]);
 const r=draftProof('$P$ | from h\n由上一结论和 f 得到 $R$',[...ctx.keys()],ctx);
 assert.equal(r.rows[1].step.application,'f duet_h1');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.equal(r.term,null);
});
test('discourse search reports its budget, not false uniqueness',()=>{
 const frame=discourseFrame('from the above result and the above result');
 const rows=Array.from({length:9},(_,i)=>({line:i+1,step:{kind:'establish',name:'h'+i}}));
 const names=rows.map(r=>r.step.name);
 const r=discourseCandidates(frame,'P ∧ P',rows,names,new Map(names.map(n=>[n,'P'])));
 assert.equal(r.overflow,true);
 assert.equal(r.candidates.length,0);
});
test('incremental replay and full evaluation agree after changing a referent',()=>{
 const s=createDraftSession();
 const a='$P$ | p\n$Q$ | q\n由上述结论与 f 得到 $R$';
 s.evaluate(a,scope,facts);
 const b=a.replace('与 f','与 g');
 const r=s.evaluate(b,scope,facts);
 const full=draftProof(b,scope,facts);
 assert.equal(r.reusedRows,2);
 assert.deepEqual(r.rows,full.rows);
 assert.equal(r.rows[2].step.application,'g duet_h2');
});
