// Opt-in synthetic latency comparison: node tests/draft-benchmark.mjs
import {performance} from 'node:perf_hooks';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession} from '../web/natural-draft.mjs';
const facts=new Map([['p','P'],['f','P → P']]);
for(let i=0;i<60;i++)facts.set('irrelevant'+i,'T'+i);
const scope=['P',...facts.keys()];
const prefix=Array.from({length:15},(_,i)=>'establish h'+i+' : $P$ | from '+(i?'h'+(i-1):'p')).join('\n');
const texts=[prefix+'\n$P$ | from h14',prefix+'\n$P$ | h14'];
function measure(evaluate){
 const times=[];let reused=0;
 for(let i=0;i<120;i++){
  const start=performance.now(),r=evaluate(texts[i%2]);
  const elapsed=performance.now()-start;
  assert.equal(r.complete,true);
  assert.match(r.term,/exact h14$/);
  if(i>=20){times.push(elapsed);reused+=r.reusedRows||0;}
 }
 times.sort((a,b)=>a-b);
 return {medianMs:times[50],p95Ms:times[95],meanReusedRows:reused/times.length};
}
const session=createDraftSession();
console.log(JSON.stringify({case:'16 lines / 62 typed locals / last-line edit',full:measure(s=>draftProof(s,scope,facts)),incremental:measure(s=>session.evaluate(s,scope,facts))},null,2));
