import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession} from '../web/natural-draft.mjs';
const scope=['P','Q','R','h','f','g'];
const facts=new Map([['h','P ∧ P'],['f','P → Q'],['g','Q → R']]);
function same(session,input,sc=scope,ctx=facts,choices=new Map()){
 const incremental=session.evaluate(input,sc,ctx,{choices});
 const full=draftProof(input,sc,ctx,{choices});
 const {reusedRows,...rest}=incremental;
 const {reusedRows:unused,...reference}=full;
 assert.deepEqual(rest,reference);
 return incremental;
}
test('editing a later inference reuses the prefix, including open obligation state',()=>{
 const s=createDraftSession();
 const a='establish hp : $P$ | from h\nestablish hq : $Q$ | from hp and f\n$R$ | from hq and g';
 same(s,a);
 const r=same(s,a.replace('from hq and g','g hq'));
 assert.equal(r.reusedRows,2);
 assert.equal(r.rows[2].proofStatus,'depends-on-open');
});
test('candidate changes invalidate the affected suffix but not previous syntax',()=>{
 const s=createDraftSession();
 const input='establish hp : $P$ | from h\nestablish hq : $Q$ | from hp and f\n$R$ | from hq and g';
 same(s,input);
 const r=same(s,input,scope,facts,new Map([[1,'And.left h']]));
 assert.equal(r.reusedRows,0);assert.equal(r.complete,true);
 assert.equal(same(s,input,scope,facts,new Map([[1,'And.left h']])).reusedRows,3);
});
test('context, planned names, and changed conclusion roles invalidate safely',()=>{
 const s=createDraftSession();
 same(s,'$P$\n$Q$');
 assert.equal(same(s,'$P$\n$Q$\n$R$').reusedRows,1);
 assert.equal(same(s,'$P$\nestablish duet_h1 : $Q$\n$R$').reusedRows,0);
 assert.equal(same(s,'$P$\nestablish duet_h1 : $Q$\n$R$',scope,new Map([...facts,['h','P']])).reusedRows,0);
 s.reset();assert.equal(same(s,'$P$').reusedRows,0);
});
test('unresolved syntax is retained and cached without inventing a binding',()=>{
 const s=createDraftSession();
 same(s,'uniformly $P$\n$Q$');
 const r=same(s,'uniformly $P$\n$R$');
 assert.equal(r.reusedRows,1);assert.equal(r.term,null);
});
