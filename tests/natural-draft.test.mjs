import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,compileNaturalDraft} from '../web/natural-draft.mjs';
test('Chinese mathematical prose generates named intermediate results without Lean',()=>{
 const d=compileNaturalDraft('建立 hq : $Q$，由 f，使用 p\n因此 $R$，由 g，使用 hq',['P','Q','R','f','g','p']);
 assert.equal(d.term,'by\n  have hq : Q := f p\n  show R\n  exact g hq');
 assert.deepEqual(d.rows[1].modifiers,['因此']);
});
test('English rule-first phrasing and formula-only lines',()=>{
 const d=compileNaturalDraft('By f using p, we obtain $Q$\nHence $R$ | g duet_h1',['f','g','p','Q','R']);
 assert.match(d.term,/have duet_h1 : Q := f p/);
 assert.match(d.term,/exact g duet_h1/);
});
test('unknown assumptions do not vanish and block executable export',()=>{
 const d=draftProof('uniformly $Q$\n$R$',['Q','R']);
 assert.equal(d.complete,false);assert.equal(d.term,null);
 assert.equal(d.rows[0].raw,'uniformly $Q$');assert.equal(d.rows[1].status,'provisional');
});

test('future intermediate names cannot masquerade as global declarations',()=>{
 const d=draftProof('$P$ | later\nestablish later : $Q$ | f\n$R$ | g',['f','g']);
 assert.equal(d.complete,false);
 assert.match(d.rows[0].reason,/forward/);
});
test('automatic naming does not collide with a later explicit binding',()=>{
 const d=draftProof('$P$ | f\nestablish duet_h1 : $Q$ | g\n$R$ | h',['f','g','h']);
 assert.equal(d.complete,true);
 assert.equal(d.steps[0].name,'duet_h2');
});

test('ambiguous proofs retain typed intermediate objects without exporting a proof',()=>{
 const facts=new Map([['h','P ∧ P'],['f','P → Q'],['g','Q → R']]);
 const r=draftProof('establish hp : $P$ | from h\nestablish hq : $Q$ | from hp and f\n$R$ | from hq and g',[...facts.keys()],facts);
 assert.equal(r.complete,false);assert.equal(r.term,null);
 assert.equal(r.rows[0].status,'unresolved');
 assert.equal(r.rows[0].step.name,'hp');
 assert.equal(r.rows[0].candidates.length,2);
 assert.equal(r.rows[1].step.application,'f hp');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.deepEqual(r.rows[1].dependencies,['hp']);
 assert.equal(r.rows[2].step.application,'g hq');
 assert.deepEqual(r.openBindings,['hp','hq']);
});
test('formula-only obligations are distinct from verified proofs',()=>{
 const r=draftProof('establish hp : $P$\n$Q$ | f hp',['f']);
 assert.equal(r.complete,true); // structurally exportable for Lean search
 assert.equal(r.rows[0].proofStatus,'open');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.match(r.term,/by exact\?/);
});
