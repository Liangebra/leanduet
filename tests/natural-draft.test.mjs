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
