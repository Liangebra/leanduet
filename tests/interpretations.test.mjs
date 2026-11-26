import test from 'node:test';
import assert from 'node:assert/strict';
import {interpretations,rankInterpretations,mergeInterpretations} from '../web/interpretations.mjs';
test('discourse markers are distinct from mathematical assumptions',()=>{
 const p=interpretations('显然 $R$，由 g，使用 hq\ntherefore g hq\nuniformly g hq\n$P$', ['g','hq','P','R']);
 assert.equal(p.alternatives.length,3);
 assert.equal(p.alternatives[0].term,'g hq');
 assert.deepEqual(p.alternatives[0].modifiers,['显然']);
 assert.equal(p.unresolved[0].raw,'uniformly g hq');
 const ranked=rankInterpretations(p,{interpretations:[{index:2,candidates:[{term:'p'}]},{index:0,candidates:[{term:'g hq'}]}]});
 assert.equal(ranked[0].term,'g hq');
});
test('unknown notation is kept without semantic repair',()=>{
 const p=interpretations('x ⊛ y\n$Q$',[]);
 assert.equal(p.unresolved[0].raw,'x ⊛ y');
 assert.equal(p.alternatives[0].formula,'Q');
});

test('reviewed AI alternatives do not replace the author's original interpretation',()=>{
 const p=interpretations('$P$\nunknown ⊛',[]);
 const q=interpretations('$P$\n$Q$',[]);
 const r=mergeInterpretations(p,q);
 assert.equal(r.alternatives.length,2);
 assert.equal(r.alternatives[0].raw,'$P$');
 assert.match(r.alternatives[1].origin,/reviewed AI/);
 assert.equal(r.unresolved[0].raw,'unknown ⊛');
});
