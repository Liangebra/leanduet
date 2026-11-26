import test from 'node:test';
import assert from 'node:assert/strict';
import {interpretations,rankInterpretations} from '../web/interpretations.mjs';
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
