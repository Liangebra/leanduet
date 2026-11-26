import test from 'node:test';
import assert from 'node:assert/strict';
import {parseLean,renderLean,renderProse,EXAMPLES} from '../web/core.mjs';
import {replaceStep,snapshot,restore,lineRange} from '../web/workspace.mjs';
const lean=EXAMPLES[0].source,prose=renderProse(parseLean(lean));
test('step editing preserves theorem and neighboring lines',()=>{const ir=replaceStep(lean,'line-4','exact hqr (hpq hp)');assert.equal(renderLean(ir),lean.replace('hqr hq','hqr (hpq hp)'));});
test('step editing rejects injection of extra lines',()=>assert.throws(()=>replaceStep(lean,'line-4','exact hqr hq\n  rfl')));
test('step editing rejects missing nodes',()=>assert.throws(()=>replaceStep(lean,'line-99','rfl')));
test('workspace preserves both unsynced drafts and notes',()=>{const d=snapshot({lean,prose},{lean:lean+'  rfl\n',prose:prose+'draft'},'my argument','proof');const r=restore(JSON.parse(JSON.stringify(d)));assert.equal(r.drafts.lean,d.drafts.lean);assert.equal(r.drafts.prose,d.drafts.prose);assert.equal(r.notes,'my argument');});
test('workspace rejects mismatched base',()=>assert.throws(()=>restore(snapshot({lean,prose:'wrong'},{lean,prose},'','proof'))));
test('workspace rejects unknown version',()=>assert.throws(()=>restore({format:'leanduet-workspace',version:2})));
test('line range matches nested source',()=>{const s=EXAMPLES[2].source;const [a,b]=lineRange(s,3);assert.equal(s.slice(a,b),'    exact h');});

test('workspace stores unverified research objects separately from formal drafts',()=>{
 const exploration={schema:1,next:3,items:[
  {id:1,label:'x',expression:'x / 0 = ?',comment:'attempt',links:'#2',state:'discarded'},
  {id:2,label:'x',expression:'x ≠ x',comment:'alternative',links:'#1',state:'doubtful'}]};
 const w=snapshot({lean,prose},{lean,prose},'free text','proof',exploration);
 const r=restore(JSON.parse(JSON.stringify(w)));
 assert.deepEqual(r.exploration,exploration);
 assert.equal(r.drafts.lean,lean);
 assert.equal(r.notes,'free text');
 assert.deepEqual(restore(snapshot({lean,prose},{lean,prose},'','old')).exploration,{schema:1,next:1,items:[]});
});
