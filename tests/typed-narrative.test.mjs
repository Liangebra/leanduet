import test from 'node:test';
import assert from 'node:assert/strict';
import {narrate} from '../web/typed-narrative.mjs';
const h={kind:'hypothesis',term:'hp',type:'P',children:[]};
const q={kind:'apply',reference:'hpq',type:'Q',children:[h]};
const r={kind:'apply',reference:'hqr',type:'R',children:[q]};
test('application premises precede the conclusion',()=>assert.deepEqual(narrate(r).map(n=>n.expr),['P','Q','R']));
test('binder scopes are kept in the narrative',()=>{const rows=narrate({kind:'assume',binder:'hp',binderType:'P',children:[r]});assert.equal(rows[0].depth,0);assert.equal(rows.at(-1).depth,1);});
test('known theorem names map to bilingual inference phrases',()=>assert.match(narrate({kind:'apply',reference:'Eq.symm',type:'b = a',children:[]},'zh')[0].phrase,/对称性/));
test('unknown nodes are not assigned invented semantics',()=>assert.match(narrate({kind:'opaque',type:'P',children:[]})[0].phrase,/unexpanded/));

test('Japanese explanation retains the exact editable occurrence',()=>{
  const row=narrate({kind:'apply',reference:'Eq.symm',type:'b = a',path:'root/body',editable:true,children:[]},'ja')[0];
  assert.match(row.phrase,/対称性/);assert.equal(row.path,'root/body');assert.equal(row.editable,true);
});
test('binder display is not falsely treated as a local proof replacement',()=>{
  const row=narrate({kind:'assume',binder:'hp',binderType:'P',path:'root',editable:true,children:[r]})[0];
  assert.equal(row.editable,false);
});
