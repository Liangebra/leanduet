import test from 'node:test';
import assert from 'node:assert/strict';
import {narrate,outlinePaths} from '../web/typed-narrative.mjs';
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

const leaf={kind:'hypothesis',term:'hp',type:'P',path:'root/arg0/arg0',editable:true,children:[]};
const mid={kind:'apply',reference:'f',type:'Q',path:'root/arg0',editable:true,children:[leaf]};
const tree={kind:'apply',reference:'g',type:'R',path:'root',editable:true,children:[mid]};
test('outline collapses occurrences without changing conclusion or edit identity',()=>{
  const before=JSON.stringify(tree),folded=outlinePaths(tree);
  const rows=narrate(tree,'en',{collapsed:folded});
  assert.equal(rows.length,1);assert.equal(rows[0].path,'root');assert.equal(rows[0].expr,'R');assert.equal(rows[0].hiddenCount,2);assert.equal(rows[0].editable,true);
  folded.delete('root');
  assert.deepEqual(narrate(tree,'en',{collapsed:folded}).map(x=>[x.path,x.expr]),[['root/arg0','Q'],['root','R']]);
  assert.equal(JSON.stringify(tree),before);
});
test('folding preserves distinct occurrences even if their types coincide',()=>{
  const a={...mid,path:'root/arg0',type:'R'},b={...mid,path:'root/arg1',type:'R'};
  const t={...tree,children:[a,b]};
  const rows=narrate(t,'en',{collapsed:new Set(['root/arg0'])});
  assert.equal(rows.find(x=>x.path==='root/arg0').folded,true);
  assert.equal(rows.find(x=>x.path==='root/arg1').folded,false);
});
test('extraction limits are explicit, not conflated with user folding',()=>{
  const row=narrate({kind:'opaque',type:'P',path:'root',truncated:true})[0];assert.equal(row.truncated,true);
});

test('argument view refers to actual immediate premises and prior inferences',()=>{
 const rows=narrate(tree,'en',{style:'argument'});
 assert.deepEqual(rows.map(x=>x.path),['root/arg0','root']);
 assert.equal(rows[0].premises[0].term,'hp');
 assert.equal(rows[0].premises[0].path,leaf.path);
 assert.equal(rows[1].premises[0].label,rows[0].stepLabel);
 assert.equal(rows[1].premises[0].path,mid.path);
 assert.equal(rows[1].expr,'R');
});
test('argument mode does not collapse distinct equal-type premises',()=>{
 const a={...leaf,path:'root/arg0',term:'h1'},b={...leaf,path:'root/arg1',term:'h2'};
 const rows=narrate({...tree,children:[a,b]},'en',{style:'argument'});
 assert.deepEqual(rows.at(-1).premises.map(p=>[p.path,p.term]),[[a.path,'h1'],[b.path,'h2']]);
});
test('folded conclusions do not claim hidden derivations as displayed premises',()=>{
 const row=narrate(tree,'en',{style:'argument',collapsed:new Set(['root'])})[0];
 assert.deepEqual(row.premises,[]);assert.equal(row.hiddenCount,2);
});
