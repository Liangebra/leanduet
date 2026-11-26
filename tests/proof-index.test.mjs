import test from 'node:test';
import assert from 'node:assert/strict';
import {indexProof} from '../web/proof-index.mjs';
import {anchorFor} from '../web/wording.mjs';
test('index uses one visit per occurrence and refuses ambiguous anchors',()=>{
 const a={path:'root/arg0',kind:'hypothesis',term:'h',type:'P',children:[]};
 const b={...a,path:'root/arg1'};
 const r={path:'root',kind:'apply',reference:'f',children:[a,b]};
 const i=indexProof(r);
 assert.equal(i.visits,3);assert.equal(i.find(b.path),b);assert.equal(i.counts.get(r),3);
 assert.equal(i.unique(anchorFor(a)),null);assert.equal(i.wording(a,new Map([[anchorFor(a),'thus']])),'');
});
