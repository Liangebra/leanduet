import test from 'node:test';
import assert from 'node:assert/strict';
import {anchorFor,wordingFor,putWording,uniqueMatch,reattachWording} from '../web/wording.mjs';
const a={path:'root/arg0',kind:'apply',reference:'f',term:'f p',type:'Q',scope:[],children:[]};
test('wording follows an exact unique occurrence, not its old path',()=>{
 const root={path:'root',children:[a]};
 const w=putWording([],root,a,'Therefore,');
 const moved={...a,path:'root/arg1'};
 assert.equal(wordingFor({children:[moved]},moved,w),'Therefore,');
 assert.equal(wordingFor({children:[a,moved]},a,w),'');
 assert.equal(uniqueMatch({children:[{...a,term:'g p'}]},anchorFor(a)),null);
 assert.equal(w[0].text,'Therefore,');
});

test('detached author wording can be explicitly reattached without silently choosing an occurrence',()=>{
 const oldRoot={children:[a]};
 const wording=putWording([],oldRoot,a,'By the original observation,');
 const next={...a,path:'root/arg2',reference:'g',term:'g p'};
 const root={children:[next]};
 assert.equal(wordingFor(root,next,wording),'');
 const moved=reattachWording(wording,root,wording[0].anchor,next);
 assert.equal(wordingFor(root,next,moved),'By the original observation,');
 assert.equal(moved[0].path,next.path);
 assert.equal(wording[0].anchor,anchorFor(a));
 assert.throws(()=>reattachWording(wording,{children:[next,{...next,path:'other'}]},wording[0].anchor,next));
 assert.throws(()=>reattachWording(wording,oldRoot,wording[0].anchor,a));
 const occupied=putWording(wording,root,next,'Already written');
 assert.throws(()=>reattachWording(occupied,root,wording[0].anchor,next));
});
