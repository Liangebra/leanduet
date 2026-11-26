import test from 'node:test';
import assert from 'node:assert/strict';
import {anchorFor,wordingFor,putWording,uniqueMatch} from '../web/wording.mjs';
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
