import test from 'node:test';
import assert from 'node:assert/strict';
import {validateJudgment} from '../web/semantic-ir.mjs';
const n=s=>[[],'str',s];
const base={schema:1,format:'leanduet.kernel-judgment',declaration:n('demo'),path:'root',universes:[],judgment:{kind:'proof',context:[{slot:0,name:n('P'),binder:'explicit',internal:false,type:['sort',['zero']],value:null}],term:['lambda',n('h'),'explicit',['local',0],['bound',0]],type:['pi',n('h'),'explicit',['local',0],['local',0]],formula:null}};
test('structural IR validates context slots and binder scopes',()=>assert.equal(validateJudgment(base),base));
test('forward references, unbound variables and unresolved universe tags are rejected',()=>{
 for(const term of [['local',1],['bound',0],['sort',['unresolved']]])assert.throws(()=>validateJudgment({...base,judgment:{...base.judgment,term}}));
 const ctx=[{...base.judgment.context[0],type:['local',0]}];
 assert.throws(()=>validateJudgment({...base,judgment:{...base.judgment,context:ctx}}));
});
