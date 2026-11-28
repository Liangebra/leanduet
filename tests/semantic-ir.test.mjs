import test from 'node:test';
import assert from 'node:assert/strict';
import {natObjectContextFromJudgment,validateJudgment} from '../web/semantic-ir.mjs';import {validateJudgment} from '../web/semantic-ir.mjs';
const n=s=>[[],'str',s];
const base={schema:1,format:'leanduet.kernel-judgment',declaration:n('demo'),path:'root',universes:[],judgment:{kind:'proof',context:[{slot:0,name:n('P'),binder:'explicit',internal:false,type:['sort',['zero']],value:null}],term:['lambda',n('h'),'explicit',['local',0],['bound',0]],type:['pi',n('h'),'explicit',['local',0],['local',0]],formula:null}};
test('structural IR validates context slots and binder scopes',()=>assert.equal(validateJudgment(base),base));
test('forward references, unbound variables and unresolved universe tags are rejected',()=>{
 for(const term of [['local',1],['bound',0],['sort',['unresolved']]])assert.throws(()=>validateJudgment({...base,judgment:{...base.judgment,term}}));
 const ctx=[{...base.judgment.context[0],type:['local',0]}];
 assert.throws(()=>validateJudgment({...base,judgment:{...base.judgment,context:ctx}}));
});

const natConst=['const',n('Nat'),[]];
const checked={checked:true,shapePreserved:true,encodingPreserved:true,typeDefEq:true,freshContextChecked:true,mode:'same-environment-fresh-context'};
const natIR={schema:1,format:'leanduet.kernel-judgment',declaration:n('demo'),path:'root/body',universes:[],judgment:{kind:'expression',context:[
 {slot:0,name:n('x'),display:'x',binder:'explicit',internal:false,type:natConst,value:null},
 {slot:1,name:n('y'),display:'y',binder:'explicit',internal:false,type:natConst,value:null}
],term:['local',1],type:natConst,formula:null,roundTrip:checked}};
const withFirstLocal=changes=>({...natIR,judgment:{...natIR.judgment,context:[
 {...natIR.judgment.context[0],...changes},natIR.judgment.context[1]
]}});
test('only checked object parameters receive slot-based Nat identities',()=>{
 assert.deepEqual(natObjectContextFromJudgment(natIR),[
  {id:'demo:root/body:slot:0',name:'x',type:'Nat'},
  {id:'demo:root/body:slot:1',name:'y',type:'Nat'}
 ]);
 const fails=code=>error=>error?.name==='SemanticIRContextError'&&error.code===code;
 const {roundTrip,...uncheckedJudgment}=natIR.judgment;
 assert.throws(()=>natObjectContextFromJudgment({...natIR,judgment:uncheckedJudgment}),fails('unchecked-judgment'));
 assert.throws(()=>natObjectContextFromJudgment(withFirstLocal({value:['nat','0']})),fails('local-definition'));
 assert.throws(()=>natObjectContextFromJudgment(withFirstLocal({internal:true})),fails('internal-local'));
 assert.throws(()=>natObjectContextFromJudgment(withFirstLocal({type:['const',n('Int'),[]]})),fails('unsupported-local-type'));
 assert.throws(()=>natObjectContextFromJudgment(withFirstLocal({display:'x y'})),fails('unsupported-local-name'));
});
