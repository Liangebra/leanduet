// Consume a goal constructor; never introduce arbitrary assumptions.
import {compileFormula,renderFormula,scopedFormula} from './math-formula.mjs';
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function containsName(ast,name){
 if(ast.kind==='id'&&ast.value===name||['binder','bounded'].includes(ast.kind)&&ast.name===name)return true;
 return Object.values(ast).some(v=>v&&typeof v==='object'&&(Array.isArray(v)?v.some(x=>containsName(x,name)):containsName(v,name)));
}
function rename(ast,oldName,newName){
 if(ast.kind==='id')return ast.value===oldName?{...ast,value:newName}:ast;
 if(ast.kind==='binary')return {...ast,left:rename(ast.left,oldName,newName),right:rename(ast.right,oldName,newName)};
 if(ast.kind==='unary')return {...ast,body:rename(ast.body,oldName,newName)};
 if(ast.kind==='call')return {...ast,fn:rename(ast.fn,oldName,newName),args:ast.args.map(x=>rename(x,oldName,newName))};
 if(ast.kind==='binder'||ast.kind==='bounded'){
  const k=ast.kind==='binder'?'domain':'set';
  return {...ast,[k]:ast[k]?rename(ast[k],oldName,newName):null,body:ast.name===oldName?ast.body:rename(ast.body,oldName,newName)};
 }
 return ast;
}
function negationBody(ast){
 if(ast.kind==='unary'&&ast.op==='¬')return ast.body;
 if(ast.kind==='call'&&ast.fn?.kind==='id'&&ast.fn.value==='Not'&&ast.args.length===1)return ast.args[0];
 return null;
}
function inferredIntroductionType(ast,kind){
 if(kind==='introduce'&&ast.kind==='binder'&&ast.op==='∀'&&ast.domain)return renderFormula(ast.domain);
 if(kind==='assume'&&ast.kind==='binary'&&ast.op==='→')return renderFormula(ast.left);
 const negative=kind==='assume'?negationBody(ast):null;
 if(negative)return renderFormula(negative);
 throw Error('The current goal does not determine a supported introduction type; supply an annotation.');
}

/** Describe a goal operation before opening its child proof obligations. */
export function planGoalOperation(goal,{kind,name=null,type=null,source=null,sourceType=null,branchNames=['hp','hq']}={}){
 if(!goal)throw Error('A proof operation needs the current goal.');
 const ast=compileFormula(goal,{syntax:'lean'}).ast;
 if(kind==='disjunction-elimination'){
  if(typeof sourceType!=='string')throw Error('Disjunction elimination needs a typed source.');
  const sourceAst=compileFormula(sourceType,{syntax:'lean'}).ast;
  let parts=null;
  if(sourceAst.kind==='binary'&&sourceAst.op==='∨')parts=[sourceAst.left,sourceAst.right];
  else if(sourceAst.kind==='call'&&sourceAst.fn?.kind==='id'&&sourceAst.fn.value==='Or'&&sourceAst.args.length===2)parts=sourceAst.args;
  if(!parts)throw Error('The cited source is not a supported disjunction.');
  return {kind:'disjunction-elimination',parentGoal:goal,logic:'intuitionistic',source,
   subgoals:parts.map((part,index)=>({id:index===0?'left':'right',goal,contextDelta:[{
    name:branchNames[index],type:renderFormula(part),kind:'case-assumption'
   }]})),
   closure:{kind:'eliminator',name:'Or.elim',source}};
 }
 if(kind==='conjunction-introduction'){
  let parts=null;
  if(ast.kind==='binary'&&ast.op==='∧')parts=[ast.left,ast.right];
  else if(ast.kind==='call'&&ast.fn?.kind==='id'&&ast.fn.value==='And'&&ast.args.length===2)parts=ast.args;
  if(!parts)throw Error('The current goal is not a supported conjunction.');
  return {kind:'conjunction-introduction',parentGoal:goal,logic:'intuitionistic',
   subgoals:parts.map((part,index)=>({id:index===0?'first':'second',goal:renderFormula(part),contextDelta:[]})),
   closure:{kind:'constructor',name:'And.intro'}};
 }
 if(!['introduce','assume'].includes(kind))throw Error('Unknown goal operation.');
 const introType=type||inferredIntroductionType(ast,kind);
 if(typeof name!=='string'||!name)name=ast.kind==='binder'?ast.name:'h';
 const domain=compileFormula(introType,{syntax:'lean'}).scoped;
 if(kind==='introduce'){
  if(ast.kind!=='binder'||ast.op!=='∀'||(ast.domain&&!same(scopedFormula(ast.domain),domain)))
   throw Error('The current goal is not a matching universal.');
  if(name!==ast.name&&containsName(ast.body,name))throw Error('Introduction name may capture an existing occurrence; choose a fresh name.');
  return {kind:'universal-introduction',parentGoal:goal,logic:'dependent-function',
   subgoals:[{id:'body',goal:renderFormula(rename(ast.body,ast.name,name)),contextDelta:[{name,type:introType,kind:'universal-variable'}]}],
   closure:{kind:'binder-introduction',name}};
 }
 if(ast.kind==='binary'&&ast.op==='→'&&same(scopedFormula(ast.left),domain))return {
  kind:'implication-introduction',parentGoal:goal,logic:'intuitionistic',
  subgoals:[{id:'body',goal:renderFormula(ast.right),contextDelta:[{name,type:introType,kind:'assumption'}]}],
  closure:{kind:'binder-introduction',name}
 };
 const negative=negationBody(ast);
 if(negative&&same(scopedFormula(negative),domain))return {
  kind:'negation-introduction',parentGoal:goal,logic:'intuitionistic',
  subgoals:[{id:'contradiction',goal:'False',contextDelta:[{name,type:introType,kind:'assumption'}]}],
  closure:{kind:'binder-introduction',name}
 };
 throw Error('The current goal is not a matching implication or negation.');
}

export function extendGoal(goal,introduction){
 return planGoalOperation(goal,introduction).subgoals[0].goal;
}

export function inferIntroduction(goal,kind,name=null){
 return planGoalOperation(goal,{kind,name}).subgoals[0].contextDelta[0].type;
}
export function existentialBindings(sourceType,{name,type=null}){
 if(!sourceType)throw Error('The cited existential premise has no known type.');
 const ast=compileFormula(sourceType,{syntax:'lean'}).ast;
 if(ast.kind!=='binder'||ast.op!=='∃')throw Error('The cited premise is not a supported existential.');
 if(ast.domain&&type&&!same(scopedFormula(ast.domain),compileFormula(type,{syntax:'lean'}).scoped))throw Error('Witness type does not match the existential domain.');
 const domain=type||(ast.domain?renderFormula(ast.domain):null);
 if(!domain)throw Error('Supply the witness type for an existential with an implicit domain.');
 if(name!==ast.name&&containsName(ast.body,name))throw Error('Witness name may capture an existing occurrence; choose a fresh name.');
 return {type:domain,evidenceType:renderFormula(rename(ast.body,ast.name,name))};
}
