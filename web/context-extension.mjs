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
export function extendGoal(goal,{kind,name,type}){
 if(!goal)throw Error('An introduction needs the current goal.');
 const ast=compileFormula(goal,{syntax:'lean'}).ast;
 const domain=compileFormula(type,{syntax:'lean'}).scoped;
 if(kind==='introduce'){
  if(ast.kind!=='binder'||ast.op!=='∀'||(ast.domain&&!same(scopedFormula(ast.domain),domain)))
   throw Error('The current goal is not a matching universal.');
  if(name!==ast.name&&containsName(ast.body,name))throw Error('Introduction name may capture an existing occurrence; choose a fresh name.');
  return renderFormula(rename(ast.body,ast.name,name));
 }
 if(kind==='assume'){
  if(ast.kind==='binary'&&ast.op==='→'&&same(scopedFormula(ast.left),domain))return renderFormula(ast.right);
  const negative=negationBody(ast);
  if(negative&&same(scopedFormula(negative),domain))return 'False';
  throw Error('The current goal is not a matching implication or negation.');
 }
 throw Error('Unknown context extension.');
}

export function inferIntroduction(goal,kind){
 if(!goal)throw Error('An introduction needs the current goal.');
 const ast=compileFormula(goal,{syntax:'lean'}).ast;
 if(kind==='introduce'&&ast.kind==='binder'&&ast.op==='∀'&&ast.domain)return renderFormula(ast.domain);
 if(kind==='assume'&&ast.kind==='binary'&&ast.op==='→')return renderFormula(ast.left);
 const negative=kind==='assume'?negationBody(ast):null;
 if(negative)return renderFormula(negative);
 throw Error('The current goal does not determine a supported introduction type; supply an annotation.');
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
