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
  if(ast.kind!=='binary'||ast.op!=='→'||!same(scopedFormula(ast.left),domain))
   throw Error('The current goal is not a matching implication.');
  return renderFormula(ast.right);
 }
 throw Error('Unknown context extension.');
}
