// Consume a goal constructor; never introduce arbitrary assumptions.
import {compileFormula,renderFormula,scopedFormula} from './math-formula.mjs';
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function containsName(ast,name){
 if(ast.kind==='id'&&ast.value===name||['binder','bounded'].includes(ast.kind)&&ast.name===name)return true;
 return Object.values(ast).some(v=>v&&typeof v==='object'&&(Array.isArray(v)?v.some(x=>containsName(x,name)):containsName(v,name)));
}
function hasBinderNamed(ast,name){
 if(!ast||typeof ast!=='object')return false;
 if(['binder','bounded'].includes(ast.kind)&&ast.name===name)return true;
 return Object.values(ast).some(value=>Array.isArray(value)?value.some(item=>hasBinderNamed(item,name)):hasBinderNamed(value,name));
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

// Lean prints bounded quantifiers in their ordinary Pi/And form. Recover the
// restriction only when the membership's left side is exactly the binder.
function restrictedQuantifier(ast,quantifier){
 if(ast?.kind==='bounded'&&ast.op===quantifier)
  return {name:ast.name,domain:null,set:ast.set,property:ast.body};
 if(ast?.kind!=='binder'||ast.op!==quantifier)return null;
 const connective=quantifier==='∀'?'→':'∧',body=ast.body;
 if(body?.kind!=='binary'||body.op!==connective)return null;
 const membership=body.left;
 if(membership?.kind!=='binary'||membership.op!=='∈'||
    membership.left?.kind!=='id'||membership.left.value!==ast.name)return null;
 return {name:ast.name,domain:ast.domain,set:membership.right,property:body.right};
}
function inferredIntroductionType(ast,kind){
 if(kind==='introduce'&&ast.kind==='binder'&&ast.op==='∀'&&ast.domain)return renderFormula(ast.domain);
 if(kind==='introduce'&&ast.kind==='binary'&&ast.op==='→')return renderFormula(ast.left);
 if(kind==='assume'&&ast.kind==='binary'&&ast.op==='→')return renderFormula(ast.left);
 const negative=kind==='assume'?negationBody(ast):null;
 if(negative)return renderFormula(negative);
 throw Error('The current goal does not determine a supported introduction type; supply an annotation.');
}

/** Describe a goal operation before opening its child proof obligations. */
export function planGoalOperation(goal,{kind,name=null,type=null,source=null,sourceType=null,branchNames=['hp','hq'],witness=null,witnessType=null,witnessId=null}={}){
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
 if(kind==='iff-introduction'){
  let parts=null;
  if(ast.kind==='binary'&&ast.op==='↔')parts=[ast.left,ast.right];
  else if(ast.kind==='call'&&ast.fn?.kind==='id'&&ast.fn.value==='Iff'&&ast.args.length===2)parts=ast.args;
  if(!parts)throw Error('The current goal is not a supported equivalence.');
  const [forward,backward]=parts.map(renderFormula);
  return {kind:'iff-introduction',parentGoal:goal,logic:'intuitionistic',
   subgoals:[{id:'forward',goal:'('+forward+' → '+backward+')',contextDelta:[]},
    {id:'reverse',goal:'('+backward+' → '+forward+')',contextDelta:[]}],
   closure:{kind:'constructor',name:'Iff.intro'}};
 }
 if(kind==='existential-introduction'){
  if(ast.kind!=='binder'||ast.op!=='∃')throw Error('The current goal is not a supported existential.');
  if(typeof witness!=='string'||!witness)throw Error('Choose an explicit local witness.');
  const witnessAst=compileFormula(witness,{syntax:'lean'}).ast;
  if(witnessAst.kind!=='id')throw Error('Supply a visible typed local object as the witness.');
  if(typeof witnessType!=='string'||!witnessType)throw Error('The witness type is not available in the current context.');
  if(ast.domain&&!same(scopedFormula(ast.domain),compileFormula(witnessType,{syntax:'lean'}).scoped))
   throw Error('The witness type does not match the existential domain.');
  if(witness!==ast.name&&hasBinderNamed(ast.body,witness))
   throw Error('The witness name would be captured by a nested binder in the existential body.');
  return {kind:'existential-introduction',parentGoal:goal,logic:'dependent-function',witness,witnessId,
   subgoals:[{id:'witness-property',goal:renderFormula(rename(ast.body,ast.name,witness)),contextDelta:[]}],
   closure:{kind:'constructor',name:'Exists.intro',witness}};
 }
 if(kind==='classical-reductio'){
  if(typeof name!=='string'||!name)throw Error('Classical reductio needs a fresh name for the temporary negation.');
  const negatedGoal=renderFormula({kind:'unary',op:'¬',body:ast});
  return {kind:'classical-reductio',parentGoal:goal,logic:'classical',
   subgoals:[{id:'contradiction',goal:'False',contextDelta:[{name,type:negatedGoal,kind:'classical-assumption'}]}],
   closure:{kind:'classical-principle',name:'Classical.byContradiction'}};
 }
 if(!['introduce','assume'].includes(kind))throw Error('Unknown goal operation.');
 const restricted=kind==='introduce'?restrictedQuantifier(ast,'∀'):null;
 if(restricted){
  // A parsed Lean Pi already carries a trustworthy binder domain. Surface
  // bounded quantifiers omit it, so those still require an explicit type.
  if((typeof type!=='string'||!type)&&restricted.domain)type=renderFormula(restricted.domain);
  if(typeof type!=='string'||!type)throw Error('A set-restricted universal needs an explicit element type annotation.');
  const domain=compileFormula(type,{syntax:'lean'}).scoped;
  if(restricted.domain&&!same(scopedFormula(restricted.domain),domain))
   throw Error('The element type does not match the universal binder domain.');
  if(typeof name!=='string'||!name)name=restricted.name;
  if(name!==restricted.name&&(containsName(restricted.property,name)||containsName(restricted.set,name)))
   throw Error('Introduction name may capture an existing occurrence; choose a fresh name.');
  const set=renderFormula(rename(restricted.set,restricted.name,name));
  const property=renderFormula(rename(restricted.property,restricted.name,name));
  const membership='('+name+' ∈ '+set+')';
  return {kind:'bounded-universal-introduction',parentGoal:goal,logic:'intuitionistic',restrictionSet:set,focusProperty:property,
   subgoals:[{id:'restricted-body',goal:'('+membership+' → '+property+')',contextDelta:[{name,type,kind:'universal-variable'}]}],
   closure:{kind:'bounded-binder-introduction',name,requiredCondition:membership}};
 }
 const introType=type||inferredIntroductionType(ast,kind);
 if(typeof name!=='string'||!name)name=ast.kind==='binder'?ast.name:'h';
 const domain=compileFormula(introType,{syntax:'lean'}).scoped;
 if(kind==='introduce'){
  let body;
  if(ast.kind==='binder'&&ast.op==='∀'&&(!ast.domain||same(scopedFormula(ast.domain),domain))){
   if(name!==ast.name&&containsName(ast.body,name))throw Error('Introduction name may capture an existing occurrence; choose a fresh name.');
   body=renderFormula(rename(ast.body,ast.name,name));
  }else if(ast.kind==='binary'&&ast.op==='→'&&same(scopedFormula(ast.left),domain)){
   // Lean prints a nondependent Pi as an arrow. When the request supplies
   // the binder type, treating that function argument as a new object keeps
   // it distinct from the ordinary "assume hp : P" introduction path.
   body=renderFormula(ast.right);
  }else throw Error('The current goal is not a matching universal or typed nondependent Pi.');
  return {kind:'universal-introduction',parentGoal:goal,logic:'dependent-function',
   subgoals:[{id:'body',goal:body,contextDelta:[{name,type:introType,kind:'universal-variable'}]}],
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
 const restricted=restrictedQuantifier(ast,'∃');
 if(restricted){
  if(typeof type!=='string'&&!restricted.domain)
   throw Error('A set-restricted existential needs an explicit witness type annotation.');
  const domain=type||(restricted.domain?renderFormula(restricted.domain):null);
  if(restricted.domain&&type&&!same(scopedFormula(restricted.domain),compileFormula(type,{syntax:'lean'}).scoped))
   throw Error('Witness type does not match the existential domain.');
  if(name!==restricted.name&&(containsName(restricted.property,name)||containsName(restricted.set,name)))
   throw Error('Witness name may capture an existing occurrence; choose a fresh name.');
  const restrictionSet=renderFormula(rename(restricted.set,restricted.name,name));
  const propertyType=renderFormula(rename(restricted.property,restricted.name,name));
  const membership='('+name+' ∈ '+restrictionSet+')';
  return {type:domain,evidenceType:'('+membership+' ∧ '+propertyType+')',restrictionSet,propertyType};
 }
 if(ast.kind!=='binder'||ast.op!=='∃')throw Error('The cited premise is not a supported existential.');
 if(ast.domain&&type&&!same(scopedFormula(ast.domain),compileFormula(type,{syntax:'lean'}).scoped))throw Error('Witness type does not match the existential domain.');
 const domain=type||(ast.domain?renderFormula(ast.domain):null);
 if(!domain)throw Error('Supply the witness type for an existential with an implicit domain.');
 if(name!==ast.name&&containsName(ast.body,name))throw Error('Witness name may capture an existing occurrence; choose a fresh name.');
 const evidenceType=renderFormula(rename(ast.body,ast.name,name));
 return {type:domain,evidenceType,restrictionSet:null,propertyType:evidenceType};
}
