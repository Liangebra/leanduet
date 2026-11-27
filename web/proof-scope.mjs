import {compileFormula} from './math-formula.mjs';

const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const identifier=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;

function formulaKey(text){
 if(typeof text!=='string'||!text.trim())throw Error('A proof scope needs a proposition.');
 return compileFormula(text,{syntax:'lean'}).scoped;
}

export function rootProofScope(names,facts,{goal=null,id='root'}={}){
 if(!Array.isArray(names)||!(facts instanceof Map))throw Error('Invalid root proof context.');
 const counts=new Map();for(const name of names)counts.set(name,(counts.get(name)||0)+1);
 const bindings=names.map((name,index)=>({
  id:'context:'+index,name,type:counts.get(name)===1?facts.get(name)??null:null,
  kind:'context',local:false
 }));
 return {id,parentId:null,goal:goal===null?null:formulaKey(goal),goalText:goal,bindings};
}

export function resolveProofName(scope,name){
 const matches=scope.bindings.filter(binding=>binding.name===name);
 return matches.length===1?{status:'resolved',binding:matches[0]}:
  {status:matches.length?'ambiguous':'missing',bindings:matches};
}

export function extendProofScope(scope,binding){
 if(!binding||typeof binding.id!=='string'||!identifier.test(binding.name||'')||typeof binding.type!=='string')
  throw Error('Invalid proof-scope binding.');
 if(scope.bindings.some(item=>item.id===binding.id))throw Error('Proof-scope identity already exists.');
 if(resolveProofName(scope,binding.name).status!=='missing')throw Error('A binding with this name is already visible.');
 return {...scope,bindings:[...scope.bindings,{...binding,local:true}]};
}

export function forkProofScope(parent,{id,goal,binding}){
 if(typeof id!=='string'||!id||id===parent.id)throw Error('A child proof scope needs a distinct identity.');
 const child={id,parentId:parent.id,goal:formulaKey(goal),goalText:goal,bindings:[...parent.bindings]};
 const extended=extendProofScope(child,binding);
 return {...extended,localBindingIds:[binding.id]};
}

/**
 * Close one local proof scope. The branch result must prove its own target.
 * Dependencies on declarations introduced inside the scope are discharged;
 * only identities already present in the parent can cross the boundary.
 */
export function closeProofScope(parent,child,{proofType,dependencies=[],localIds=[]}={}){
 if(child.parentId!==parent.id)throw Error('A proof scope cannot return into a different parent.');
 if(!same(formulaKey(proofType),child.goal))throw Error('The local proof does not establish its subgoal.');
 const parentIds=new Set(parent.bindings.map(binding=>binding.id));
 const childIds=new Set([...child.localBindingIds,...localIds]);
 const returned=new Set();
 for(const id of dependencies){
  if(parentIds.has(id))returned.add(id);
  else if(!childIds.has(id))throw Error('A dependency escapes from an unrelated proof scope.');
 }
 return {type:child.goalText,dependencies:[...returned],discharged:[...childIds]};
}

export function proofScopeNames(scope){return scope.bindings.map(binding=>binding.name);}
export function proofScopeFacts(scope){return new Map(scope.bindings.filter(binding=>binding.type!==null).map(binding=>[binding.name,binding.type]));}
