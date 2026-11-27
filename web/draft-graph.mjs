// A draft is a revision-local, acyclic semantic graph, not a checked proof.
// Identity is assigned by introduction occurrence, never by proposition or name.
import {compileFormula} from './math-formula.mjs';
export function buildDraftGraph(scope,facts,rows,{goal=null}={}){
 const nodes=[],bindings=new Map(),counts=new Map();
 for(const name of scope)counts.set(name,(counts.get(name)||0)+1);
 function declare(node){
  nodes.push(node);
  if(node.name&&counts.get(node.name)!==undefined&&counts.get(node.name)!==1)return;
  if(node.name)bindings.set(node.name,node.id);
 }
 const refs=names=>[...new Set(names.map(name=>bindings.get(name)).filter(Boolean))];
 function formula(type){
  if(!type)return {tree:null,refs:[],unresolvedNames:[]};
  let tree;try{tree=compileFormula(type,{syntax:'lean'}).scoped;}catch{return {tree:null,refs:[],unresolvedNames:[]};}
  const used=new Set(),unknown=new Set();
  function bind(t){
   if(t.kind==='free'){
    const id=bindings.get(t.name);
    if(id){used.add(id);return {kind:'local',id};}
    unknown.add(t.name);return t;
   }
   if(t.kind==='binary')return {...t,left:bind(t.left),right:bind(t.right)};
   if(t.kind==='unary')return {...t,body:bind(t.body)};
   if(t.kind==='call')return {...t,fn:bind(t.fn),args:t.args.map(bind)};
   if(t.kind==='binder')return {...t,domain:t.domain?bind(t.domain):null,body:bind(t.body)};
   return t;
  }
  return {tree:bind(tree),refs:[...used],unresolvedNames:[...unknown]};
 }
 for(let i=0;i<scope.length;i++){
  const name=scope[i],type=counts.get(name)===1?facts.get(name)||null:null;
  const parsed=formula(type);
  declare({id:'context:'+i,kind:'context',name,type,formula:parsed,dependencies:parsed.refs,ambiguousName:counts.get(name)!==1});
 }
 const scopeRefs=[];
 for(const row of rows){
  const id='line:'+row.line,step=row.step,parsed=formula(row.type),value=step?.kind==='define'?formula(step.value):null;
  const alternatives=(row.candidates||[]).map((c,i)=>({
   id:id+':candidate:'+i,schema:c.schema,term:c.term,dependencies:refs(c.premises||[])
  }));
  const application=step?.application||null;
  const selected=application&&application!=='?'?alternatives.find(c=>c.term===application):null;
  const proofRefs=application&&application!=='?'?(selected?.dependencies||refs(application.split(/\s+/))):[];
  const node={id,kind:step?.kind||'unresolved',name:step?.name||null,type:row.type||null,raw:row.raw,modifiers:row.modifiers||[],formula:parsed,
   proofStatus:row.proofStatus||'open',status:row.status,application,alternatives,value,
   selectedCandidate:selected?.id||null,scopeRefs:[...scopeRefs],dependencies:[...new Set([...scopeRefs,...parsed.refs,...(value?.refs||[]),...proofRefs])]};
  declare(node);
  if(['introduce','assume'].includes(node.kind))scopeRefs.push(id);
 }
 return {schema:1,identity:'revision-local',goal,nodes};
}
export function dependentNodes(graph,ids,{includeAlternatives=true}={}){
 const affected=new Set(ids);
 for(const node of graph.nodes){
  const deps=includeAlternatives?[...node.dependencies,...node.alternatives?.flatMap(c=>c.dependencies)||[]]:node.dependencies;
  if(deps.some(id=>affected.has(id)))affected.add(node.id);
 }
 return graph.nodes.filter(n=>affected.has(n.id)).map(n=>n.id);
}
