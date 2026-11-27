// A draft is a revision-local, acyclic semantic graph, not a checked proof.
// Identity is assigned by introduction occurrence, never by proposition or name.
import {compileFormula} from './math-formula.mjs';
export function buildDraftGraph(scope,facts,rows,{goal=null}={}){
 const nodes=[],bindings=new Map(),symbolicBindings=new Map(),counts=new Map();
 for(const name of scope)counts.set(name,(counts.get(name)||0)+1);
 function declare(node){
  nodes.push(node);
  if(node.name&&counts.get(node.name)!==undefined&&counts.get(node.name)!==1)return;
  if(node.name&&node.kind!=='unresolved')bindings.set(node.name,node.id);
  if(node.name&&node.origin==='infer-proposition'&&node.typeDomain?.length)symbolicBindings.set(node.name,node.id);
 }
 const refs=names=>[...new Set(names.map(name=>bindings.get(name)||symbolicBindings.get(name)).filter(Boolean))];
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
 const scopeRefs=[],constraintGroups=new Map();
 for(const row of rows){
  const id='line:'+row.line,step=row.step,parsed=formula(row.type),value=step?.kind==='define'?formula(step.value):null;
  function alternative(c){
   const candidateFormula=c.type?formula(c.type):null;
   return {schema:c.schema,term:c.term,...(c.choice?{choice:c.choice}:{}),...(c.type?{type:c.type,formula:candidateFormula}:{}),
    dependencies:[...new Set([...refs(c.premises||[]),...(candidateFormula?.refs||[])])]};
  }
  const alternatives=(row.candidates||[]).map((c,i)=>({id:id+':candidate:'+i,...alternative(c)}));
  const group=row.constraintGroup;
  if(group)constraintGroups.set(group.id,group);
  const constraintRefs=[...new Set([...(row.constraints||[]).filter(c=>c.line!==row.line).map(c=>'line:'+c.line),...(group?.variables||[]).filter(v=>v.line!==row.line).map(v=>'line:'+v.line),...(group?.relations||[]).filter(r=>r.line!==row.line).map(r=>'line:'+r.line)])];
  const application=step?.application||null;
  const selected=application&&application!=='?'?alternatives.find(c=>c.term===application):null;
  const proofRefs=application&&application!=='?'?(selected?.dependencies||refs(application.split(/\s+/))):[];
  const node={id,kind:step?.kind||'unresolved',name:step?.name||(row.kind==='infer-proposition'?row.name:null),type:row.type||null,raw:row.raw,modifiers:row.modifiers||[],formula:parsed,
   proofStatus:row.proofStatus||'open',status:row.status,application,alternatives,value,...(row.domain?{origin:'infer-proposition',typeDomain:row.domain.map(alternative),constraints:row.constraints,constraintRefs,constraintGroup:group?.id||null}:{}),
   selectedCandidate:selected?.id||null,scopeRefs:[...scopeRefs],dependencies:[...new Set([...scopeRefs,...parsed.refs,...(value?.refs||[]),...proofRefs])]};
  declare(node);
  if(['introduce','assume'].includes(node.kind))scopeRefs.push(id);
 }
 return {schema:1,identity:'revision-local',goal,nodes,constraintGroups:[...constraintGroups.values()]};
}
export function dependentNodes(graph,ids,{includeAlternatives=true}={}){
 const affected=new Set(ids);
 // Constraint edges point backwards in source order. They are invalidation
 // edges, not proof dependencies; a fixed point handles their cycles.
 let changed=true;
 while(changed){
  changed=false;
  for(const node of graph.nodes){
   if(affected.has(node.id))continue;
   const deps=[...node.dependencies,...(node.constraintRefs||[]),
    ...(includeAlternatives?[...(node.alternatives||[]),...(node.typeDomain||[])].flatMap(c=>c.dependencies):[])];
   if(deps.some(id=>affected.has(id))){affected.add(node.id);changed=true;}
  }
 }
 return graph.nodes.filter(n=>affected.has(n.id)).map(n=>n.id);
}
