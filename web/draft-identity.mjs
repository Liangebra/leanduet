// Conservative correspondence between revisions of one natural draft.
// This tracks introduction occurrences, not Lean kernel equality.
function groups(nodes,key){
 const result=new Map();
 for(const n of nodes){const k=key(n);if(!result.has(k))result.set(k,[]);result.get(k).push(n);}
 return result;
}
function allNodes(graph){
 const out=[],seen=new Set();
 function visit(current){
  for(const node of current?.nodes||[]){
   if(!seen.has(node.id)){seen.add(node.id);out.push(node);}
   for(const branch of node.branches||[])visit(branch.graph);
  }
 }
 visit(graph);return out;
}
function stableTree(t,ids){
 if(!t)return null;
 if(t.kind==='local'){
  if(!ids.has(t.id))throw Error('Unmatched local');
  return {...t,id:ids.get(t.id)};
 }
 if(t.kind==='binary')return {...t,left:stableTree(t.left,ids),right:stableTree(t.right,ids)};
 if(t.kind==='unary')return {...t,body:stableTree(t.body,ids)};
 if(t.kind==='call')return {...t,fn:stableTree(t.fn,ids),args:t.args.map(a=>stableTree(a,ids))};
 if(t.kind==='binder')return {...t,domain:stableTree(t.domain,ids),body:stableTree(t.body,ids)};
 return t;
}
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const contextSignature=nodes=>nodes.filter(n=>n.kind==='context').map(n=>[n.name,n.type,n.ambiguousName]);
const lineKey=n=>JSON.stringify([n.origin||n.kind,n.raw]);
function candidateKey(c,ids){
 if(c.dependencies.some(id=>!ids.has(id)))return null;
 if(c.type&&!c.formula?.tree)return null;
 return JSON.stringify([c.schema,c.term,c.type?stableTree(c.formula.tree,ids):null,c.dependencies.map(id=>ids.get(id)).sort()]);
}
function matchingContent(a,b,oldIds,newIds){
 const oldScope=(a.scopeRefs||[]).map(x=>oldIds.get(x));
 const newScope=(b.scopeRefs||[]).map(x=>newIds.get(x));
 if(oldScope.includes(undefined)||newScope.includes(undefined)||!same(oldScope,newScope))return false;
 if(a.origin==='infer-proposition'&&b.origin===a.origin){
  // The hole is the introduction; resolving its type is not a new
  // introduction. Require the entire original candidate domain to match.
  const left=(a.typeDomain||[]).map(c=>candidateKey(c,oldIds));
  const right=(b.typeDomain||[]).map(c=>candidateKey(c,newIds));
  return left.length>0&&!left.includes(null)&&!right.includes(null)&&same(left,right);
 }
 return !!a.formula.tree&&!!b.formula.tree&&same(stableTree(a.formula.tree,oldIds),stableTree(b.formula.tree,newIds))&&same(stableTree(a.value?.tree,oldIds),stableTree(b.value?.tree,newIds));
}
export function reconcileDraftIdentity(previous,graph){
 const ids=new Map(),matches=new Map();let next=previous?.next??1;
 const fresh=()=> 'object:'+next++;
 const oldRoot=previous?.graph?.nodes||[],nowRoot=graph.nodes;
 const sameRootContext=!!previous&&previous.graph.goal===graph.goal&&same(contextSignature(oldRoot),contextSignature(nowRoot));
 const oldById=new Map(allNodes(previous?.graph).map(n=>[n.id,n]));
 const mapToPrior=(currentId,priorId)=>{
  if(priorId&&previous?.ids.has(priorId)){
   ids.set(currentId,previous.ids.get(priorId));matches.set(currentId,priorId);return true;
  }
  ids.set(currentId,fresh());return false;
 };
 if(sameRootContext){
  const oldContext=new Map(oldRoot.filter(n=>n.kind==='context').map(n=>[n.id,n]));
  for(const node of nowRoot.filter(n=>n.kind==='context')){
   const prior=oldContext.get(node.id);
   if(prior&&same([prior.name,prior.type,prior.ambiguousName],[node.name,node.type,node.ambiguousName]))mapToPrior(node.id,prior.id);
   else ids.set(node.id,fresh());
  }
 }
 function scopeMatches(oldGraph,newGraph){
  if(!oldGraph||!newGraph||oldGraph.goal!==newGraph.goal)return false;
  const a=(oldGraph.nodes||[]).filter(n=>n.kind==='context'),b=(newGraph.nodes||[]).filter(n=>n.kind==='context');
  if(a.length!==b.length)return false;
  return a.every((node,index)=>{
   const oldIdentity=previous?.ids.get(node.id),newIdentity=ids.get(b[index].id);
   return oldIdentity!==undefined&&newIdentity!==undefined&&oldIdentity===newIdentity&&
    same([node.type,node.ambiguousName],[b[index].type,b[index].ambiguousName]);
  });
 }
 function pairBranches(oldNode,newNode,eligible){
  const oldBranches=oldNode?.branches||[],newBranches=newNode?.branches||[];
  for(const branch of newBranches){
   const matchesByCtor=oldBranches.filter(candidate=>candidate.constructor===branch.constructor);
   const prior=matchesByCtor.length===1?matchesByCtor[0]:null;
   const oldBinding=prior?.binding?.id||prior?.bindingId,newBinding=branch.binding?.id||branch.bindingId;
   const oldContext=oldById.get(oldBinding),newContext=allNodes({nodes:branch.graph?.nodes||[]}).find(node=>node.id===newBinding);
   let compatible=!!(eligible&&prior&&oldBinding&&newBinding&&oldContext&&newContext&&
    same([oldContext.type,oldContext.ambiguousName],[newContext.type,newContext.ambiguousName]));
   if(compatible){
    try{compatible=same(stableTree(oldContext.formula?.tree,previous.ids),stableTree(newContext.formula?.tree,ids));}catch{compatible=false;}
   }
   if(compatible){
    mapToPrior(branch.id,prior.id);
    mapToPrior(newBinding,oldBinding);
   }else{
    if(branch.id&&!ids.has(branch.id))ids.set(branch.id,fresh());
    if(newBinding&&!ids.has(newBinding))ids.set(newBinding,fresh());
   }
   reconcileScope(prior?.graph,branch.graph,compatible);
  }
 }
 function reconcileScope(oldGraph,newGraph,allowed){
  if(!newGraph)return;
  const oldNodes=oldGraph?.nodes||[],newNodes=newGraph.nodes||[];
  const compatible=allowed&&scopeMatches(oldGraph,newGraph);
  const oldContexts=new Map(oldNodes.filter(n=>n.kind==='context').map(n=>[n.id,n]));
  for(const node of newNodes.filter(n=>n.kind==='context')){
   if(ids.has(node.id))continue;
   const prior=compatible?oldContexts.get(node.id):null;
   if(prior&&same([prior.type,prior.ambiguousName],[node.type,node.ambiguousName]))mapToPrior(node.id,prior.id);
   else ids.set(node.id,fresh());
  }
  const oldRows=oldNodes.filter(n=>n.kind!=='context'&&n.kind!=='case-branch');
  const newRows=newNodes.filter(n=>n.kind!=='context'&&n.kind!=='case-branch');
  const oldLines=groups(oldRows,lineKey),newLines=groups(newRows,lineKey);
  for(const node of newRows){
   let prior=null;
   if(compatible){
    const a=oldLines.get(lineKey(node))||[],b=newLines.get(lineKey(node))||[];
    if(a.length===1&&b.length===1){
     try{if(matchingContent(a[0],node,previous.ids,ids))prior=a[0];}catch{}
    }
   }
   mapToPrior(node.id,prior?.id);
   if(node.kind==='cases')pairBranches(prior,node,!!prior&&compatible);
  }
 }
 reconcileScope(previous?.graph,graph,sameRootContext);
 return {graph,ids,matches,next};
}
// Migrate only an explicitly selected candidate whose old and new premise
// identities and rule agree. Never migrate by candidate index or text alone.
export function migrateDraftChoices(previous,current,choices){
 const result=new Map();
 if(!previous)return result;
 const oldById=new Map(allNodes(previous.graph).map(n=>[n.id,n]));
 for(const n of allNodes(current.graph)){
  const oldId=current.matches.get(n.id);
  const oldLine=/\/line:(\d+)$|^line:(\d+)$/.exec(oldId||'');
  const newLine=/\/line:(\d+)$|^line:(\d+)$/.exec(n.id);
  if(!oldId||!oldLine||!newLine)continue;
  const selected=choices.get(Number(oldLine[1]||oldLine[2]));if(!selected)continue;
  const p=oldById.get(oldId);
  const oldCandidates=p?.alternatives.filter(c=>(c.choice??c.term)===selected)||[];
  if(oldCandidates.length!==1)continue;
  const key=candidateKey(oldCandidates[0],previous.ids);if(!key)continue;
  const compatible=n.alternatives.filter(c=>candidateKey(c,current.ids)===key);
  if(compatible.length===1)result.set(Number(newLine[1]||newLine[2]),compatible[0].choice??compatible[0].term);
 }
 return result;
}
