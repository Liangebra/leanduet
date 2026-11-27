// Conservative correspondence between revisions of one natural draft.
// This tracks introduction occurrences, not Lean kernel equality.
function groups(nodes,key){
 const result=new Map();
 for(const n of nodes){const k=key(n);if(!result.has(k))result.set(k,[]);result.get(k).push(n);}
 return result;
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
const lineKey=n=>JSON.stringify([n.kind,n.raw]);
function candidateKey(c,ids){
 if(c.dependencies.some(id=>!ids.has(id)))return null;
 return JSON.stringify([c.schema,c.term,c.type||null,c.dependencies.map(id=>ids.get(id)).sort()]);
}
export function reconcileDraftIdentity(previous,graph){
 const ids=new Map(),matches=new Map();let next=previous?.next??1;
 const fresh=()=> 'object:'+next++;
 const old=previous?.graph?.nodes||[],now=graph.nodes;
 const sameContext=!!previous&&previous.graph.goal===graph.goal&&same(contextSignature(old),contextSignature(now));
 const oldLines=groups(old.filter(n=>n.kind!=='context'),lineKey);
 const newLines=groups(now.filter(n=>n.kind!=='context'),lineKey);
 const oldById=new Map(old.map(n=>[n.id,n]));
 for(const n of now){
  let prior=null;
  if(sameContext&&n.kind==='context')prior=oldById.get(n.id);
  else if(sameContext){
   const k=lineKey(n),a=oldLines.get(k)||[],b=newLines.get(k)||[];
   // A repeated source occurrence has no reliable edit correspondence.
   if(a.length===1&&b.length===1&&n.formula.tree&&a[0].formula.tree){
    try{
     if(same(stableTree(a[0].formula.tree,previous.ids),stableTree(n.formula.tree,ids))&&same(stableTree(a[0].value?.tree,previous.ids),stableTree(n.value?.tree,ids))&&(n.scopeRefs||[]).every(x=>ids.has(x))&&same((a[0].scopeRefs||[]).map(x=>previous.ids.get(x)),(n.scopeRefs||[]).map(x=>ids.get(x))))prior=a[0];
    }catch{}
   }
  }
  if(prior&&previous.ids.has(prior.id)){
   ids.set(n.id,previous.ids.get(prior.id));matches.set(n.id,prior.id);
  }else ids.set(n.id,fresh());
 }
 return {graph,ids,matches,next};
}
// Migrate only an explicitly selected candidate whose old and new premise
// identities and rule agree. Never migrate by candidate index or text alone.
export function migrateDraftChoices(previous,current,choices){
 const result=new Map();
 if(!previous)return result;
 const oldById=new Map(previous.graph.nodes.map(n=>[n.id,n]));
 for(const n of current.graph.nodes){
  const oldId=current.matches.get(n.id);
  if(!oldId||!n.id.startsWith('line:'))continue;
  const selected=choices.get(Number(oldId.slice(5)));if(!selected)continue;
  const p=oldById.get(oldId);
  const oldCandidates=p?.alternatives.filter(c=>c.term===selected)||[];
  if(oldCandidates.length!==1)continue;
  const key=candidateKey(oldCandidates[0],previous.ids);if(!key)continue;
  const compatible=n.alternatives.filter(c=>candidateKey(c,current.ids)===key);
  if(compatible.length===1)result.set(Number(n.id.slice(5)),compatible[0].term);
 }
 return result;
}
