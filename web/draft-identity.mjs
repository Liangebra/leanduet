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
   if(a.length===1&&b.length===1){
    try{
     if(matchingContent(a[0],n,previous.ids,ids))prior=a[0];
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
  const oldCandidates=p?.alternatives.filter(c=>(c.choice??c.term)===selected)||[];
  if(oldCandidates.length!==1)continue;
  const key=candidateKey(oldCandidates[0],previous.ids);if(!key)continue;
  const compatible=n.alternatives.filter(c=>candidateKey(c,current.ids)===key);
  if(compatible.length===1)result.set(Number(n.id.slice(5)),compatible[0].choice??compatible[0].term);
 }
 return result;
}
