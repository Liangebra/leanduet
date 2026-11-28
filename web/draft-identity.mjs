import {compileFormula} from './math-formula.mjs';
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
   for(const subgoal of node.subgoals||[])visit(subgoal.graph);
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
function sameGoal(a,b){
 if(a===b)return true;
 try{return same(compileFormula(a,{syntax:'lean'}).scoped,compileFormula(b,{syntax:'lean'}).scoped);}
 catch{return false;}
}
function sameTypeText(a,b){
 if(a===b)return true;
 return typeof a==='string'&&typeof b==='string'&&sameGoal(a,b);
}
function sameContextSignature(a,b){
 const left=a.filter(node=>node.kind==='context'),right=b.filter(node=>node.kind==='context');
 return left.length===right.length&&left.every((node,index)=>
  node.name===right[index].name&&node.ambiguousName===right[index].ambiguousName&&sameTypeText(node.type,right[index].type));
}
function formulaShape(text,bindings=[]){
 if(typeof text!=='string')return null;
 const names=new Map(bindings.map((binding,index)=>[binding.name,index]));
 try{
  const tree=compileFormula(text,{syntax:'lean'}).scoped;
  function normalize(value){
   if(!value||typeof value!=='object')return value;
   if(Array.isArray(value))return value.map(normalize);
   if(value.kind==='free'&&names.has(value.name))return {kind:'introduced-local',index:names.get(value.name)};
   return Object.fromEntries(Object.entries(value).map(([key,child])=>[key,normalize(child)]));
  }
  return normalize(tree);
 }catch{return {unsupported:text};}
}
function operationLineKey(node){
 const operation=node?.goalOperation;
 if(!operation)return null;
 const subgoals=(operation.subgoals||[]).map(subgoal=>{
  const bindings=subgoal.contextDelta||[];
  return [subgoal.id,formulaShape(subgoal.goal,bindings),
   bindings.map((binding,index)=>[binding.kind,formulaShape(binding.type,bindings.slice(0,index))])];
 });
 const closure=operation.closure||{};
 const closureBinding=(operation.subgoals||[]).flatMap((subgoal,subgoalIndex)=>
  (subgoal.contextDelta||[]).map((binding,bindingIndex)=>({subgoalIndex,bindingIndex,name:binding.name})))
  .find(binding=>binding.name===closure.name);
 // A binder's spelling is a label; its slot and dependent occurrences carry identity.
 const closureKey=closureBinding?['introduced-local',closureBinding.subgoalIndex,closureBinding.bindingIndex]:closure.name||null;
 return JSON.stringify([node.origin||node.kind,node.kind,operation.kind,operation.logic||null,
  formulaShape(operation.parentGoal),subgoals,closure.kind||null,closureKey,operation.witness||null]);
}
const lineKey=n=>n.origin==='element-request'?JSON.stringify([n.origin,n.raw]):operationLineKey(n)||JSON.stringify([n.origin||n.kind,n.raw]);
function candidateKey(c,ids,nodesById=new Map(),renamedNames=new Map()){
 if(c.dependencies.some(id=>!ids.has(id)))return null;
 if(c.type&&!c.formula?.tree)return null;
 // Normalize only a dependency whose display name changed between these
 // revisions and whose identity is unique on both sides. This preserves
 // proof routes while allowing a selected term to follow a local alpha-rename.
 const dependencyNames=new Map(),ambiguousNames=new Set();
 for(const id of c.dependencies){
  const node=nodesById.get(id),identity=ids.get(id);
  if(!node||typeof node.name!=='string'||identity===undefined)continue;
  if(dependencyNames.has(node.name)&&dependencyNames.get(node.name)!==identity)ambiguousNames.add(node.name);
  else dependencyNames.set(node.name,identity);
 }
 const normalizedTerm=String(c.term).replace(/[\p{L}_][\p{L}\p{N}_']*/gu,name=>{
  const identity=dependencyNames.get(name);
  return identity!==undefined&&!ambiguousNames.has(name)&&renamedNames.get(name)===identity
   ?String.fromCharCode(0)+'local:'+identity+String.fromCharCode(0):name;
 });
 return JSON.stringify([c.schema,normalizedTerm,c.type?stableTree(c.formula.tree,ids):null,c.dependencies.map(id=>ids.get(id)).sort()]);
}
function renamedContextNames(previous,current){
 const byIdentity=(revision)=>{
  const groups=new Map();
  for(const node of allNodes(revision.graph)){
   if(typeof node.name!=='string')continue;
   const identity=revision.ids.get(node.id);if(identity===undefined)continue;
   if(!groups.has(identity))groups.set(identity,[]);
   groups.get(identity).push(node.name);
  }
  return groups;
 };
 const oldGroups=byIdentity(previous),newGroups=byIdentity(current);
 const oldNames=new Map(),newNames=new Map(),oldConflicts=new Set(),newConflicts=new Set();
 const add=(map,conflicts,name,identity)=>{
  if(map.has(name)&&map.get(name)!==identity)conflicts.add(name);else map.set(name,identity);
 };
 for(const [identity,oldSpellings] of oldGroups){
  const newSpellings=newGroups.get(identity);
  if(oldSpellings.length!==1||newSpellings?.length!==1||oldSpellings[0]===newSpellings[0])continue;
  add(oldNames,oldConflicts,oldSpellings[0],identity);
  add(newNames,newConflicts,newSpellings[0],identity);
 }
 for(const name of oldConflicts)oldNames.delete(name);
 for(const name of newConflicts)newNames.delete(name);
 return {old:oldNames,current:newNames};
}
function matchingContent(a,b,oldIds,newIds){
 const oldScope=(a.scopeRefs||[]).map(x=>oldIds.get(x));
 const newScope=(b.scopeRefs||[]).map(x=>newIds.get(x));
 if(oldScope.includes(undefined)||newScope.includes(undefined)||!same(oldScope,newScope))return false;
 if(a.origin==='element-request'&&b.origin===a.origin)return a.raw===b.raw;
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
 const sameRootContext=!!previous&&sameGoal(previous.graph.goal,graph.goal)&&sameContextSignature(oldRoot,nowRoot);
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
   if(prior&&prior.name===node.name&&sameTypeText(prior.type,node.type)&&prior.ambiguousName===node.ambiguousName)mapToPrior(node.id,prior.id);
   else ids.set(node.id,fresh());
  }
 }
 function scopeMatches(oldGraph,newGraph){
  if(!oldGraph||!newGraph||!sameGoal(oldGraph.goal,newGraph.goal))return false;
  const a=(oldGraph.nodes||[]).filter(n=>n.kind==='context'),b=(newGraph.nodes||[]).filter(n=>n.kind==='context');
  if(a.length!==b.length)return false;
  return a.every((node,index)=>{
   const oldIdentity=previous?.ids.get(node.id),newIdentity=ids.get(b[index].id);
   return oldIdentity!==undefined&&newIdentity!==undefined&&oldIdentity===newIdentity&&
    sameTypeText(node.type,b[index].type)&&node.ambiguousName===b[index].ambiguousName;
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
    sameTypeText(oldContext.type,newContext.type)&&oldContext.ambiguousName===newContext.ambiguousName);
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
 function subgoalPlan(node,record){
  return node?.goalOperation?.subgoals?.find(item=>item.id===record.key||item.scopeId===record.id)||null;
 }
 function matchSubgoalBindings(oldNode,newNode,oldSubgoal,newSubgoal){
  const oldDelta=subgoalPlan(oldNode,oldSubgoal)?.contextDelta||[];
  const newDelta=subgoalPlan(newNode,newSubgoal)?.contextDelta||[];
  if(oldDelta.length!==newDelta.length)return false;
  if(!oldDelta.length)return true;
  const oldContexts=new Map(allNodes(oldSubgoal.graph).filter(node=>node.kind==='context').map(node=>[node.id,node]));
  const newContexts=new Map(allNodes(newSubgoal.graph).filter(node=>node.kind==='context').map(node=>[node.id,node]));
  const trialIds=new Map(ids),pairs=[];
  for(let index=0;index<oldDelta.length;index++){
   const prior=oldDelta[index],current=newDelta[index];
   const priorId=prior.id||oldSubgoal.id+'/binding:'+index;
   const currentId=current.id||newSubgoal.id+'/binding:'+index;
   if(prior.kind!==current.kind)return false;
   const priorIdentity=previous?.ids.get(priorId);
   if(priorIdentity===undefined)return false;
   const oldContext=oldContexts.get(priorId),newContext=newContexts.get(currentId);
   if(!oldContext||!newContext||oldContext.ambiguousName||newContext.ambiguousName)return false;
   const oldType=oldContext.formula?.tree,newType=newContext.formula?.tree;
   let compatibleType=sameTypeText(oldContext.type,newContext.type);
   if(oldType&&newType){
    try{compatibleType=same(stableTree(oldType,previous.ids),stableTree(newType,trialIds));}
    catch{compatibleType=false;}
   }
   if(!compatibleType)return false;
   if(trialIds.has(currentId)&&trialIds.get(currentId)!==priorIdentity)return false;
   trialIds.set(currentId,priorIdentity);
   pairs.push([currentId,priorId]);
  }
  for(const [currentId,priorId] of pairs)if(!mapToPrior(currentId,priorId))return false;
  return true;
 }
 function pairSubgoals(oldNode,newNode,eligible){
  const oldSubgoals=oldNode?.subgoals||[];
  for(const subgoal of newNode.subgoals||[]){
   const matchesByKey=oldSubgoals.filter(candidate=>candidate.key&&candidate.key===subgoal.key);
   const prior=matchesByKey.length===1?matchesByKey[0]:null;
   let compatible=!!(eligible&&prior&&sameGoal(prior.goal,subgoal.goal)&&prior.graph&&subgoal.graph);
   if(compatible){
    mapToPrior(subgoal.id,prior.id);
    compatible=matchSubgoalBindings(oldNode,newNode,prior,subgoal);
   }else if(subgoal.id&&!ids.has(subgoal.id))ids.set(subgoal.id,fresh());
   reconcileScope(prior?.graph,subgoal.graph,compatible);
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
   if(prior&&sameTypeText(prior.type,node.type)&&prior.ambiguousName===node.ambiguousName)mapToPrior(node.id,prior.id);
   else ids.set(node.id,fresh());
  }
  const oldRows=oldNodes.filter(n=>n.kind!=='context'&&n.kind!=='case-branch');
  const newRows=newNodes.filter(n=>n.kind!=='context'&&n.kind!=='case-branch');
  const matched=new Map(),usedOld=new Set();

  // Stable, structurally matched rows act as anchors. Repeated source rows
  // are paired only when a monotone interval between such anchors contains
  // exactly one occurrence on each side; ambiguous edits stay unmatched.
  function operationNameRenames(){
   const oldOperations=oldRows.filter(node=>node.goalOperation),newOperations=newRows.filter(node=>node.goalOperation);
   const oldGroups=groups(oldOperations,operationLineKey),newGroups=groups(newOperations,operationLineKey);
   const renames=new Map(),conflicts=new Set();
   for(const [key,oldGroup] of oldGroups){
    const newGroup=newGroups.get(key)||[];
    if(oldGroup.length!==1||newGroup.length!==1)continue;
    const oldOperation=oldGroup[0].goalOperation,newOperation=newGroup[0].goalOperation;
    const bindingSlot=operation=>{
     const name=operation.closure?.name;
     const matches=(operation.subgoals||[]).flatMap((subgoal,subgoalIndex)=>
      (subgoal.contextDelta||[]).map((binding,bindingIndex)=>({subgoalIndex,bindingIndex,binding})))
      .filter(item=>item.binding.name===name);
     return matches.length===1?matches[0]:null;
    };
    const oldSlot=bindingSlot(oldOperation),newSlot=bindingSlot(newOperation);
    if(!oldSlot||!newSlot||oldSlot.subgoalIndex!==newSlot.subgoalIndex||oldSlot.bindingIndex!==newSlot.bindingIndex)continue;
    const oldName=oldSlot.binding.name,newName=newSlot.binding.name;
    if(oldName===newName||!/^[A-Za-z_][A-Za-z0-9_']*$/.test(oldName)||!/^[A-Za-z_][A-Za-z0-9_']*$/.test(newName))continue;
    if(renames.has(oldName)&&renames.get(oldName)!==newName)conflicts.add(oldName);
    else renames.set(oldName,newName);
   }
   for(const name of conflicts)renames.delete(name);
   const destinationCounts=new Map();
   for(const name of renames.values())destinationCounts.set(name,(destinationCounts.get(name)||0)+1);
   for(const [name,destination] of renames)if(destinationCounts.get(destination)>1)renames.delete(name);
   return renames;
  }
  const scopedNameRenames=operationNameRenames();
  const renamingLineKey=(node,side)=>{
   if(node.goalOperation||node.origin==='element-request'||node.origin==='infer-proposition'||!scopedNameRenames.size)
    return lineKey(node);
   const raw=String(node.raw||'').replace(/[A-Za-z_][A-Za-z0-9_']*/g,name=>
    side==='old'?scopedNameRenames.get(name)||name:name);
   return JSON.stringify([node.origin||node.kind,node.kind,raw]);
  };
  function uniquePairs(oldStart,oldEnd,newStart,newEnd){
   const oldGroups=groups(oldRows.slice(oldStart,oldEnd),node=>renamingLineKey(node,'old'));
   const newGroups=groups(newRows.slice(newStart,newEnd),node=>renamingLineKey(node,'new'));
   const pairs=[];
   for(const [key,oldGroup] of oldGroups){
    const newGroup=newGroups.get(key)||[];
    if(oldGroup.length!==1||newGroup.length!==1)continue;
    pairs.push([oldRows.indexOf(oldGroup[0]),newRows.indexOf(newGroup[0])]);
   }
   return pairs;
  }
  function inOrder(pairs){
   const sorted=[...pairs].sort((a,b)=>a[0]-b[0]);
   return sorted.every((pair,index)=>index===0||pair[1]>sorted[index-1][1]);
  }
  function connectChildren(prior,node){
   if(node.kind==='cases')pairBranches(prior,node,!!prior&&compatible);
   if(node.subgoals?.length)pairSubgoals(prior,node,!!prior&&compatible);
  }
  function tryPairs(pairs){
   let changed=false;
   for(const [oldIndex,newIndex] of [...pairs].sort((a,b)=>a[1]-b[1])){
    if(matched.has(newIndex)||usedOld.has(oldIndex))continue;
    const prior=oldRows[oldIndex],node=newRows[newIndex];
    if(!previous?.ids.has(prior.id))continue;
    let contentMatches=false;
    if(compatible){
     try{contentMatches=matchingContent(prior,node,previous.ids,ids);}catch{}
    }
    if(!contentMatches)continue;
    if(!mapToPrior(node.id,prior.id))continue;
    matched.set(newIndex,oldIndex);usedOld.add(oldIndex);
    connectChildren(prior,node);changed=true;
   }
   return changed;
  }

  if(compatible){
   const globalPairs=uniquePairs(0,oldRows.length,0,newRows.length);
   // First retain globally unique rows, preserving the existing behavior.
   // Repeat after local matches because a dependent row may become comparable
   // only after its earlier local object has been reconciled.
   let changed=true;
   while(changed){
    changed=tryPairs(globalPairs);
    const anchors=[...matched].map(([newIndex,oldIndex])=>[oldIndex,newIndex]).sort((a,b)=>a[0]-b[0]);
    if(!inOrder(anchors))continue;
    const boundaries=[[-1,-1],...anchors,[oldRows.length,newRows.length]];
    for(let i=0;i<boundaries.length-1;i++){
     const [oldBefore,newBefore]=boundaries[i], [oldAfter,newAfter]=boundaries[i+1];
     const localPairs=uniquePairs(oldBefore+1,oldAfter,newBefore+1,newAfter);
     if(inOrder(localPairs))changed=tryPairs(localPairs)||changed;
    }
   }
  }

  // Unmatched rows get new identities only after all safe matches have been
  // considered. Their child scopes are also fresh when the parent row changed.
  for(let index=0;index<newRows.length;index++){
   if(matched.has(index))continue;
   const node=newRows[index];
   mapToPrior(node.id,null);
   connectChildren(null,node);
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
 const currentById=new Map(allNodes(current.graph).map(n=>[n.id,n]));
 const renamedNames=renamedContextNames(previous,current);
 for(const n of currentById.values()){
  const oldId=current.matches.get(n.id);
  const oldLine=/\/line:(\d+)$|^line:(\d+)$/.exec(oldId||'');
  const newLine=/\/line:(\d+)$|^line:(\d+)$/.exec(n.id);
  if(!oldId||!oldLine||!newLine)continue;
  const selected=choices.get(Number(oldLine[1]||oldLine[2]));if(!selected)continue;
  const p=oldById.get(oldId);
  const oldCandidates=p?.alternatives.filter(c=>(c.choice??c.term)===selected)||[];
  if(oldCandidates.length!==1)continue;
  const key=candidateKey(oldCandidates[0],previous.ids,oldById,renamedNames.old);if(!key)continue;
  const compatible=n.alternatives.filter(c=>candidateKey(c,current.ids,currentById,renamedNames.current)===key);
  if(compatible.length===1)result.set(Number(newLine[1]||newLine[2]),compatible[0].choice??compatible[0].term);
 }
 return result;
}
