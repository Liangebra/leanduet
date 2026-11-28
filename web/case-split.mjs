import {compileFormula,renderFormula,sameScopedFormula} from './math-formula.mjs';
import {buildDraftGraph} from './draft-graph.mjs';
import {closeProofScope,extendProofScope,forkProofScope,proofDraftClosesGoal,proofScopeBindings,proofScopeFacts,proofScopeNames,resolveProofName} from './proof-scope.mjs';
import {planGoalOperation} from './context-extension.mjs';
import {renderChain} from './proof-chain.mjs';

const ident='[A-Za-z_][A-Za-z0-9_\']{0,63}';
const headerPattern=new RegExp('^(?:分情况讨论|case split|cases|split on)\\s+('+ident+')\\s*[，,;]\\s*(?:建立|得到|establish|prove)\\s+('+ident+')\\s*[:：]\\s*(\\$[^$\\n]+\\$|\\\\\\([^]*?\\\\\\))$','iu');
const branchPattern=new RegExp('^  (左支|右支|left case|right case)\\s+('+ident+')\\s*[:：]?$','iu');

export function hasCaseSplitHeader(text){
 const first=String(text||'').split(/\r?\n/).find(line=>line.trim());
 return !!first&&headerPattern.test(first);
}

function hasFreeName(text,name){
 const tree=compileFormula(text,{syntax:'lean'}).scoped;
 function visit(node){
  if(!node||typeof node!=='object')return false;
  if(node.kind==='free'&&node.name===name)return true;
  return Object.values(node).some(value=>Array.isArray(value)?value.some(visit):visit(value));
 }
 return visit(tree);
}

function parseBlock(input,lineOffset){
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const all=String(input).split(/\r?\n/).map((raw,index)=>({raw,index,line:lineOffset+index+1,indent:(/^ */.exec(raw)||[''])[0].length}));
 if(all.some(x=>x.raw.includes('\t')))throw Error('Use spaces to indent proof branches.');
 const significant=all.filter(x=>x.raw.trim());
 if(significant.length>64)throw Error('A nested proof draft may contain at most 64 nonblank lines.');
 if(!significant.length||significant[0].indent!==0)throw Error('A case split must begin at the start of its proof segment.');
 const head=significant[0],match=headerPattern.exec(head.raw.trim());
 if(!match)throw Error('Expected “分情况讨论 h，建立 hR : $R$” or its English equivalent.');
 const [,source,resultName,typeText]=match;
 const type=compileFormula(typeText).lean;
 const branches=[];let pos=1,tailStart=null;
 while(pos<significant.length){
  const record=significant[pos];
  if(record.indent===0){tailStart=record.index;break;}
  const branch=branchPattern.exec(record.raw);
  if(record.indent!==2||!branch)throw Error('Each branch starts with an indented “左支 name” or “右支 name” heading.');
  const kind=/^(?:左支|left case)$/iu.test(branch[1])?'inl':'inr';
  const name=branch[2];pos++;
  const body=[];
  while(pos<significant.length){
   const next=significant[pos];
   if(next.indent===2&&branchPattern.test(next.raw))break;
   if(next.indent===0){tailStart=next.index;break;}
   if(next.indent<4)throw Error('Indent branch proof steps by four spaces.');
   body.push({raw:next.raw.slice(4),index:next.index,line:next.line});pos++;
  }
  if(!body.length)throw Error('Each disjunction branch needs a proof of the common result.');
  // Keep physical source addresses: blank lines inside an arm must not
  // shift candidate-choice keys or collide with another scoped occurrence.
  const first=body[0].index,last=body.at(-1).index;
  const sourceLines=all.slice(first,last+1).map(line=>line.raw.trim()?line.raw.slice(4):'');
  branches.push({constructor:kind,name,line:record.line,body,sourceLines,bodyLineOffset:all[first].line-1});
  if(tailStart!==null)break;
 }
 if(branches.length!==2||branches[0].constructor!=='inl'||branches[1].constructor!=='inr')
  throw Error('A disjunction split needs one left branch and one right branch, in that order.');
 const tail=tailStart===null?[]:all.slice(tailStart);
 // Parent continuation text is recursively parsed as a draft sequence. It may
 // contain ordinary lines followed by another top-level split, whose own
 // branch indentation belongs to that later block.
 return {head,source,resultName,type,typeText,branches,tail,tailLineOffset:tailStart===null?lineOffset:all[tailStart].line-1};
}

function mapId(id,frame){
 if(typeof id!=='string')return id;
 const context=/^context:(\d+)$/.exec(id);
 if(context)return proofScopeBindings(frame)[Number(context[1])]?.id||id;
 if(frame.id!=='root'&&/^(?:line:|constraint:)/.test(id))return frame.id+'/'+id;
 return id;
}
const scopedLineId=(frame,line)=>frame.id==='root'?'line:'+line:frame.id+'/line:'+line;

function remapNode(node,frame){
 const map=(value,key='')=>{
  if(Array.isArray(value))return ['dependencies','branchDependencies','refs','scopeRefs','constraintRefs'].includes(key)?value.map(item=>mapId(item,frame)):value.map(item=>map(item,key));
  if(!value||typeof value!=='object'){
   if(['id','selectedCandidate','constraintGroup'].includes(key))return mapId(value,frame);
   return value;
  }
  const out={};
  for(const [k,v] of Object.entries(value))out[k]=['branches','subgoals'].includes(k)?v:map(v,k);
  return out;
 };
 return map(node);
}

export function remapProofGraph(graph,frame){
 return {...graph,nodes:graph.nodes.map(node=>remapNode(node,frame)),
  constraintGroups:(graph.constraintGroups||[]).map(group=>({...group,id:mapId(group.id,frame)}))};
}

export function graphNodes(graph){
 const rows=[];
 for(const node of graph?.nodes||[]){
  rows.push(node);
  for(const branch of node.branches||[]){rows.push(branch);rows.push(...graphNodes(branch.graph));}
  for(const subgoal of node.subgoals||[]){rows.push(subgoal);rows.push(...graphNodes(subgoal.graph));}
 }
 return rows;
}
export function proofResultId(graph){
 return [...(graph?.nodes||[])].reverse().find(node=>node.kind!=='context')?.id||null;
}

export function proofContextDependencies(graph){
 const nodes=graphNodes(graph),byId=new Map(nodes.map(node=>[node.id,node]));
 const contexts=new Set(nodes.filter(node=>node.kind==='context').map(node=>node.id));
 const end=[...(graph?.nodes||[])].reverse().find(node=>node.kind!=='context');
 const found=new Set(),visited=new Set();
 function visit(id){
  if(typeof id!=='string'||visited.has(id))return;
  visited.add(id);
  if(contexts.has(id))found.add(id);
  const node=byId.get(id);
  if(node)for(const dependency of node.dependencies||[])visit(dependency);
 }
 if(end)visit(end.id);
 return [...found];
}

function incomplete(input,parsed,branchResults,frame,{goal,choices,closedNames=[],openBindings=[],incompleteContext=false,reason,resolutionStatus='open-obligation',preserveTail=false,compileSegment,cache=null}){
 const line=parsed.head.line;
 // Even an unclosed arm cannot justify a parent result whose type mentions
 // one of its local objects. Check the shared result type against the same
 // scope identities used at closure, while respecting bound occurrences.
 const parentIds=new Set(frame.bindings.map(binding=>binding.id));
 const expired=new Set(closedNames);
 for(const {result} of branchResults){
  for(const node of graphNodes(result?.graph))if(node.name&&!parentIds.has(node.id))expired.add(node.name);
 }
 const parentNames=new Set(proofScopeNames(frame));
 function freeClosed(tree){
  if(tree.kind==='free')return expired.has(tree.name)&&!parentNames.has(tree.name)?tree.name:null;
  for(const value of Object.values(tree))if(value&&typeof value==='object'){
   for(const child of Array.isArray(value)?value:[value]){const name=freeClosed(child);if(name)return name;}
  }
  return null;
 }
 const escaping=freeClosed(compileFormula(parsed.type,{syntax:'lean'}).scoped);
 if(escaping){
  reason='A branch-local name cannot occur in the parent result: '+escaping;
  resolutionStatus='incompatible-target';
 }
 const branches=branchResults.map(({branch,child,result,closed})=>({
  id:child.id,bindingId:child.localBindingIds[0],constructor:branch.constructor,name:branch.name,type:branch.type,goal:parsed.type,
  resultId:proofResultId(result?.graph),dependencies:closed?.dependencies||[],graph:result?.graph||null,
  status:!closed?'open':proofDraftClosesGoal(result)?'complete':'open-obligation'
 }));
 const branchProofIds=branches.map(branch=>branch.resultId).filter(Boolean);
 const row={kind:'cases',raw:parsed.head.raw.trim(),line,status:'unresolved',proofStatus:'open',resolutionStatus,reason,
  name:parsed.resultName,type:parsed.type,source:parsed.source,graphId:scopedLineId(frame,line),step:null,branches,branchProofIds};
 const graph=remapProofGraph(buildDraftGraph(proofScopeNames(frame),proofScopeFacts(frame),[row],{goal}),frame);
 const branchRows=branchResults.flatMap(({child,result})=>(result?.rows||[]).map(item=>({...item,graphId:item.graphId||scopedLineId(child,item.line)})));
 // Keep parsing parent prose even when the provisional result itself has an
 // invalid escaped type. The continuation is explicitly open and the expired
 // names remain unavailable, so this retains useful structure without
 // certifying or exporting a term that depends on the bad result.
 if(preserveTail&&parsed.tail.length){
  const resultFrame=extendProofScope(frame,{id:scopedLineId(frame,line),name:parsed.resultName,type:parsed.type,kind:'cases'});
  const inherited=[...new Set([...openBindings,parsed.resultName])];
  const tailResult=compileSegment(parsed.tail.map(x=>x.raw).join('\n'),resultFrame,{
   goal,choices,lineOffset:parsed.tailLineOffset,closedNames:[...expired],openBindings:inherited,
   incompleteContext:true,cache
  });
  const tailRows=(tailResult.rows||[]).map(item=>({...item,graphId:item.graphId||scopedLineId(resultFrame,item.line)}));
  const rows=[row,...branchRows,...tailRows].sort((a,b)=>a.line-b.line);
  const combinedGraph=remapProofGraph(buildDraftGraph(proofScopeNames(frame),proofScopeFacts(frame),[row,...(tailResult.rows||[])],{goal}),frame);
  const reusedRows=branchResults.reduce((total,item)=>total+(item.result?.reusedRows||0),0)+(tailResult.reusedRows||0);
  return {rows,steps:[],complete:false,completionKind:'incomplete',leanVerification:'not-run',semanticFidelity:'not-assessed',reusedRows,
   openBindings:[...new Set([...inherited,...(tailResult.openBindings||[])])],
   remainingGoal:tailResult.remainingGoal,graph:combinedGraph,term:null};
 }
 const reusedRows=branchResults.reduce((total,item)=>total+(item.result?.reusedRows||0),0);
 return {rows:[row,...branchRows],steps:[],complete:false,completionKind:'incomplete',leanVerification:'not-run',semanticFidelity:'not-assessed',reusedRows,
  openBindings:[...new Set(openBindings)],remainingGoal:goal,graph,term:null};
}

/**
 * Compile one scoped disjunction block and its parent continuation. Each arm
 * is elaborated in a forked identity context; only the common result returns.
 */
export function compileCaseProgram(input,frame,{goal=null,choices=new Map(),lineOffset=0,closedNames=[],openBindings=[],incompleteContext=false,cache=null}={},compileSegment){
 if((frame.id.match(/\/(?:case|subgoal):/g)||[]).length>=8)throw Error('Nested proof scopes are limited to eight levels.');
 const parsed=parseBlock(input,lineOffset),sourceBinding=resolveProofName(frame,parsed.source);
 if(sourceBinding.status!=='resolved'||typeof sourceBinding.binding.type!=='string')
  throw Error('The disjunction source must be a unique, typed parent-scope object.');
 const goalOperation=planGoalOperation(parsed.type,{kind:'disjunction-elimination',source:parsed.source,
  sourceType:sourceBinding.binding.type,branchNames:parsed.branches.map(branch=>branch.name)});
 const [leftType,rightType]=goalOperation.subgoals.map(subgoal=>subgoal.contextDelta[0].type);
 if(resolveProofName(frame,parsed.resultName).status!=='missing')throw Error('The case result name must be fresh in the parent scope.');
 const parentResultId=scopedLineId(frame,parsed.head.line);
 const resultFrame=extendProofScope(frame,{id:parentResultId,name:parsed.resultName,type:parsed.type,kind:'cases'});
 const branchTypes={inl:leftType,inr:rightType};
 const branchResults=[];let firstOpen=null;
 for(const branch of parsed.branches){
  const hidden=resolveProofName(frame,branch.name);
  if(hidden.status!=='missing'&&(hasFreeName(parsed.type,branch.name)||hasFreeName(branchTypes[branch.constructor],branch.name)))
   throw Error('A branch-local name would capture a parent reference in the branch goal or assumption type; use a fresh spelling.');
  const childId=frame.id+'/case:'+parsed.head.line+':'+branch.constructor;
  const child=forkProofScope(frame,{id:childId,goal:parsed.type,binding:{
   id:childId+':binding',name:branch.name,type:branchTypes[branch.constructor],kind:'case-assumption'
  },allowShadow:true});
  const body=branch.sourceLines.join('\n');
  const result=compileSegment(body,child,{goal:parsed.type,choices,lineOffset:branch.bodyLineOffset,closedNames:[...closedNames,...parsed.branches.filter(b=>b!==branch&&b.name!==branch.name).map(b=>b.name)],openBindings,cache});
  if(!result.complete){
   const failed=result.rows.find(row=>row.status==='unresolved');
   firstOpen??=failed?{line:failed.line,reason:failed.reason}:{reason:'A case branch is still open.'};
   branchResults.push({branch:{...branch,type:branchTypes[branch.constructor]},child,result});
   continue;
  }
  // The arm may consume binders of its own goal. Its final annotation
  // must match the remaining goal, not merely the original declaration.
  // This conservative structural check does not replace Lean elaboration.
  const conclusion=result.steps.at(-1);
  if(!['conclude','and-intro','iff-intro','exists-intro','classical-reductio'].includes(conclusion?.kind)||!sameScopedFormula(conclusion.type,result.remainingGoal??parsed.type)){
   const last=result.rows.at(-1);
   const reason='The branch conclusion does not structurally match its remaining goal.';
   firstOpen??={line:last?.line||branch.line,reason};
   branchResults.push({branch:{...branch,type:branchTypes[branch.constructor]},child,
    result:{...result,complete:false,completionKind:'incomplete',term:null,rows:result.rows.map(row=>row===last?{...row,status:'unresolved',proofStatus:'open',resolutionStatus:'incompatible-target',reason}:row)}});
   continue;
  }
  const localIds=graphNodes(result.graph).filter(node=>!frame.bindings.some(binding=>binding.id===node.id)).map(node=>node.id);
  const closed=closeProofScope(frame,child,{proofType:parsed.type,dependencies:proofContextDependencies(result.graph),localIds});
  branchResults.push({branch:{...branch,type:branchTypes[branch.constructor]},child,result,closed});
 }
 if(firstOpen)return incomplete(input,parsed,branchResults,frame,{goal,choices,closedNames,openBindings,incompleteContext,
  reason:(firstOpen.line?'Branch proof line '+firstOpen.line+': ':'')+(firstOpen.reason||'A case branch is still open.'),
  preserveTail:true,compileSegment,cache});
 const branches=branchResults.map(({branch,child,result,closed})=>({
  id:child.id,bindingId:child.localBindingIds[0],constructor:branch.constructor,name:branch.name,type:branch.type,goal:parsed.type,
  steps:result.steps,resultId:proofResultId(result.graph),dependencies:closed.dependencies,graph:result.graph,status:proofDraftClosesGoal(result)?'complete':'open-obligation'
 }));
 const branchDependencies=[...new Set(branches.flatMap(branch=>branch.dependencies))];
 const inheritedOpenIds=new Set(openBindings.map(name=>resolveProofName(frame,name)).filter(result=>result.status==='resolved').map(result=>result.binding.id));
 const hasOpenProof=branchResults.some(({result})=>!proofDraftClosesGoal(result));
 const proofStatus=hasOpenProof?'open':branchDependencies.some(id=>inheritedOpenIds.has(id))?'depends-on-open':'candidate';
 const branchProofIds=branches.map(branch=>branch.resultId).filter(Boolean);
 const scopedOperation={...goalOperation,subgoals:branchResults.map(({branch,child})=>{
  const index=branch.constructor==='inl'?0:1,subgoal=goalOperation.subgoals[index];
  return {...subgoal,contextDelta:subgoal.contextDelta.map(binding=>({...binding,
   id:child.localBindingIds[0],scopeId:child.id
  }))};
 })};
 const step={kind:'cases',source:parsed.source,name:parsed.resultName,type:parsed.type,branches,goalOperation:scopedOperation};
 const caseRow={kind:'cases',name:parsed.resultName,type:parsed.type,raw:parsed.head.raw.trim(),line:parsed.head.line,
  graphId:parentResultId,status:'translated',proofStatus,resolutionStatus:proofStatus==='open'?'open-obligation':proofStatus==='depends-on-open'?'depends-on-open':'candidate-unverified',
  step,goalOperation:scopedOperation,branches,branchDependencies,branchProofIds,dependencies:[sourceBinding.binding.id,...branchDependencies,...branchProofIds]};
 // Names introduced in a branch cannot be reinterpreted as unqualified
 // global rules after closure. Parent bindings retain their original meaning;
 // a fresh parent introduction may deliberately reuse a spelling.
 const parentIds=new Set(resultFrame.bindings.map(binding=>binding.id));
 const expired=new Set(closedNames);
 for(const {result} of branchResults){
  for(const node of graphNodes(result.graph)){
   if(node.name&&!parentIds.has(node.id))expired.add(node.name);
  }
 }
 // A closed name may not occur in the result annotation itself. Resolve
 // scoped free names, not spelling inside a bound quantifier.
 const parentNames=new Set(proofScopeNames(frame));
 function freeClosed(tree){
  if(tree.kind==='free')return expired.has(tree.name)&&!parentNames.has(tree.name)?tree.name:null;
  for(const value of Object.values(tree)){
   if(value&&typeof value==='object'){
    for(const child of Array.isArray(value)?value:[value]){
     const name=freeClosed(child);if(name)return name;
    }
   }
  }
  return null;
 }
 const escaping=freeClosed(compileFormula(parsed.type,{syntax:'lean'}).scoped);
 if(escaping)return incomplete(input,parsed,branchResults,frame,{goal,choices,closedNames:[...expired],openBindings,incompleteContext,
  reason:'A branch-local name cannot occur in the parent result: '+escaping,resolutionStatus:'incompatible-target',
  preserveTail:true,compileSegment,cache});
 let tailResult;
 if(parsed.tail.length){
  tailResult=compileSegment(parsed.tail.map(x=>x.raw).join('\n'),resultFrame,{goal,choices,lineOffset:parsed.tailLineOffset,closedNames:[...expired],openBindings,incompleteContext,cache});
 }else{
  if(goal&&!sameScopedFormula(parsed.type,goal))return incomplete(input,parsed,branchResults,frame,{goal,
   reason:'The case result does not structurally match the enclosing goal; supply a parent continuation.',resolutionStatus:'incompatible-target',cache});
  tailResult={rows:[],steps:[{kind:'conclude',type:goal||null,application:parsed.resultName}],complete:!incompleteContext,
   graph:remapProofGraph(buildDraftGraph(proofScopeNames(resultFrame),proofScopeFacts(resultFrame),[],{goal}),resultFrame),
   openBindings:[],reusedRows:0,remainingGoal:goal};
 }
 const branchRows=branchResults.flatMap(({child,result})=>(result.rows||[]).map(row=>({...row,graphId:row.graphId||scopedLineId(child,row.line)})));
 const tailRows=(tailResult.rows||[]).map(row=>({...row,graphId:row.graphId||scopedLineId(resultFrame,row.line)}));
 const rows=[caseRow,...branchRows,...tailRows].sort((a,b)=>a.line-b.line);
 const graph=remapProofGraph(buildDraftGraph(proofScopeNames(frame),proofScopeFacts(frame),[caseRow,...(tailResult.rows||[])],{goal}),frame);
 const steps=[step,...tailResult.steps];
 const complete=tailResult.complete&&!incompleteContext;
 const reusedRows=branchResults.reduce((total,item)=>total+(item.result?.reusedRows||0),0)+(tailResult.reusedRows||0);
 return {rows,steps,complete,completionKind:complete?'structural-export-ready':'incomplete',leanVerification:'not-run',semanticFidelity:'not-assessed',reusedRows,
  openBindings:tailResult.openBindings||[],remainingGoal:tailResult.remainingGoal,graph,
  term:complete?renderChain(steps):null};
}
