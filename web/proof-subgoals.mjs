import {buildDraftGraph} from './draft-graph.mjs';
import {compileFormula} from './math-formula.mjs';
import {planGoalOperation} from './context-extension.mjs';
import {closeProofScope,extendProofScope,forkGoalScope,proofDraftClosesGoal,proofScopeFacts,proofScopeNames,resolveProofName} from './proof-scope.mjs';
import {renderChain} from './proof-chain.mjs';
import {graphNodes,proofContextDependencies,proofResultId,remapProofGraph} from './case-split.mjs';

const operations=[
 {kind:'conjunction-introduction',header:/^(?:split conjunction|prove conjunction|分解合取目标|证明合取目标)$/iu,
  subgoals:[{id:'first',heading:/^(?:first goal|第一子目标)$/iu},{id:'second',heading:/^(?:second goal|第二子目标)$/iu}]},
 {kind:'iff-introduction',header:/^(?:prove equivalence|证明等价命题)$/iu,
  subgoals:[{id:'forward',heading:/^(?:forward direction|正向)$/iu},{id:'reverse',heading:/^(?:reverse direction|反向)$/iu}]},
 {kind:'existential-introduction',header:/^(?:construct witness|choose witness|构造见证|选取见证)\s+([A-Za-z_][A-Za-z0-9_']{0,63})$/iu,
  subgoals:[{id:'witness-property',heading:/^(?:witness property|见证性质)$/iu}]}
];

const lemmaName='[A-Za-z_][A-Za-z0-9_\']{0,63}';
const lemmaFormula='(?:\\$[^$\\n]+\\$|\\\\\\([^]*?\\\\\\))';
const localLemmaPatterns=[
 new RegExp('^(?:local lemma|prove lemma)\\s+('+lemmaName+')\\s*[:：]\\s*('+lemmaFormula+')$','iu'),
 new RegExp('^(?:局部引理|证明引理)\\s*('+lemmaName+')\\s*[:：]\\s*('+lemmaFormula+')$','u')
];

/** Parse a deliberately explicit local claim header, separate from goal constructors. */
export function localLemmaHeader(text){
 const first=String(text||'').split(/\r?\n/).find(line=>line.trim());
 if(!first)return null;
 for(const pattern of localLemmaPatterns){
  const match=pattern.exec(first.trim());
  if(match){
   try{return {kind:'local-lemma',name:match[1],type:compileFormula(match[2],{syntax:'lean'}).lean};}
   catch{return null;}
  }
 }
 return null;
}

export function goalOperationHeader(text){
 const first=String(text||'').split(/\r?\n/).find(line=>line.trim());
 if(!first)return null;
 for(const operation of operations){
  const match=operation.header.exec(first.trim());
  if(match)return {kind:operation.kind,witness:match[1]||null,subgoals:operation.subgoals};
 }
 return null;
}
export function hasGoalOperationHeader(text){return !!goalOperationHeader(text);}
export function hasConjunctionGoalHeader(text){return goalOperationHeader(text)?.kind==='conjunction-introduction';}

function parseBlock(input,lineOffset){
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const all=String(input).split(/\r?\n/).map((raw,index)=>({raw,index,line:lineOffset+index+1,indent:(/^ */.exec(raw)||[''])[0].length}));
 if(all.some(line=>line.raw.includes('\t')))throw Error('Use spaces to indent subgoal proofs.');
 const significant=all.filter(line=>line.raw.trim());
 if(significant.length>64)throw Error('A nested proof draft may contain at most 64 nonblank lines.');
 const operation=significant.length?goalOperationHeader(significant[0].raw.trim()):null;
 if(!operation||significant[0].indent!==0)
  throw Error('Start a goal operation at the beginning of its proof segment.');
 const head=significant[0],subgoals=[];let pos=1;
 for(let index=0;index<operation.subgoals.length;index++){
  const spec=operation.subgoals[index];
  const heading=significant[pos];
  if(!heading||heading.indent!==2||!spec.heading.test(heading.raw.trim()))
   throw Error('Write the operation’s goal headings in the displayed order, each indented by two spaces.');
  pos++;
  const body=[];
  while(pos<significant.length){
   const next=significant[pos];
   if(next.indent===2&&operation.subgoals.some(candidate=>candidate.heading.test(next.raw.trim())))break;
   if(next.indent===0)throw Error('A goal operation closes the current proof; no root-level line may follow it.');
   if(next.indent<4)throw Error('Indent each subgoal proof by four spaces.');
   body.push(next);pos++;
  }
  if(!body.length)throw Error('Each child goal needs a proof draft.');
  const first=body[0].index,last=body.at(-1).index;
  const sourceLines=all.slice(first,last+1).map(line=>line.raw.trim()?line.raw.slice(4):'');
  subgoals.push({id:spec.id,line:heading.line,sourceLines,bodyLineOffset:all[first].line-1});
 }
 if(pos<significant.length)throw Error('A goal operation has exactly the displayed ordered subgoals.');
 return {...operation,head,subgoals};
}

function contextDependencyClosure(frame,dependencies,line){
 if(!dependencies.length)return [];
 const names=dependencies.map(id=>frame.bindings.find(binding=>binding.id===id)?.name).filter(Boolean);
 if(names.length!==dependencies.length)throw Error('A goal operation depends on an identity outside its parent context.');
 const probe={kind:'conclude',line,type:null,dependencies,
  step:{kind:'conclude',application:names.join(' ')}};
 const graph=remapProofGraph(buildDraftGraph(proofScopeNames(frame),proofScopeFacts(frame),[probe]),frame);
 return proofContextDependencies(graph);
}

/** Compile a bounded goal constructor by checking each child in an isolated scope. */
export function compileGoalOperationProgram(input,frame,{goal=null,choices=new Map(),lineOffset=0,closedNames=[],openBindings=[],incompleteContext=false,cache=null}={},compileSegment,parseDraftLine){
 if((frame.id.match(/\/(?:case|subgoal):/g)||[]).length>=8)throw Error('Nested proof scopes are limited to eight levels.');
 const target=goal||frame.goalText;
 const parsed=parseBlock(input,lineOffset),parentIds=new Set(frame.bindings.map(binding=>binding.id));
 let witnessBinding=null;
 if(parsed.kind==='existential-introduction'){
  witnessBinding=resolveProofName(frame,parsed.witness);
  if(witnessBinding.status!=='resolved'||typeof witnessBinding.binding.type!=='string')
   throw Error('Existential construction needs a uniquely visible typed local witness.');
 }
 const operation=planGoalOperation(target,{kind:parsed.kind,witness:parsed.witness,
  witnessType:witnessBinding?.binding.type,witnessId:witnessBinding?.binding.id});
 const reserved=parsed.subgoals.map(subgoal=>{
  const names=new Set();
  for(const raw of subgoal.sourceLines){
   if(!raw.trim()||!parseDraftLine)continue;
   try{const draft=parseDraftLine(raw);for(const name of [draft.name,draft.evidenceName])if(name)names.add(name);}catch{}
  }
  return names;
 });
 const results=[];let firstOpen=null;
 for(let index=0;index<parsed.subgoals.length;index++){
  const subgoal=parsed.subgoals[index],plan=operation.subgoals[index],childId=frame.id+'/subgoal:'+parsed.head.line+':'+subgoal.id;
  const child=forkGoalScope(frame,{id:childId,goal:plan.goal});
  const siblingNames=reserved.flatMap((names,siblingIndex)=>siblingIndex===index?[]:[...names]);
  const result=compileSegment(subgoal.sourceLines.join('\n'),child,{goal:plan.goal,choices,lineOffset:subgoal.bodyLineOffset,
   closedNames:[...new Set([...closedNames,...siblingNames])],openBindings,cache});
  let closed=null;
  if(result.complete){
   const conclusion=result.steps.at(-1);
   if(!['conclude','and-intro','iff-intro','exists-intro'].includes(conclusion?.kind)){
    firstOpen??={line:subgoal.line,reason:'A child proof did not end with a conclusion.'};
   }else{
    const localIds=graphNodes(result.graph).filter(node=>!parentIds.has(node.id)&&node.kind!=='context').map(node=>node.id);
    closed=closeProofScope(frame,child,{proofType:plan.goal,dependencies:proofContextDependencies(result.graph),localIds});
   }
  }else{
   const failed=result.rows.find(row=>row.status==='unresolved');
   firstOpen??={line:failed?.line||subgoal.line,reason:failed?.reason||'A conjunction subgoal remains open.'};
  }
  const status=proofDraftClosesGoal(result)&&closed?'complete':result.complete?'open-obligation':'open';
  results.push({plan,child,result,closed,id:childId,status,resultId:proofResultId(result.graph),dependencies:closed?.dependencies||[]});
 }
 const inheritedOpenIds=new Set(openBindings.map(name=>frame.bindings.filter(binding=>binding.name===name).at(-1)?.id).filter(Boolean));
 const operationDependencies=contextDependencyClosure(frame,witnessBinding?[witnessBinding.binding.id]:[],parsed.head.line);
 const dependencies=[...new Set([...operationDependencies,...results.flatMap(result=>result.dependencies)])];
 const structurallyComplete=results.every(result=>result.result.complete&&result.closed)&&!incompleteContext;
 const hasOpenProof=results.some(result=>result.status!=='complete');
 const proofStatus=!structurallyComplete?'open':hasOpenProof?'open':dependencies.some(id=>inheritedOpenIds.has(id))?'depends-on-open':'candidate';
 const subgoalRecords=results.map(({plan,child,result,status,resultId,dependencies:returned})=>({
  id:child.id,key:plan.id,kind:'subgoal',goal:plan.goal,resultId,dependencies:returned,graph:result.graph,status
 }));
 const stepKind=parsed.kind==='conjunction-introduction'?'and-intro':parsed.kind==='iff-introduction'?'iff-intro':'exists-intro';
 const step=!structurallyComplete?null:{kind:stepKind,type:target,witness:parsed.witness,goalOperation:operation,
  subgoals:results.map(({plan,result})=>({id:plan.id,goal:plan.goal,steps:result.steps}))};
 const scopedOperation={...operation,subgoals:results.map(({plan,child})=>({...plan,scopeId:child.id}))};
 if(step)step.goalOperation=scopedOperation;
 const row={kind:stepKind,raw:parsed.head.raw.trim(),line:parsed.head.line,
  graphId:frame.id==='root'?'line:'+parsed.head.line:frame.id+'/line:'+parsed.head.line,
  type:target,status:structurallyComplete?'translated':'unresolved',proofStatus,
 resolutionStatus:proofStatus==='open'?'open-obligation':proofStatus==='depends-on-open'?'depends-on-open':'candidate-unverified',
  reason:firstOpen?(firstOpen.line?'Subgoal line '+firstOpen.line+': ':'')+firstOpen.reason:undefined,
  goalOperation:scopedOperation,subgoals:subgoalRecords,dependencies:[...dependencies,...subgoalRecords.map(item=>item.resultId).filter(Boolean)],step};
 const graph=remapProofGraph(buildDraftGraph(proofScopeNames(frame),proofScopeFacts(frame),[row],{goal:target}),frame);
 const childRows=results.flatMap(({result})=>result.rows||[]);
 const rows=[row,...childRows].sort((left,right)=>left.line-right.line);
 const complete=structurallyComplete;
 const resultStep=complete?step:null;
 return {rows,steps:resultStep?[resultStep]:[],complete,completionKind:complete?'structural-export-ready':'incomplete',
  leanVerification:'not-run',semanticFidelity:'not-assessed',reusedRows:results.reduce((sum,item)=>sum+(item.result.reusedRows||0),0),
  // Child-local open declarations cannot be named after this operation closes.
  // Any dependency on them is already reflected in the child's proof status.
  openBindings:[...new Set(openBindings)],
  remainingGoal:target,graph,term:complete?renderChain([resultStep]):null};
}

function parseLocalLemmaBlock(input,lineOffset){
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const all=String(input).split(/\r?\n/).map((raw,index)=>({raw,index,line:lineOffset+index+1,indent:(/^ */.exec(raw)||[''])[0].length}));
 if(all.some(line=>line.raw.includes('\t')))throw Error('Use spaces to indent a local lemma proof.');
 const significant=all.filter(line=>line.raw.trim());
 if(significant.length>64)throw Error('A local lemma proof may contain at most 64 nonblank lines.');
 const head=significant[0],operation=head&&localLemmaHeader(head.raw.trim());
 if(!operation||head.indent!==0)throw Error('Start a local lemma with “local lemma h : $P$”.');
 const heading=significant[1];
 if(!heading||heading.indent!==2||! /^(?:proof|证明)$/iu.test(heading.raw.trim()))
  throw Error('Add an indented “proof” heading below the local lemma.');
 let bodyFirst=null,tailStart=null;
 for(const line of significant.slice(2)){
  if(line.indent===0){tailStart=line.index;break;}
  if(line.indent<4)throw Error('Indent local lemma proof steps by four spaces.');
  if(bodyFirst===null)bodyFirst=line.index;
 }
 const bodyEnd=tailStart===null?all.length:tailStart;
 const body=bodyFirst===null?[]:all.slice(bodyFirst,bodyEnd).map(line=>line.raw.trim()?line.raw.slice(4):'');
 const tail=tailStart===null?[]:all.slice(tailStart).map(line=>line.raw);
 const bodyLineOffset=bodyFirst===null?(tailStart===null?lineOffset+all.length:all[tailStart].line-1):all[bodyFirst].line-1;
 return {operation,head,body,bodyLineOffset,tail,
  tailLineOffset:tailStart===null?lineOffset+all.length:all[tailStart].line-1};
}

/**
 * Prove one named claim in an isolated child scope, then return only that
 * proposition to the parent context. Child declarations expire at closure.
 */
export function compileLocalLemmaProgram(input,frame,{goal=null,choices=new Map(),lineOffset=0,closedNames=[],openBindings=[],incompleteContext=false,cache=null}={},compileSegment){
 if((frame.id.match(/\/(?:case|subgoal|lemma):/g)||[]).length>=8)
  throw Error('Nested proof scopes are limited to eight levels.');
 const parsed=parseLocalLemmaBlock(input,lineOffset),{name,type}=parsed.operation;
 if(resolveProofName(frame,name).status!=='missing')throw Error('A local lemma name must be fresh in its parent scope.');
 const scopedType=compileFormula(type,{syntax:'lean'}).scoped;
 function refersToOwnName(term){
  if(!term||typeof term!=='object')return false;
  if(term.kind==='free'&&term.name===name)return true;
  return Object.values(term).some(value=>Array.isArray(value)?value.some(refersToOwnName):refersToOwnName(value));
 }
 if(refersToOwnName(scopedType))throw Error('A local lemma statement cannot refer to the name it is introducing.');
 const headId=frame.id==='root'?'line:'+parsed.head.line:frame.id+'/line:'+parsed.head.line;
 const childId=frame.id+'/lemma:'+parsed.head.line;
 const child=forkGoalScope(frame,{id:childId,goal:type});
 const childResult=compileSegment(parsed.body.join('\n'),child,{goal:type,choices,lineOffset:parsed.bodyLineOffset,
  closedNames,openBindings,incompleteContext,cache});
 const structurallyRenderable=childResult.complete;
 // A child proof may be structurally closed while depending on an upstream
 // open object. That dependency must flow through the returned lemma, but it
 // does not erase the proof's local conclusion or its Lean candidate.
 const proofClosed=structurallyRenderable&&!childResult.rows.some(item=>
  item.status==='unresolved'||item.proofStatus==='open'||item.step?.application==='?');
 const parentIds=new Set(frame.bindings.map(binding=>binding.id));
 const dependencies=proofContextDependencies(childResult.graph||{}).filter(id=>parentIds.has(id));
 let closure=null;
 if(structurallyRenderable){
  const localIds=graphNodes(childResult.graph).filter(node=>!parentIds.has(node.id)).map(node=>node.id);
  closure=closeProofScope(frame,child,{proofType:type,dependencies:proofContextDependencies(childResult.graph),localIds});
 }
 const returnedDependencies=closure?.dependencies||dependencies;
 const openIds=new Set(openBindings.flatMap(bindingName=>frame.bindings.filter(binding=>binding.name===bindingName).map(binding=>binding.id)));
 const dependsOnOpen=returnedDependencies.some(id=>openIds.has(id));
 const proofStatus=!structurallyRenderable?'open':!proofClosed?'open':dependsOnOpen?'depends-on-open':'candidate';
 const resultId=proofResultId(childResult.graph);
 const subgoalStatus=proofClosed?(dependsOnOpen?'depends-on-open':'complete'):
  structurallyRenderable?'open-obligation':'open';
 const operation={kind:'local-lemma',name,type,parentGoal:goal||frame.goalText,logic:'intuitionistic',
  subgoal:{id:'proof',goal:type,scopeId:child.id},closure:{kind:'local-binding',name}};
 const row={kind:'local-lemma',name,type,raw:parsed.head.raw.trim(),line:parsed.head.line,
  graphId:headId,status:structurallyRenderable?'translated':'unresolved',proofStatus,
  resolutionStatus:proofStatus==='candidate'?'candidate-unverified':proofStatus==='depends-on-open'?'depends-on-open':'open-obligation',
  reason:structurallyRenderable?undefined:'The local lemma proof is incomplete; its parent continuation remains provisional.',
  goalOperation:operation,subgoals:[{id:child.id,key:'proof',kind:'subgoal',goal:type,resultId,
   dependencies:returnedDependencies,graph:childResult.graph,status:subgoalStatus}],
  dependencies:[...returnedDependencies,...(resultId?[resultId]:[])]};
 const step={kind:'local-lemma',name,type,dependencies:returnedDependencies,
  subgoals:[{id:'proof',goal:type,steps:childResult.steps}]};
 row.step=step;
 const lemmaScope=extendProofScope(frame,{id:headId,name,type,kind:'local-lemma'});
 const tailOpen=[...new Set([...openBindings,...(proofStatus==='candidate'?[]:[name])])];
 // Every declaration introduced below the lemma belongs to its child proof,
 // including declarations in nested branches. Remember only their spellings
 // after the child closes so a later parent expression cannot accidentally
 // resolve to an out-of-scope object with the same display name.
 const expiredNames=graphNodes(childResult.graph).filter(node=>node.kind!=='context'&&node.name)
  .map(node=>node.name);
 const tailResult=compileSegment(parsed.tail.join('\n'),lemmaScope,{goal,choices,lineOffset:parsed.tailLineOffset,
  closedNames:[...new Set([...closedNames,...expiredNames])],incompleteContext:!!incompleteContext||!structurallyRenderable||!proofClosed,
  openBindings:tailOpen,cache});
 const graph=remapProofGraph(buildDraftGraph(proofScopeNames(frame),proofScopeFacts(frame),[row],{goal:goal||frame.goalText}),frame);
 const childRows=(childResult.rows||[]).map(item=>({...item,graphId:item.graphId||child.id+'/line:'+item.line}));
 const nodes=[...graph.nodes],seen=new Set(nodes.map(node=>node.id));
 for(const node of tailResult.graph.nodes)if(!seen.has(node.id)){nodes.push(node);seen.add(node.id);}
 const groups=new Map([...(graph.constraintGroups||[]),...(tailResult.graph.constraintGroups||[])].map(group=>[group.id,group]));
 const rows=[row,...childRows,...(tailResult.rows||[])].sort((left,right)=>left.line-right.line);
 const complete=tailResult.complete&&!rows.some(item=>item.status==='unresolved');
 const steps=[step,...(tailResult.steps||[])];
 return {...tailResult,rows,steps,complete,completionKind:complete?'structural-export-ready':'incomplete',
  reusedRows:(childResult.reusedRows||0)+(tailResult.reusedRows||0),
  openBindings:[...new Set([...(proofClosed?openBindings:tailOpen),...(tailResult.openBindings||[])])],
  graph:{...tailResult.graph,nodes,constraintGroups:[...groups.values()]},
  term:complete?renderChain(steps):null};
}

export function compileConjunctionGoal(...args){return compileGoalOperationProgram(...args);}
