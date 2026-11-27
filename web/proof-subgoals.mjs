import {buildDraftGraph} from './draft-graph.mjs';
import {planGoalOperation} from './context-extension.mjs';
import {closeProofScope,forkGoalScope,proofDraftClosesGoal,proofScopeFacts,proofScopeNames} from './proof-scope.mjs';
import {renderChain} from './proof-chain.mjs';
import {graphNodes,proofContextDependencies,proofResultId,remapProofGraph} from './case-split.mjs';

const header=/^(?:split conjunction|prove conjunction|分解合取目标|证明合取目标)$/iu;
const headings=[/^(?:first goal|第一子目标)$/iu,/^(?:second goal|第二子目标)$/iu];

export function hasConjunctionGoalHeader(text){
 const first=String(text||'').split(/\r?\n/).find(line=>line.trim());
 return !!first&&header.test(first.trim());
}

function parseBlock(input,lineOffset){
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const all=String(input).split(/\r?\n/).map((raw,index)=>({raw,index,line:lineOffset+index+1,indent:(/^ */.exec(raw)||[''])[0].length}));
 if(all.some(line=>line.raw.includes('\t')))throw Error('Use spaces to indent subgoal proofs.');
 const significant=all.filter(line=>line.raw.trim());
 if(significant.length>64)throw Error('A nested proof draft may contain at most 64 nonblank lines.');
 if(!significant.length||significant[0].indent!==0||!header.test(significant[0].raw.trim()))
  throw Error('Start a conjunction proof with “split conjunction”.');
 const head=significant[0],subgoals=[];let pos=1;
 for(let index=0;index<2;index++){
  const heading=significant[pos];
  if(!heading||heading.indent!==2||!headings[index].test(heading.raw.trim()))
   throw Error('Write “first goal” and “second goal” in that order, each indented by two spaces.');
  pos++;
  const body=[];
  while(pos<significant.length){
   const next=significant[pos];
   if(next.indent===2&&headings.some(pattern=>pattern.test(next.raw.trim())))break;
   if(next.indent===0)throw Error('A conjunction goal split closes the current proof; no root-level line may follow it.');
   if(next.indent<4)throw Error('Indent each subgoal proof by four spaces.');
   body.push(next);pos++;
  }
  if(!body.length)throw Error('Each conjunction subgoal needs a proof draft.');
  const first=body[0].index,last=body.at(-1).index;
  const sourceLines=all.slice(first,last+1).map(line=>line.raw.trim()?line.raw.slice(4):'');
  subgoals.push({id:index===0?'first':'second',line:heading.line,sourceLines,bodyLineOffset:all[first].line-1});
 }
 if(pos<significant.length)throw Error('A conjunction proof has exactly two ordered subgoals.');
 return {head,subgoals};
}

/** Prove a conjunction by checking two independent child goals in sibling scopes. */
export function compileConjunctionGoal(input,frame,{goal=null,choices=new Map(),lineOffset=0,closedNames=[],openBindings=[],incompleteContext=false,cache=null}={},compileSegment,parseDraftLine){
 if((frame.id.match(/\/(?:case|subgoal):/g)||[]).length>=8)throw Error('Nested proof scopes are limited to eight levels.');
 const target=goal||frame.goalText;
 const operation=planGoalOperation(target,{kind:'conjunction-introduction'});
 const parsed=parseBlock(input,lineOffset),parentIds=new Set(frame.bindings.map(binding=>binding.id));
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
   if(!['conclude','and-intro'].includes(conclusion?.kind)){
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
 const dependencies=[...new Set(results.flatMap(result=>result.dependencies))];
 const structurallyComplete=results.every(result=>result.result.complete&&result.closed)&&!incompleteContext;
 const hasOpenProof=results.some(result=>result.status!=='complete');
 const proofStatus=!structurallyComplete?'open':hasOpenProof?'open':dependencies.some(id=>inheritedOpenIds.has(id))?'depends-on-open':'candidate';
 const subgoalRecords=results.map(({plan,child,result,status,resultId,dependencies:returned})=>({
  id:child.id,key:plan.id,kind:'subgoal',goal:plan.goal,resultId,dependencies:returned,graph:result.graph,status
 }));
 const step=!structurallyComplete?null:{kind:'and-intro',type:target,goalOperation:operation,
  subgoals:results.map(({plan,result})=>({id:plan.id,goal:plan.goal,steps:result.steps}))};
 const scopedOperation={...operation,subgoals:results.map(({plan,child})=>({...plan,scopeId:child.id}))};
 if(step)step.goalOperation=scopedOperation;
 const row={kind:'and-intro',raw:parsed.head.raw.trim(),line:parsed.head.line,
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
