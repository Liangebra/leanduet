// A small structural alternative family for “take an element satisfying P”.
// The shared request is kept separate from its operational readings. A reading
// is admitted only when the current goal or a typed existential premise
// supplies its mathematical justification.
import {compileFormula,sameScopedFormula} from './math-formula.mjs';
import {planGoalOperation,existentialBindings} from './context-extension.mjs';

const identifier='[A-Za-z_][A-Za-z0-9_\']{0,63}';
const delimited='(?:\\$[^$\\n]+\\$|\\\\\\([^]*?\\\\\\))';
const explicitSource=(source,scope)=>!source||scope.includes(source);

export function parseElementRequest(raw){
 const english=new RegExp(`^(?:take|choose)\\s+(?:a\\s+|an\\s+)?(?:(arbitrary|any)\\s+)?(?:element\\s+)?(${identifier})(?:\\s*:\\s*(${delimited}))?\\s+(?:satisfying|such\\s+that)\\s+(${delimited})(?:\\s+(?:from|using)\\s+(${identifier}))?\\s*[。.]?$`,'iu');
 const chinese=new RegExp(`^(?:取|选取)(任意|一个)?(?:元素)?\\s*(${identifier})(?:\\s*[:：]\\s*(${delimited}))?\\s*(?:满足|使得)\\s*(${delimited})(?:\\s*(?:从|由)\\s*(${identifier}))?\\s*[。.]?$`,'u');
 let match=english.exec(raw.trim()),language='en';
 if(!match){match=chinese.exec(raw.trim());language='zh';}
 if(!match)return null;
 const [,quantifier,name,typeText,propertyText,source]=match;
 try{
  const type=typeText?compileFormula(typeText,{syntax:'lean'}).lean:null;
  const property=compileFormula(propertyText,{syntax:'lean'}).lean;
  if(typeText&&!type) return null;
  if(compileFormula(name).ast.kind!=='id')return null;
  return {kind:'element-request',raw,name,type,property,source:source||null,
   arbitrary:/^(?:arbitrary|any|任意)$/iu.test(quantifier||''),language};
 }catch{return null;}
}

function compatibleType(requested,actual){
 return !requested||sameScopedFormula(requested,actual,{syntax:'lean'});
}

/**
 * Build a finite family of operation candidates. A universal reading consumes
 * a matching ∀ goal; an existential reading consumes a matching, visible,
 * typed ∃ premise. No local definition, subtype coercion, or witness search is
 * inferred by this function.
 */
export function elementInterpretationCandidates(request,{goal=null,scope=[],facts=new Map(),scopeIds=[],reservedNames=[],budget=64,limit=8}={}){
 if(!request||request.kind!=='element-request')return {candidates:[],status:'no-supported-match',explored:0};
 const names=[...new Set(scope)];
 if(scope.length>budget)return {candidates:[],status:'budget-exhausted',explored:budget,
  reason:'Element interpretation exceeded its finite context scan budget; narrow the visible context.'};
 const candidates=[];
 const add=candidate=>candidates.push(candidate);
 if(!request.source&&goal){
  try{
   const operation=planGoalOperation(goal,{kind:'introduce',name:request.name});
   const binding=operation.subgoals[0].contextDelta[0];
   if(!scope.includes(request.name)&&compatibleType(request.type,binding.type)&&sameScopedFormula(request.property,operation.subgoals[0].goal,{syntax:'lean'})){
    const key=JSON.stringify([request.name,binding.type,operation.subgoals[0].goal]);
    add({kind:'introduce',name:request.name,type:binding.type,term:'introduce '+request.name,
     schema:'universal-variable introduction',choice:'element:forall:'+key,operation:'universal-introduction'});
   }
  }catch{}
 }
 if(!request.arbitrary){
  const visibleCounts=new Map();for(const name of scope)visibleCounts.set(name,(visibleCounts.get(name)||0)+1);
  for(let index=0;index<scope.length;index++){
   const source=scope[index];
   if(visibleCounts.get(source)!==1||!explicitSource(request.source,scope)||request.source&&request.source!==source||scope.includes(request.name))continue;
   const sourceType=facts.get(source);
   if(typeof sourceType!=='string')continue;
   let binding;
   try{binding=existentialBindings(sourceType,{name:request.name});}catch{continue;}
   if(!compatibleType(request.type,binding.type)||!sameScopedFormula(request.property,binding.evidenceType,{syntax:'lean'}))continue;
   const sourceId=scopeIds[index]||'name:'+source;
   let evidenceName='h_'+request.name;
   let suffix=0;
   while(new Set([...scope,...reservedNames,request.name]).has(evidenceName))evidenceName='h_'+request.name+'_'+(++suffix);
   const key=JSON.stringify([sourceId,request.name,binding.type,binding.evidenceType]);
   add({kind:'obtain',name:request.name,type:binding.type,source,evidenceName,
    evidenceType:binding.evidenceType,sourceId,premises:[source],term:`obtain ${request.name}, ${evidenceName} from ${source}`,
    schema:'existential witness extraction',choice:'element:exists:'+key,operation:'existential-elimination'});
  }
 }
 if(candidates.length>limit)return {candidates:[],status:'budget-exhausted',explored:names.length,
  reason:'Element interpretation produced more candidates than the display budget; specify a source or mark the element arbitrary.'};
 if(candidates.length)return {candidates,status:candidates.length===1?'unique':'ambiguous',explored:names.length};
 const sourceNeedsContext=request.source&&(!scope.includes(request.source)||typeof facts.get(request.source)!=='string');
 const missingPotentialContext=!request.source&&scope.some(name=>typeof facts.get(name)!=='string');
 return {candidates,status:sourceNeedsContext||missingPotentialContext||!goal&&!scope.length?'needs-context':'no-supported-match',explored:names.length,
  reason:sourceNeedsContext?'The named source is not a visible typed local premise.':
   missingPotentialContext?'Some visible local objects do not have a known type, so a witness reading cannot be ruled out.':
   'No matching universal goal or typed existential premise supports this interpretation.'};
}
