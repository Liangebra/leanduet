// A small structural alternative family for “take an element satisfying P”.
// The shared request is kept separate from its operational readings. A reading
// is admitted only when the current goal or a typed existential premise
// supplies its mathematical justification.
import {compileFormula,sameScopedFormula} from './math-formula.mjs';
import {planGoalOperation,existentialBindings} from './context-extension.mjs';

const identifier="[A-Za-z_][A-Za-z0-9_']{0,63}";
const delimited='(?:\\$[^$\\n]+\\$|\\\\\\([^]*?\\\\\\))';
const restrictionTerm=`(?:${delimited}|${identifier})`;
const sameRestriction=(left,right)=>left==null||right==null?left==null&&right==null:
 sameScopedFormula(left,right,{syntax:'lean'});
function restrictionReferences(restriction,scope,scopeIds,ambiguousNames){
 if(!restriction)return {key:[],dependencies:[],ambiguousName:null};
 const tree=compileFormula(restriction,{syntax:'lean'}).scoped,names=new Set();
 function visit(value){
  if(!value||typeof value!=='object')return;
  if(Array.isArray(value)){value.forEach(visit);return;}
  if(value.kind==='free'&&typeof value.name==='string'){names.add(value.name);return;}
  Object.values(value).forEach(visit);
 }
 visit(tree);
 const ambiguous=new Set(ambiguousNames);
 for(const name of names){
  if(ambiguous.has(name)||scope.filter(candidate=>candidate===name).length>1)
   return {key:[],dependencies:[],ambiguousName:name};
 }
 const key=[],dependencies=[];
 for(const name of [...names].sort()){
  const index=scope.indexOf(name);
  if(index<0)key.push([name,'global:'+name]);
  else{
   const id=scopeIds[index]||'name:'+name;
   key.push([name,id]);dependencies.push(id);
  }
 }
 return {key,dependencies,ambiguousName:null};
}
const explicitSource=(source,scope)=>!source||scope.includes(source);

export function parseElementRequest(raw){
 const english=new RegExp(`^(?:take|choose)\\s+(?:a\\s+|an\\s+)?(?:(arbitrary|any)\\s+)?(?:element\\s+)?(${identifier})(?:\\s*:\\s*(${delimited}))?(?:\\s+in\\s+(${restrictionTerm}))?\\s+(?:satisfying|such\\s+that)\\s+(${delimited})(?:\\s+(?:from|using)\\s+(${identifier}))?\\s*[。.]?$`,'iu');
 const chinese=new RegExp(`^(?:取|选取)(任意|一个)?(?:元素)?\\s*(${identifier})(?:\\s*[:：]\\s*(${delimited}))?(?:\\s*∈\\s*(${restrictionTerm}))?\\s*(?:满足|使得)\\s*(${delimited})(?:\\s*(?:从|由)\\s*(${identifier}))?\\s*[。.]?$`,'u');
 let match=english.exec(raw.trim()),language='en';
 if(!match){match=chinese.exec(raw.trim());language='zh';}
 if(!match)return null;
 const [,quantifier,name,typeText,restrictionText,propertyText,source]=match;
 try{
  const type=typeText?compileFormula(typeText,{syntax:'lean'}).lean:null;
  const restriction=restrictionText?compileFormula(restrictionText,{syntax:'lean'}).lean:null;
  const property=compileFormula(propertyText,{syntax:'lean'}).lean;
  if(compileFormula(name).ast.kind!=='id')return null;
  return {kind:'element-request',raw,name,type,restriction,property,source:source||null,
   arbitrary:/^(?:arbitrary|any|任意)$/iu.test(quantifier||''),language};
 }catch{return null;}
}

function compatibleType(requested,actual){
 return !requested||sameScopedFormula(requested,actual,{syntax:'lean'});
}
function renderType(ast){
 if(ast.kind==='id'||ast.kind==='number')return ast.value;
 if(ast.kind==='call')return '('+[renderType(ast.fn),...ast.args.map(renderType)].join(' ')+')';
 return null;
}
function knownRestrictionCarrier(restriction,facts){
 if(!restriction||!facts.has(restriction))return null;
 try{
  const ast=compileFormula(facts.get(restriction),{syntax:'lean'}).ast;
  if(ast.kind!=='call'||ast.args.length!==1||ast.fn?.kind!=='id'||
     !['Set','List','Finset','Multiset'].includes(ast.fn.value))return null;
  const carrier=renderType(ast.args[0]);
  return carrier?compileFormula(carrier,{syntax:'lean'}).lean:null;
 }catch{return null;}
}

/**
 * Build a finite family of operation candidates. A universal reading consumes
 * a matching ∀ goal; an existential reading consumes a matching, visible,
 * typed ∃ premise. A bounded quantifier also requires its set restriction to
 * agree and an explicit element type, because the browser does not elaborate
 * the set's carrier. No local definition, subtype coercion, or witness search
 * is inferred by this function.
 */
export function elementInterpretationCandidates(request,{goal=null,scope=[],facts=new Map(),scopeIds=[],reservedNames=[],ambiguousNames=[],budget=64,limit=8}={}){
 if(!request||request.kind!=='element-request')return {candidates:[],status:'no-supported-match',explored:0};
 const names=[...new Set(scope)];
 if(scope.length>budget)return {candidates:[],status:'budget-exhausted',explored:budget,
  reason:'Element interpretation exceeded its finite context scan budget; narrow the visible context.'};
 const restrictionRefs=restrictionReferences(request.restriction,scope,scopeIds,ambiguousNames);
 if(restrictionRefs.ambiguousName)return {candidates:[],status:'ambiguous-context',explored:names.length,
  reason:`The set restriction refers to ambiguous local object ${restrictionRefs.ambiguousName}; qualify or rename it before choosing an interpretation.`};
 const carrier=knownRestrictionCarrier(request.restriction,facts);
 if(request.restriction&&request.type&&carrier&&!compatibleType(request.type,carrier))return {
  candidates:[],status:'incompatible-type',explored:names.length,expectedType:carrier,
  reason:`The annotated element type ${request.type} does not match the known carrier ${carrier} of ${request.restriction}.`};
 const candidates=[];
 const add=candidate=>candidates.push(candidate);
 if(!request.source&&goal){
  try{
   const operation=planGoalOperation(goal,{kind:'introduce',name:request.name,type:request.type});
   const binding=operation.subgoals[0].contextDelta[0];
   const property=operation.focusProperty||operation.subgoals[0].goal;
   const restriction=operation.restrictionSet||null;
   if(!scope.includes(request.name)&&compatibleType(request.type,binding.type)&&
      sameRestriction(request.restriction,restriction)&&sameScopedFormula(request.property,property,{syntax:'lean'})){
    const key=JSON.stringify([request.name,binding.type,restriction,property,restrictionRefs.key]);
    add({kind:'introduce',name:request.name,type:binding.type,term:'introduce '+request.name,
     schema:restriction?'arbitrary element introduction under a set restriction':'universal-variable introduction',
     choice:'element:forall:'+key,operation:'universal-introduction',restrictionDependencies:restrictionRefs.dependencies,
     ...(restriction?{restrictionSet:restriction,requiredCondition:'('+request.name+' ∈ '+restriction+')'}:{})});
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
   try{binding=existentialBindings(sourceType,{name:request.name,type:request.type});}catch{continue;}
   if(!compatibleType(request.type,binding.type)||!sameRestriction(request.restriction,binding.restrictionSet||null)||
      !sameScopedFormula(request.property,binding.propertyType,{syntax:'lean'}))continue;
   const sourceId=scopeIds[index]||'name:'+source;
   let evidenceName='h_'+request.name;
   let suffix=0;
   while(new Set([...scope,...reservedNames,request.name]).has(evidenceName))evidenceName='h_'+request.name+'_'+(++suffix);
   const key=JSON.stringify([sourceId,request.name,binding.type,binding.restrictionSet||null,binding.propertyType,restrictionRefs.key]);
   add({kind:'obtain',name:request.name,type:binding.type,source,evidenceName,
    evidenceType:binding.evidenceType,sourceId,premises:[source],term:`obtain ${request.name}, ${evidenceName} from ${source}`,
    schema:binding.restrictionSet?'restricted existential witness extraction':'existential witness extraction',
    choice:'element:exists:'+key,operation:'existential-elimination',
    restrictionDependencies:restrictionRefs.dependencies,...(binding.restrictionSet?{restrictionSet:binding.restrictionSet}:{})});
  }
 }
 if(candidates.length>limit)return {candidates:[],status:'budget-exhausted',explored:names.length,
  reason:'Element interpretation produced more candidates than the display budget; specify a source or mark the element arbitrary.'};
 if(candidates.length)return {candidates,status:candidates.length===1?'unique':'ambiguous',explored:names.length};
 const sourceNeedsContext=request.source&&(!scope.includes(request.source)||typeof facts.get(request.source)!=='string');
 const missingPotentialContext=!request.source&&scope.some(name=>typeof facts.get(name)!=='string');
 if(request.restriction&&!request.type)return {candidates:[],status:'needs-type-annotation',explored:names.length,
  reason:'A set-restricted element request needs an explicit element type; the browser does not infer the carrier type of a set.'};
 return {candidates,status:sourceNeedsContext||missingPotentialContext||!goal&&!scope.length?'needs-context':'no-supported-match',explored:names.length,
  reason:sourceNeedsContext?'The named source is not a visible typed local premise.':
   missingPotentialContext?'Some visible local objects do not have a known type, so a witness reading cannot be ruled out.':
   'No matching universal goal or typed existential premise supports this interpretation.'};
}
