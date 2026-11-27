import {compileFormula,sameScopedFormula} from './math-formula.mjs';
import {buildDraftGraph} from './draft-graph.mjs';
import {planGoalOperation,existentialBindings} from './context-extension.mjs';
import {constrainPropositions,candidateChoice} from './proposition-constraints.mjs';
import {discourseFrame,discourseCandidates} from './discourse.mjs';
import {parseRuleIntent} from './rule-intent.mjs';
import {renderChain} from './proof-chain.mjs';
import {premiseFrame,contextCandidates,formulaPremiseSentence,citationCandidates,implicitCandidates,structuralRules} from './context-grammar.mjs';
import {compileCaseProgram,hasCaseSplitHeader,remapProofGraph} from './case-split.mjs';
import {compileConjunctionGoal,hasConjunctionGoalHeader} from './proof-subgoals.mjs';
import {extendProofScope,proofScopeFacts,proofScopeNames,rootProofScope} from './proof-scope.mjs';
const marker=/^(?:(?:therefore|hence|thus|clearly|obviously|indeed|then)(?:\s*[,，:：]\s*|\s+)|(?:因此|从而|于是|显然|事实上|故|则)[，、：:\s]*)/iu;
const formulaPattern=/\$[^$\n]+\$|\\\([^]*?\\\)|\\\[[^]*?\\\]/g;
const namePattern=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
const ruleGlueWords=new Set(['using','from','by','with','and','or','the','a']);
const candidateResolution=proofStatus=>proofStatus==='candidate'?'candidate-unverified':proofStatus==='depends-on-open'?'depends-on-open':'open-obligation';
const resolutionError=(message,resolutionStatus='needs-context')=>Object.assign(Error(message),{resolutionStatus});
function freeNames(...expressions){
 const names=new Set();
 function visit(t){if(t.kind==='free')names.add(t.name);for(const v of Object.values(t))if(v&&typeof v==='object'){if(Array.isArray(v))v.forEach(visit);else visit(v);}}
 for(const expression of expressions)if(expression)visit(compileFormula(expression,{syntax:'lean'}).scoped);
 return [...names];
}
function unwrap(s){let body=s.trim(),modifiers=[];for(let i=0;i<4;i++){const m=marker.exec(body);if(!m)break;modifiers.push(m[0].trim());body=body.slice(m[0].length);}return {body,modifiers};}
function parseLine(raw){
 const {body,modifiers}=unwrap(raw);
 const hole=/^(?:建立|记|establish\s+|have\s+)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[:：]\s*\$\?\$\s*[,，|；;]\s*(?:由|from\s+|using\s+)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[。.]?$/iu.exec(body);
 if(hole){
  const [,name,source]=hole;
  if(compileFormula(name).ast.kind!=='id')throw Error('Invalid intermediate name.');
  return {raw,kind:'infer-proposition',name,source,modifiers};
 }
 const obtain=/^(?:由\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*取\s*|obtain\s+from\s+([A-Za-z_][A-Za-z0-9_']{0,63})\s+)([A-Za-z_][A-Za-z0-9_']{0,63})(?:\s*[:：]\s*(\$[^$\n]+\$|\\\([^]*?\\\)))?\s*[,，]\s*(?:记\s*|with\s+)?([A-Za-z_][A-Za-z0-9_']{0,63})\s*[。.]?$/iu.exec(body);
 if(obtain){
  const [,cn,en,name,annotation,evidenceName]=obtain;
  for(const n of [name,evidenceName])if(compileFormula(n).ast.kind!=='id')throw Error('Invalid witness or evidence name.');
  return {raw,kind:'obtain',source:cn||en,name,type:annotation?compileFormula(annotation).lean:null,evidenceName,modifiers};
 }
 const implicit=/^(任取|取任意|假设|设|take\s+|assume\s+)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[。.]?$/iu.exec(body);
 if(implicit){
  const [,word,name]=implicit;
  if(compileFormula(name).ast.kind!=='id')throw Error('Invalid introduction name.');
  return {raw,kind:/^(?:假设|设|assume)/iu.test(word)?'assume':'introduce',name,type:null,modifiers};
 }
 const intro=/^(任取|取任意|假设|设|take\s+|assume\s+)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[:：]\s*(\$[^$\n]+\$|\\\([^]*?\\\))\s*[。.]?$/iu.exec(body);
 if(intro){
  const [,word,name,type]=intro;
  if(compileFormula(name).ast.kind!=='id')throw Error('Invalid introduction name.');
  return {raw,kind:/^(?:假设|设|assume)/iu.test(word)?'assume':'introduce',name,type:compileFormula(type).lean,modifiers};
 }
 // A definition introduces a value, not a proof of an equality.
 const definition=/^(?:令|定义|记|let\s+|define\s+)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[:：]\s*(\$[^$\n]+\$|\\\([^]*?\\\))\s*(?::=|＝|=)\s*(\$[^$\n]+\$|\\\([^]*?\\\))\s*[。.]?$/iu.exec(body);
 if(definition){
  const [,name,domain,value]=definition;
  // Validate the name with the same restricted identifier grammar.
  if(compileFormula(name).ast.kind!=='id')throw Error('Invalid definition name.');
  return {raw,kind:'define',name,type:compileFormula(domain).lean,value:compileFormula(value).lean,modifiers};
 }
 const citation=formulaPremiseSentence(body);
 if(citation)return {raw,formula:citation.goal,type:compileFormula(citation.goal).lean,name:null,ruleText:'',conclusion:false,modifiers,citation};
 const occurrences=[...body.matchAll(formulaPattern)];
 if(occurrences.length!==1)throw Error('Write one delimited proposition in each inference.');
 const f=occurrences[0],formula=f[0],before=body.slice(0,f.index).trim(),after=body.slice(f.index+formula.length).trim().replace(/[。.]$/,'').trim();
 let name=null,ruleText='',conclusion=false,forwardText=null;
 const binding=/^(?:建立|记|令|let|establish|have|置く|示す)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[:：]$/iu.exec(before);
 if(binding){name=binding[1];if(compileFormula(name).ast.kind!=='id')throw Error('Invalid intermediate name.');ruleText=after.replace(/^[,，|；;]\s*/,'');}
 else if(/^(?:结论|证明|推出|conclude|show|therefore|示す)\s*[:：]?$/iu.test(before)){conclusion=true;ruleText=after.replace(/^[,，|；;]\s*/,'');}
 else if(!before){ruleText=after.replace(/^[,，|；;]\s*/,'');}
 else{
  const forward=/^(?:由|根据|利用|应用|by\s+|using\s+|from\s+)(.+?)\s*(?:[，,]\s*)?(?:得到|可得|推出|we obtain|we get|gives|yields|を得る)\s*[:：]?$/iu.exec(before);
  if(!forward||after)throw Error('Unrecognized mathematical wording; retained without guessing.');
  ruleText=forward[1].trim().replace(/[,，]$/,'').trim();
  // A rule-first phrase may cite either a theorem or local facts.
  // Defer this decision until the current context is available.
  forwardText='from '+ruleText;
 }
 return {raw,formula,type:compileFormula(formula).lean,name,ruleText,conclusion,modifiers,forwardText};
}
export function draftProof(input,scope=[],context=new Map(),{choices=new Map(),cache=null,goal=null,lineOffset=0,closedNames=[],openBindings=[],incompleteContext=false,continuation=false,scopeIds=[]}={}){
 const facts=new Map(context);
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const lines=input.split(/\r?\n/).map((raw,i)=>({raw,line:i+1+lineOffset})).filter(x=>x.raw.trim());
 if(lines.length>16)throw Error('Use at most sixteen inference lines.');
 const closed=new Set(closedNames);
 const occupied=new Set(scope),visible=new Set(scope.filter((x,i)=>scope.indexOf(x)===i&&scope.lastIndexOf(x)===i));
 // Cache syntax by exact text, independently of context. Cached errors are
 // deterministic syntax diagnostics, not semantic failures.
 const syntax=cache?(cache.syntax??=new Map()):new Map();
 const parsed=lines.map(({raw})=>{
  if(syntax.has(raw))return syntax.get(raw);
  let entry;try{entry={value:parseLine(raw)};}catch(e){entry={error:e.message};}
  if(syntax.size>=128)syntax.delete(syntax.keys().next().value);
  syntax.set(raw,entry);return entry;
 });
 const planned=new Set(parsed.flatMap(p=>[p.value?.name,p.value?.evidenceName]).filter(Boolean));
 const lookahead=parsed.some(p=>p.value?.kind==='infer-proposition')?JSON.stringify([input,[...choices]]):null;
 const inheritedOpen=[...new Set(openBindings)];
 const key=JSON.stringify([scope,scopeIds,[...context],[...planned].sort(),goal,lineOffset,lookahead,[...closed].sort(),inheritedOpen.sort(),incompleteContext,continuation]);
 const signatures=lines.map(({raw,line},i)=>JSON.stringify([raw,line,i===lines.length-1&&!continuation,choices.has(line),choices.get(line)]));
 let remainingGoal=goal;
 const constraintResults=new Map();
 let serial=1;const rows=[],steps=[],openNames=new Set(inheritedOpen),serials=[];let blocked=false,reusedRows=0;
 // The context and all planned names affect the entire draft. Under the
 // same context, reuse only an identical prefix, including choice and
 // conclusion-vs-intermediate role. Reconstruct its local scope exactly.
 const previous=cache?.previous;
 if(previous?.key===key){
  while(reusedRows<signatures.length&&signatures[reusedRows]===previous.signatures[reusedRows]){
   const row=previous.rows[reusedRows];if(!row)break;
   rows.push(row);serials.push(previous.serials[reusedRows]);
   if(row.status==='unresolved')blocked=true;
   if(row.step){
    steps.push(row.step);
    if(['establish','define','introduce','assume','obtain'].includes(row.step.kind)){
     const {name,type}=row.step;occupied.add(name);visible.add(name);facts.set(name,type);
     if(row.proofStatus!=='candidate')openNames.add(name);
     if(row.step.kind==='obtain'){
      const {evidenceName,evidenceType,copy}=row.step;
      occupied.add(copy);occupied.add(evidenceName);visible.add(evidenceName);facts.set(evidenceName,evidenceType);
      if(row.proofStatus!=='candidate')openNames.add(evidenceName);
     }
     if(['introduce','assume'].includes(row.step.kind))remainingGoal=row.remainingGoal;
    }
   }
   reusedRows++;
  }
  if(reusedRows)serial=serials.at(-1);
 }
 function unavailable(type){return freeNames(type).find(n=>(planned.has(n)||occupied.has(n)||closed.has(n))&&!visible.has(n));}
 function makeStep(p,last,application){
  if(last)return {kind:'conclude',type:p.type,application};
  let name=p.name;
  if(name&&occupied.has(name))throw Error('This intermediate name already exists.');
  if(!name){do{name='duet_h'+serial++;}while(occupied.has(name)||planned.has(name));}
  occupied.add(name);visible.add(name);facts.set(name,p.type);
  return {kind:'establish',name,type:p.type,application};
 }
 function unresolved(p,raw,line,last,details){
  const {resolutionStatus=p?'needs-context':'unsupported',...rowDetails}=details;
  blocked=true;
  const row={...p,raw,line,status:'unresolved',proofStatus:'open',resolutionStatus,...rowDetails};
  // Keep a recognized proposition as a tentative local object. It is not
  // an established theorem and no incomplete draft is exported.
  if(p&&!['define','introduce','assume','infer-proposition','obtain'].includes(p.kind)&&!last&&!p.conclusion&&(!p.name||!occupied.has(p.name))&&!unavailable(p.type)){
   const step=makeStep(p,false,'?');
   openNames.add(step.name);steps.push(step);row.step=step;
  }
  rows.push(row);
 }
 for(let i=reusedRows;i<lines.length;i++){
   const {raw,line}=lines[i],last=i===lines.length-1&&!continuation;let p=null;
   try{
    if(parsed[i].error)throw Error(parsed[i].error);
    p=parsed[i].value;
    if(p.kind==='infer-proposition'){
     if(last)throw resolutionError('An inferred intermediate must be followed by a conclusion.','incompatible-target');
     if(occupied.has(p.name))throw resolutionError('This intermediate name already exists.','incompatible-choice');
     const future=lines.slice(i+1).map((x,j)=>({line:x.line,parsed:parsed[i+1+j].value}));
     if(!constraintResults.has(line)){
      const network=constrainPropositions({line,parsed:p},[...visible],facts,future,choices,new Set(constraintResults.keys()));
      for(const [key,value] of network)if(!constraintResults.has(key))constraintResults.set(key,value);
     }
     const result=constraintResults.get(line);
     const {domain,candidates,constraints,group}=result;
     const picked=result.overflow?null:choices.has(line)?candidates.find(c=>candidateChoice(c)===choices.get(line)):candidates.length===1?candidates[0]:null;
     if(!picked){
      const sourceAvailable=visible.has(p.source)&&facts.has(p.source);
      const resolutionStatus=result.overflow?'budget-exhausted':choices.has(line)?'incompatible-choice':candidates.length?'ambiguous':group?.status==='contradiction'?'incompatible-constraints':sourceAvailable?'no-supported-match':'needs-context';
      const details={candidates,domain,constraints,constraintGroup:group,resolutionStatus,reason:result.reason||(choices.has(line)?'Selected proposition candidate is no longer compatible.':'Intermediate proposition is ambiguous; choose a candidate or add a structural constraint.')};
      // A type can be known even when the proof is not. Preserve a typed
      // open obligation if every surviving candidate has the same scoped
      // type; do not choose a proof merely because the types coincide.
      if(!result.overflow&&!choices.has(line)&&candidates.length>1){
       const type=candidates[0].type;
       const canonical=JSON.stringify(compileFormula(type,{syntax:'lean'}).scoped);
       if(candidates.every(c=>JSON.stringify(compileFormula(c.type,{syntax:'lean'}).scoped)===canonical)&&!unavailable(type)){
        p={...p,type};
        const step=makeStep(p,false,'?');
        openNames.add(step.name);steps.push(step);
        details.step=step;
        details.reason='The proposition type is determined, but its proof is ambiguous; choose a proof candidate.';
       }
      }
      unresolved(p,raw,line,last,details);
      continue;
     }
     p={...p,type:picked.type};
     if(unavailable(p.type))throw Error('The inferred proposition refers to an unavailable local object.');
     if(!visible.has(p.source)){
      const step=makeStep(p,false,'?');openNames.add(step.name);steps.push(step);
      unresolved(p,raw,line,last,{step,candidates,domain,constraints,constraintGroup:group,dependencies:[p.source],resolutionStatus:'needs-context',reason:'The proposition type is determined, but its projection source is still unresolved.'});continue;
     }
     const dependencies=[...new Set([...picked.premises,...freeNames(picked.type)].filter(n=>openNames.has(n)))];
     const proofStatus=dependencies.length?'depends-on-open':'candidate';
     const step=makeStep(p,false,picked.term);
     if(dependencies.length)openNames.add(step.name);
     rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,resolutionStatus:candidateResolution(proofStatus),dependencies,step,candidates,domain,constraints,constraintGroup:group});steps.push(step);continue;
    }
    if(p.kind==='obtain'){
      if(last)throw resolutionError('An existential elimination must be followed by a conclusion.','incompatible-target');
      if(choices.has(line))throw resolutionError('An existential elimination has no proof candidate choice.','incompatible-choice');
      if(!visible.has(p.source)||!facts.has(p.source))throw resolutionError('Cite a visible typed existential premise.','needs-context');
      if(p.name===p.evidenceName||occupied.has(p.name)||occupied.has(p.evidenceName))throw resolutionError('Witness and evidence names must be distinct and fresh.','incompatible-choice');
     const types=existentialBindings(facts.get(p.source),p);
     const missing=freeNames(types.type,types.evidenceType).find(n=>n!==p.name&&(planned.has(n)||occupied.has(n)||closed.has(n))&&!visible.has(n));
     if(missing)throw Error('Ambiguous or forward reference in existential elimination: '+missing);
     if(freeNames(types.type).includes(p.name))throw Error('Witness domain cannot refer to the new witness.');
     const stem='duet_exists_'+p.name.slice(0,40);
     let copy=stem;
     // Keep the original premise available; destructure a fresh copy.
     let suffix=0;while(occupied.has(copy)||planned.has(copy))copy=stem+'_'+(++suffix);
     const dependencies=[...new Set([p.source,...freeNames(types.type,types.evidenceType)].filter(n=>openNames.has(n)))];
     const proofStatus=dependencies.length?'depends-on-open':'candidate';
     const step={kind:'obtain',source:p.source,name:p.name,evidenceName:p.evidenceName,copy,...types};
     occupied.add(copy);
     for(const [name,type] of [[step.name,step.type],[step.evidenceName,step.evidenceType]]){
      occupied.add(name);visible.add(name);facts.set(name,type);if(dependencies.length)openNames.add(name);
     }
     rows.push({...p,...types,line,status:blocked?'provisional':'translated',proofStatus,resolutionStatus:candidateResolution(proofStatus),dependencies,step,candidates:[]});steps.push(step);continue;
    }
    if(['introduce','assume'].includes(p.kind)){
      if(last)throw resolutionError('An introduction must be followed by a conclusion.','incompatible-target');
      if(blocked)throw resolutionError('Resolve preceding incomplete wording before extending the goal.','needs-context');
      if(occupied.has(p.name))throw resolutionError('This local name already exists.','incompatible-choice');
      if(choices.has(line))throw resolutionError('An introduction has no proof candidate choice.','incompatible-choice');
     const goalOperation=planGoalOperation(remainingGoal,{kind:p.kind,name:p.name,type:p.type});
     p={...p,type:goalOperation.subgoals[0].contextDelta[0].type};
     const names=freeNames(p.type);
     for(const n of names)if((planned.has(n)||occupied.has(n)||closed.has(n))&&!visible.has(n))throw Error('Ambiguous or forward reference in introduction: '+n);
     remainingGoal=goalOperation.subgoals[0].goal;
     const scopedOperation={...goalOperation,subgoals:goalOperation.subgoals.map(subgoal=>({...subgoal,
      contextDelta:subgoal.contextDelta.map(binding=>({...binding,id:'line:'+line}))
     }))};
     const step={kind:p.kind,name:p.name,type:p.type,goalOperation:scopedOperation};
     occupied.add(p.name);visible.add(p.name);facts.set(p.name,p.type);
     const dependencies=names.filter(n=>openNames.has(n));
     if(dependencies.length)openNames.add(p.name);
     const proofStatus=dependencies.length?'depends-on-open':'candidate';
     rows.push({...p,line,status:'translated',proofStatus,resolutionStatus:candidateResolution(proofStatus),dependencies,remainingGoal,step,candidates:[]});steps.push(step);continue;
    }
    if(p.kind==='define'){
      if(last)throw resolutionError('A definition must be followed by a conclusion.','incompatible-target');
      if(occupied.has(p.name))throw resolutionError('This local name already exists.','incompatible-choice');
      if(choices.has(line))throw resolutionError('A definition has no proof candidate choice.','incompatible-choice');
     const free=freeNames(p.type,p.value);
     for(const n of free)if((planned.has(n)||occupied.has(n)||closed.has(n))&&!visible.has(n))throw Error('Ambiguous or forward reference in definition: '+n);
     const dependencies=[...free].filter(n=>openNames.has(n));
     const proofStatus=dependencies.length?'depends-on-open':'candidate';
     const step={kind:'define',name:p.name,type:p.type,value:p.value};
     occupied.add(p.name);visible.add(p.name);facts.set(p.name,p.type);
     if(dependencies.length)openNames.add(p.name);
     rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,resolutionStatus:candidateResolution(proofStatus),dependencies,step,candidates:[]});steps.push(step);continue;
    }
     if(p.conclusion&&!last)throw resolutionError('A conclusion must be the last inference.','incompatible-target');
     if(last&&p.name)throw resolutionError('The final inference must conclude the goal, not name a fact.','incompatible-target');
    const missing=unavailable(p.type);
    if(missing)throw Error('Ambiguous or forward reference in proposition: '+missing);
    let application='?',candidates=[];
    function chosen(){
     if(!choices.has(line))return null;
     const candidate=candidates.find(c=>c.term===choices.get(line));
     if(!candidate)throw resolutionError('Selected candidate is no longer available.','incompatible-choice');
     return candidate.term;
    }
    const frame=premiseFrame(p.forwardText||p.ruleText,[...visible]);
    const discourse=discourseFrame(p.forwardText||p.ruleText);
    if(p.citation||frame||discourse){
      const resolution=p.citation?citationCandidates(p.citation,[...visible],facts):discourse?discourseCandidates(discourse,p.type,rows,[...visible],facts):{candidates:contextCandidates(p.type,frame.premises,facts),overflow:false};
      candidates=resolution.candidates;
      const picked=chosen();
      if(!picked&&resolution.overflow){unresolved(p,raw,line,last,{candidates,resolutionStatus:'budget-exhausted',reason:'Too many matching formula citations; name a specific premise.'});continue;}
      if(!picked&&candidates.length!==1){
       const missingType=(discourse||frame)?.premises?.some(name=>!facts.has(name));
       const resolutionStatus=candidates.length?'ambiguous':missingType?'needs-context':'no-supported-match';
       unresolved(p,raw,line,last,{frame:discourse||frame,candidates,resolutionStatus,reason:candidates.length?'Multiple structural interpretations; specify the rule and ordered premises.':missingType?'A cited premise has no available type; add its context before resolving this inference.':'No structural match under the supported rules for these premises.'});continue;
      }
      application=picked||candidates[0].term;
    }else if(p.ruleText&&p.ruleText!=='?'){
      const words=p.ruleText.split(/\s+/);
      if(words.length<=9&&words.every(w=>namePattern.test(w)&&visible.has(w)))application=words.join(' ');
      else if(words.length<=9&&words.every(w=>namePattern.test(w))&&words.some(w=>visible.has(w))&&words.some(w=>!visible.has(w)&&!ruleGlueWords.has(w.toLowerCase()))){
       const missing=words.find(w=>!visible.has(w)&&!ruleGlueWords.has(w.toLowerCase()));
       throw resolutionError('Unknown or unavailable local premise: '+missing+'.','needs-context');
      }
      else {
       const r=parseRuleIntent(p.ruleText,{ordered:true});
       if(!r.rule)throw resolutionError('This rule wording is outside the supported deterministic rule catalog.','unsupported');
       if(r.required.some(x=>!visible.has(x)))throw resolutionError('A required premise is not available in the current context.','needs-context');
       if((occupied.has(r.rule)||planned.has(r.rule)||closed.has(r.rule))&&!visible.has(r.rule))throw resolutionError('Ambiguous or forward local rule reference.','needs-context');
       if(!r.required.length&&(structuralRules.has(r.rule)||visible.has(r.rule))){
         const resolution=implicitCandidates(p.type,[...visible],facts,{rule:r.rule});candidates=resolution.candidates;
         const picked=chosen();
         if(!picked&&(resolution.overflow||candidates.length!==1)){unresolved(p,raw,line,last,{candidates,resolutionStatus:resolution.overflow?'budget-exhausted':candidates.length?'ambiguous':'no-supported-match',reason:resolution.overflow?'Candidate search exceeded its finite budget; narrow the premises or add a candidate choice.':'The named rule has no unique supported premise correspondence; choose a candidate or specify its premises.'});continue;}
         application=picked||candidates[0].term;
       }else application=[r.rule,...r.required].join(' ');
      }
    }else if(!p.ruleText){
      const resolution=implicitCandidates(p.type,[...visible],facts);candidates=resolution.candidates;
      application=chosen()||'?';
      // Bare conclusions specify no reasoning. Keep the proof obligation,
      // even when a limited schema finds just one possible proof.
    }
    if(choices.has(line)&&!candidates.some(c=>c.term===choices.get(line))){const error=Error('Selected candidate is no longer available.');error.resolutionStatus='incompatible-choice';throw error;}
    // A bare local reference is the one proof shape whose surface type is
    // available without elaborating an application. A mismatch blocks export,
    // but does not decide Lean definitional equality.
    if(namePattern.test(application)&&facts.has(application)){
     let localTypeMatches=null;
     try{localTypeMatches=sameScopedFormula(facts.get(application),p.type);}catch{}
     if(localTypeMatches===false){const error=Error('Surface type of local premise '+application+' ('+facts.get(application)+') differs structurally from conclusion ('+p.type+'); Lean definitional equality has not been checked.');error.resolutionStatus='incompatible-target';throw error;}
    }
    const applicationPremises=candidates.find(c=>c.term===application)?.premises||application.split(/\s+/);
    const dependencies=[...new Set([...applicationPremises,...freeNames(p.type)].filter(name=>openNames.has(name)))];
    const proofStatus=application==='?'?'open':dependencies.length?'depends-on-open':'candidate';
    const step=makeStep(p,last,application);
    if(step.kind==='establish'&&proofStatus!=='candidate')openNames.add(step.name);
    const resolutionStatus=application==='?'?(candidates.length?'needs-choice':'open-obligation'):candidateResolution(proofStatus);
    rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,resolutionStatus,dependencies,step,candidates});steps.push(step);
   }catch(e){unresolved(p,raw,line,last,{resolutionStatus:e.resolutionStatus,reason:e.message});}
   finally{serials.push(serial);}
 }
 let structurallyComplete=lines.length>0&&!blocked&&steps.at(-1)?.kind==='conclude';
 if(structurallyComplete&&goal&&!sameScopedFormula(steps.at(-1).type,remainingGoal)){
  blocked=true;structurallyComplete=false;
  const last=rows.at(-1);
  if(last)rows[rows.length-1]={...last,status:'unresolved',proofStatus:'open',resolutionStatus:'incompatible-target',reason:'The conclusion does not structurally match the remaining goal.'};
 }
 const complete=structurallyComplete&&!incompleteContext;
 if(cache)cache.previous={key,signatures,rows,serials};
 // `complete` means only that this bounded draft can be rendered as a Lean
 // candidate. It does not report elaboration, kernel verification or faithful
 // alignment with the author's intended mathematics.
 return {rows,steps,complete,completionKind:complete?'structural-export-ready':'incomplete',leanVerification:'not-run',semanticFidelity:'not-assessed',reusedRows,remainingGoal,openBindings:[...openNames],graph:buildDraftGraph(scope,context,rows,{goal}),term:complete?renderChain(steps):null};
}
export function createDraftSession(){
 const cache={};
 return {
  evaluate:(input,scope,context,options)=>evaluateScopeAware(input,scope,context,{...options,cache}),
  compile:(input,scope,context,options)=>compileNaturalDraft(input,scope,context,{...options,cache}),
  reset:()=>{delete cache.previous;cache.syntax?.clear();cache.scopeCaches?.clear();cache.segmentResults?.clear();}
 };
}
export function compileNaturalDraft(input,scope,context,options){
 const r=evaluateScopeAware(input,scope,context,options);
 if(!r.complete){const unresolved=r.rows.find(x=>x.status==='unresolved'&&x.graphId?.includes('/case:'))||[...r.rows].reverse().find(x=>x.status==='unresolved');throw Error(unresolved?'Line '+unresolved.line+': '+unresolved.reason:'No complete conclusion.');}
 return r;
}

function evaluateScopeAware(input,scope=[],context=new Map(),options={}){
 const frame=options._proofScope||rootProofScope(scope,new Map(context),{goal:options.goal});
 function cacheForFrame(currentFrame,sharedCache){
  if(!sharedCache)return null;
  if(currentFrame.id==='root')return sharedCache;
  const scoped=sharedCache.scopeCaches??=new Map();
  let local=scoped.get(currentFrame.id);
  if(!local){
   if(scoped.size>=128)scoped.delete(scoped.keys().next().value);
   local={};
  }else scoped.delete(currentFrame.id);
  scoped.set(currentFrame.id,local);
  return local;
 }
 function extendFromDraft(currentFrame,result){
  let next=currentFrame;
  const idAt=line=>next.id==='root'?'line:'+line:next.id+'/line:'+line;
  function add(id,name,type,kind){next=extendProofScope(next,{id,name,type,kind});}
  for(const row of result.rows){
   const step=row.step;if(!step)continue;
   const id=idAt(row.line);
   if(step.kind==='obtain'){
    add(id,step.name,step.type,'witness');
    add(id+':evidence',step.evidenceName,step.evidenceType,'evidence');
   }else if(['establish','introduce','assume','define'].includes(step.kind))add(id,step.name,step.type,step.kind);
  }
  return next;
 }
 function combineSegments(prefix,result){
  const seenNodes=new Set(prefix.graph.nodes.map(node=>node.id));
  const nodes=[...prefix.graph.nodes,...result.graph.nodes.filter(node=>!seenNodes.has(node.id))];
  const groups=new Map([...(prefix.graph.constraintGroups||[]),...(result.graph.constraintGroups||[])].map(group=>[group.id,group]));
  const complete=result.complete&&!prefix.rows.some(row=>row.status==='unresolved');
  const steps=[...prefix.steps,...result.steps];
  return {...result,rows:[...prefix.rows,...result.rows].sort((a,b)=>a.line-b.line),steps,complete,
   completionKind:complete?'structural-export-ready':'incomplete',reusedRows:(prefix.reusedRows||0)+(result.reusedRows||0),
   openBindings:[...new Set([...(prefix.openBindings||[]),...(result.openBindings||[])])],
   graph:{...result.graph,nodes,constraintGroups:[...groups.values()]},term:complete?renderChain(steps):null};
 }
 function segmentCacheKey(text,currentFrame,segmentOptions){
  const choices=[...(segmentOptions.choices||new Map())].sort(([left],[right])=>String(left).localeCompare(String(right)));
  const bindings=currentFrame.bindings.map(binding=>[binding.id,binding.name,binding.type,binding.kind,!!binding.local]);
  return JSON.stringify([currentFrame.id,currentFrame.goal,currentFrame.goalText,bindings,String(text||''),segmentOptions.goal||null,
   segmentOptions.lineOffset||0,choices,[...(segmentOptions.closedNames||[])].sort(),[...(segmentOptions.openBindings||[])].sort(),
   !!segmentOptions.incompleteContext,!!segmentOptions.continuation]);
 }
 function cloneResult(result){
  try{return structuredClone(result);}catch{return null;}
 }
 function compileSegment(text,currentFrame,segmentOptions={}){
  // Memoize a complete returned tree only at the editor's root. Nested scopes
  // keep the lighter row-prefix cache; cloning a whole inner graph on every
  // branch hit costs more than recompiling that bounded wrapper.
  const shared=currentFrame.id==='root'?segmentOptions.cache:null;
  const rootBlock=String(text||'').split(/\r?\n/).some(line=>!line.startsWith(' ')&&!line.startsWith('\t')&&
   (hasCaseSplitHeader(line.trim())||hasConjunctionGoalHeader(line.trim())));
  // Small linear fragments are cheaper to rebuild than to deep-clone. Reserve
  // whole-result memoization for scoped programs or substantial source text.
  if(!shared||(!rootBlock&&String(text||'').length<512))return compileSegmentFresh(text,currentFrame,segmentOptions);
  const key=segmentCacheKey(text,currentFrame,segmentOptions),memo=shared.segmentResults??=new Map();
  const cached=memo.get(key);
  if(cached){
   memo.delete(key);memo.set(key,cached);
   const reused=cloneResult(cached);
   if(reused){reused.reusedRows=reused.rows?.length||0;return reused;}
  }
  const result=compileSegmentFresh(text,currentFrame,segmentOptions),copy=cloneResult(result);
  if(copy){
   copy.reusedRows=0;
   if(memo.size>=32)memo.delete(memo.keys().next().value);
   memo.set(key,copy);
  }
  return result;
 }
 function compileSegmentFresh(text,currentFrame,segmentOptions={}){
  const names=proofScopeNames(currentFrame),facts=proofScopeFacts(currentFrame);
  const lines=String(text||'').split(/\r?\n/),first=lines.findIndex(line=>line.trim());
  const blockIndex=lines.findIndex(line=>!line.startsWith(' ')&&!line.startsWith('\t')&&
   (hasCaseSplitHeader(line.trim())||hasConjunctionGoalHeader(line.trim())));
  const blockKind=blockIndex>=0&&hasCaseSplitHeader(lines[blockIndex].trim())?'cases':'conjunction';
  if(blockIndex>=0&&blockIndex===first){
   if(blockKind==='cases')return compileCaseProgram(text,currentFrame,segmentOptions,compileSegment);
   return compileConjunctionGoal(text,currentFrame,segmentOptions,compileSegment,parseLine);
  }
  if(blockIndex>first){
   const lineOffset=segmentOptions.lineOffset||0;
   const prefix=draftProof(lines.slice(0,blockIndex).join('\n'),names,facts,{...segmentOptions,lineOffset,continuation:true,
    cache:cacheForFrame(currentFrame,segmentOptions.cache),scopeIds:currentFrame.bindings.map(binding=>binding.id)});
   prefix.graph=remapProofGraph(prefix.graph,currentFrame);
   const nextFrame=extendFromDraft(currentFrame,prefix);
   const hasOpenText=prefix.rows.some(row=>row.status==='unresolved');
   const remainingText=lines.slice(blockIndex).join('\n');
   const following=blockKind==='cases'
    ?compileCaseProgram(remainingText,nextFrame,{...segmentOptions,
      goal:prefix.remainingGoal,lineOffset:lineOffset+blockIndex,
      openBindings:[...new Set([...(segmentOptions.openBindings||[]),...(prefix.openBindings||[])])],
      incompleteContext:!!segmentOptions.incompleteContext||hasOpenText
     },compileSegment)
     :compileConjunctionGoal(remainingText,nextFrame,{...segmentOptions,
      goal:prefix.remainingGoal,lineOffset:lineOffset+blockIndex,
      openBindings:[...new Set([...(segmentOptions.openBindings||[]),...(prefix.openBindings||[])])],
      incompleteContext:!!segmentOptions.incompleteContext||hasOpenText,cache:segmentOptions.cache
     },compileSegment,parseLine);
   return combineSegments(prefix,following);
  }
  const result=draftProof(text,names,facts,{...segmentOptions,lineOffset:segmentOptions.lineOffset||0,
   cache:cacheForFrame(currentFrame,segmentOptions.cache),scopeIds:currentFrame.bindings.map(binding=>binding.id)});
  result.graph=remapProofGraph(result.graph,currentFrame);
  return result;
 }
 return compileSegment(input,frame,options);
}
