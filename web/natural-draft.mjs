import {compileFormula} from './math-formula.mjs';
import {buildDraftGraph} from './draft-graph.mjs';
import {extendGoal} from './context-extension.mjs';
import {constrainPropositions} from './proposition-constraints.mjs';
import {discourseFrame,discourseCandidates} from './discourse.mjs';
import {parseRuleIntent} from './rule-intent.mjs';
import {renderChain} from './proof-chain.mjs';
import {premiseFrame,contextCandidates,formulaPremiseSentence,citationCandidates,implicitCandidates,structuralRules} from './context-grammar.mjs';
const marker=/^(?:(?:therefore|hence|thus|clearly|obviously|indeed|then)(?:\s*[,，:：]\s*|\s+)|(?:因此|从而|于是|显然|事实上|故|则)[，、：:\s]*)/iu;
const formulaPattern=/\$[^$\n]+\$|\\\([^]*?\\\)|\\\[[^]*?\\\]/g;
const namePattern=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
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
export function draftProof(input,scope=[],context=new Map(),{choices=new Map(),cache=null,goal=null}={}){
 const facts=new Map(context);
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const lines=input.split(/\r?\n/).map((raw,i)=>({raw,line:i+1})).filter(x=>x.raw.trim());
 if(lines.length>16)throw Error('Use at most sixteen inference lines.');
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
 const planned=new Set(parsed.map(p=>p.value?.name).filter(Boolean));
 const lookahead=parsed.some(p=>p.value?.kind==='infer-proposition')?JSON.stringify([input,[...choices]]):null;
 const key=JSON.stringify([scope,[...context],[...planned].sort(),goal,lookahead]);
 const signatures=lines.map(({raw,line},i)=>JSON.stringify([raw,line,i===lines.length-1,choices.has(line),choices.get(line)]));
 let remainingGoal=goal;
 const constraintResults=new Map();
 let serial=1;const rows=[],steps=[],openNames=new Set(),serials=[];let blocked=false,reusedRows=0;
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
    if(['establish','define','introduce','assume'].includes(row.step.kind)){
     const {name,type}=row.step;occupied.add(name);visible.add(name);facts.set(name,type);
     if(row.proofStatus!=='candidate')openNames.add(name);
     if(['introduce','assume'].includes(row.step.kind))remainingGoal=row.remainingGoal;
    }
   }
   reusedRows++;
  }
  if(reusedRows)serial=serials.at(-1);
 }
 function unavailable(type){return freeNames(type).find(n=>(planned.has(n)||occupied.has(n))&&!visible.has(n));}
 function makeStep(p,last,application){
  if(last)return {kind:'conclude',type:p.type,application};
  let name=p.name;
  if(name&&occupied.has(name))throw Error('This intermediate name already exists.');
  if(!name){do{name='duet_h'+serial++;}while(occupied.has(name)||planned.has(name));}
  occupied.add(name);visible.add(name);facts.set(name,p.type);
  return {kind:'establish',name,type:p.type,application};
 }
 function unresolved(p,raw,line,last,details){
  blocked=true;
  const row={...p,raw,line,status:'unresolved',proofStatus:'open',...details};
  // Keep a recognized proposition as a tentative local object. It is not
  // an established theorem and no incomplete draft is exported.
  if(p&&!['define','introduce','assume','infer-proposition'].includes(p.kind)&&!last&&!p.conclusion&&(!p.name||!occupied.has(p.name))&&!unavailable(p.type)){
   const step=makeStep(p,false,'?');
   openNames.add(step.name);steps.push(step);row.step=step;
  }
  rows.push(row);
 }
 for(let i=reusedRows;i<lines.length;i++){
   const {raw,line}=lines[i],last=i===lines.length-1;let p=null;
   try{
    if(parsed[i].error)throw Error(parsed[i].error);
    p=parsed[i].value;
    if(p.kind==='infer-proposition'){
     if(last)throw Error('An inferred intermediate must be followed by a conclusion.');
     if(occupied.has(p.name))throw Error('This intermediate name already exists.');
     const future=lines.slice(i+1).map((x,j)=>({line:x.line,parsed:parsed[i+1+j].value}));
     if(!constraintResults.has(line)){
      const network=constrainPropositions({line,parsed:p},[...visible],facts,future,choices,new Set(constraintResults.keys()));
      for(const [key,value] of network)if(!constraintResults.has(key))constraintResults.set(key,value);
     }
     const result=constraintResults.get(line);
     const {domain,candidates,constraints,group}=result;
     const picked=result.overflow?null:choices.has(line)?candidates.find(c=>c.term===choices.get(line)):candidates.length===1?candidates[0]:null;
     if(!picked){
      const details={candidates,domain,constraints,constraintGroup:group,reason:result.reason||(choices.has(line)?'Selected proposition candidate is no longer compatible.':'Intermediate proposition is ambiguous; choose a candidate or add a structural constraint.')};
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
     const dependencies=[...new Set([...picked.premises,...freeNames(picked.type)].filter(n=>openNames.has(n)))];
     const proofStatus=dependencies.length?'depends-on-open':'candidate';
     const step=makeStep(p,false,picked.term);
     if(dependencies.length)openNames.add(step.name);
     rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,dependencies,step,candidates,domain,constraints,constraintGroup:group});steps.push(step);continue;
    }
    if(['introduce','assume'].includes(p.kind)){
     if(last)throw Error('An introduction must be followed by a conclusion.');
     if(blocked)throw Error('Resolve preceding incomplete wording before extending the goal.');
     if(occupied.has(p.name))throw Error('This local name already exists.');
     if(choices.has(line))throw Error('An introduction has no proof candidate choice.');
     const names=freeNames(p.type);
     for(const n of names)if((planned.has(n)||occupied.has(n))&&!visible.has(n))throw Error('Ambiguous or forward reference in introduction: '+n);
     remainingGoal=extendGoal(remainingGoal,p);
     const step={kind:p.kind,name:p.name,type:p.type};
     occupied.add(p.name);visible.add(p.name);facts.set(p.name,p.type);
     const dependencies=names.filter(n=>openNames.has(n));
     if(dependencies.length)openNames.add(p.name);
     rows.push({...p,line,status:'translated',proofStatus:dependencies.length?'depends-on-open':'candidate',dependencies,remainingGoal,step,candidates:[]});steps.push(step);continue;
    }
    if(p.kind==='define'){
     if(last)throw Error('A definition must be followed by a conclusion.');
     if(occupied.has(p.name))throw Error('This local name already exists.');
     if(choices.has(line))throw Error('A definition has no proof candidate choice.');
     const free=freeNames(p.type,p.value);
     for(const n of free)if((planned.has(n)||occupied.has(n))&&!visible.has(n))throw Error('Ambiguous or forward reference in definition: '+n);
     const dependencies=[...free].filter(n=>openNames.has(n));
     const proofStatus=dependencies.length?'depends-on-open':'candidate';
     const step={kind:'define',name:p.name,type:p.type,value:p.value};
     occupied.add(p.name);visible.add(p.name);facts.set(p.name,p.type);
     if(dependencies.length)openNames.add(p.name);
     rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,dependencies,step,candidates:[]});steps.push(step);continue;
    }
    if(p.conclusion&&!last)throw Error('A conclusion must be the last inference.');
    if(last&&p.name)throw Error('The final inference must conclude the goal, not name a fact.');
    const missing=unavailable(p.type);
    if(missing)throw Error('Ambiguous or forward reference in proposition: '+missing);
    let application='?',candidates=[];
    function chosen(){
     if(!choices.has(line))return null;
     const candidate=candidates.find(c=>c.term===choices.get(line));
     if(!candidate)throw Error('Selected candidate is no longer available.');
     return candidate.term;
    }
    const frame=premiseFrame(p.forwardText||p.ruleText,[...visible]);
    const discourse=discourseFrame(p.forwardText||p.ruleText);
    if(p.citation||frame||discourse){
      const resolution=p.citation?citationCandidates(p.citation,[...visible],facts):discourse?discourseCandidates(discourse,p.type,rows,[...visible],facts):{candidates:contextCandidates(p.type,frame.premises,facts),overflow:false};
      candidates=resolution.candidates;
      const picked=chosen();
      if(!picked&&resolution.overflow){unresolved(p,raw,line,last,{candidates,reason:'Too many matching formula citations; name a specific premise.'});continue;}
      if(!picked&&candidates.length!==1){unresolved(p,raw,line,last,{frame:discourse||frame,candidates,reason:candidates.length?'Multiple structural interpretations; specify the rule and ordered premises.':'No structural match for these premises. Name a rule or provide context types.'});continue;}
      application=picked||candidates[0].term;
    }else if(p.ruleText&&p.ruleText!=='?'){
      const words=p.ruleText.split(/\s+/);
      if(words.length<=9&&words.every(w=>namePattern.test(w)&&visible.has(w)))application=words.join(' ');
      else {
       const r=parseRuleIntent(p.ruleText,{ordered:true});
       if(!r.rule||r.required.some(x=>!visible.has(x)))throw Error('Unknown or ambiguous premise; check scope and wording.');
       if((occupied.has(r.rule)||planned.has(r.rule))&&!visible.has(r.rule))throw Error('Ambiguous or forward local rule reference.');
       if(!r.required.length&&(structuralRules.has(r.rule)||visible.has(r.rule))){
         const resolution=implicitCandidates(p.type,[...visible],facts,{rule:r.rule});candidates=resolution.candidates;
         const picked=chosen();
         if(!picked&&(resolution.overflow||candidates.length!==1)){unresolved(p,raw,line,last,{candidates,reason:'The named rule needs a unique premise correspondence; choose or specify its premises.'});continue;}
         application=picked||candidates[0].term;
       }else application=[r.rule,...r.required].join(' ');
      }
    }else if(!p.ruleText){
      const resolution=implicitCandidates(p.type,[...visible],facts);candidates=resolution.candidates;
      application=chosen()||'?';
      // Bare conclusions specify no reasoning. Keep the proof obligation,
      // even when a limited schema finds just one possible proof.
    }
    if(choices.has(line)&&!candidates.some(c=>c.term===choices.get(line)))throw Error('Selected candidate is no longer available.');
    const applicationPremises=candidates.find(c=>c.term===application)?.premises||application.split(/\s+/);
    const dependencies=[...new Set([...applicationPremises,...freeNames(p.type)].filter(name=>openNames.has(name)))];
    const proofStatus=application==='?'?'open':dependencies.length?'depends-on-open':'candidate';
    const step=makeStep(p,last,application);
    if(step.kind==='establish'&&proofStatus!=='candidate')openNames.add(step.name);
    rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,dependencies,step,candidates});steps.push(step);
   }catch(e){unresolved(p,raw,line,last,{reason:e.message});}
   finally{serials.push(serial);}
 }
 if(cache)cache.previous={key,signatures,rows,serials};
 const complete=lines.length>0&&!blocked&&steps.at(-1)?.kind==='conclude';
 return {rows,steps,complete,reusedRows,remainingGoal,openBindings:[...openNames],graph:buildDraftGraph(scope,context,rows,{goal}),term:complete?renderChain(steps):null};
}
export function createDraftSession(){
 const cache={};
 return {
  evaluate:(input,scope,context,options)=>draftProof(input,scope,context,{...options,cache}),
  compile:(input,scope,context,options)=>compileNaturalDraft(input,scope,context,{...options,cache}),
  reset:()=>{delete cache.previous;cache.syntax?.clear();}
 };
}
export function compileNaturalDraft(input,scope,context,options){
 const r=draftProof(input,scope,context,options);
 if(!r.complete){const unresolved=r.rows.find(x=>x.status==='unresolved');throw Error(unresolved?'Line '+unresolved.line+': '+unresolved.reason:'No complete conclusion.');}
 return r;
}
