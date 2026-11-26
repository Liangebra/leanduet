import {compileFormula} from './math-formula.mjs';
import {buildDraftGraph} from './draft-graph.mjs';
import {parseRuleIntent} from './rule-intent.mjs';
import {renderChain} from './proof-chain.mjs';
import {premiseFrame,contextCandidates,formulaPremiseSentence,citationCandidates,implicitCandidates,structuralRules} from './context-grammar.mjs';
const marker=/^(?:(?:therefore|hence|thus|clearly|obviously|indeed|then)(?:\s*[,，:：]\s*|\s+)|(?:因此|从而|于是|显然|事实上|故|则)[，、：:\s]*)/iu;
const formulaPattern=/\$[^$\n]+\$|\\\([^]*?\\\)|\\\[[^]*?\\\]/g;
const namePattern=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
function unwrap(s){let body=s.trim(),modifiers=[];for(let i=0;i<4;i++){const m=marker.exec(body);if(!m)break;modifiers.push(m[0].trim());body=body.slice(m[0].length);}return {body,modifiers};}
function parseLine(raw){
 const {body,modifiers}=unwrap(raw);
 const citation=formulaPremiseSentence(body);
 if(citation)return {raw,formula:citation.goal,type:compileFormula(citation.goal).lean,name:null,ruleText:'',conclusion:false,modifiers,citation};
 const occurrences=[...body.matchAll(formulaPattern)];
 if(occurrences.length!==1)throw Error('Write one delimited proposition in each inference.');
 const f=occurrences[0],formula=f[0],before=body.slice(0,f.index).trim(),after=body.slice(f.index+formula.length).trim().replace(/[。.]$/,'').trim();
 let name=null,ruleText='',conclusion=false,forwardText=null;
 const binding=/^(?:建立|记|令|let|establish|have|置く|示す)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[:：]$/iu.exec(before);
 if(binding){name=binding[1];ruleText=after.replace(/^[,，|；;]\s*/,'');}
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
export function draftProof(input,scope=[],context=new Map()){
 const facts=new Map(context);
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const lines=input.split(/\r?\n/).map((raw,i)=>({raw,line:i+1})).filter(x=>x.raw.trim());
 if(lines.length>16)throw Error('Use at most sixteen inference lines.');
 const occupied=new Set(scope),visible=new Set(scope.filter((x,i)=>scope.indexOf(x)===i&&scope.lastIndexOf(x)===i));
 const planned=new Set(lines.map(({raw})=>{try{return parseLine(raw).name;}catch{return null;}}).filter(Boolean));
 let serial=1;const rows=[],steps=[],openNames=new Set();let blocked=false;
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
  if(p&&!last&&!p.conclusion&&(!p.name||!occupied.has(p.name))){
   const step=makeStep(p,false,'?');
   openNames.add(step.name);steps.push(step);row.step=step;
  }
  rows.push(row);
 }
 for(let i=0;i<lines.length;i++){
   const {raw,line}=lines[i],last=i===lines.length-1;let p=null;
   try{
    p=parseLine(raw);
    if(p.conclusion&&!last)throw Error('A conclusion must be the last inference.');
    if(last&&p.name)throw Error('The final inference must conclude the goal, not name a fact.');
    let application='?',candidates=[];
    const frame=premiseFrame(p.forwardText||p.ruleText,[...visible]);
    if(p.citation||frame){
      const resolution=p.citation?citationCandidates(p.citation,[...visible],facts):{candidates:contextCandidates(p.type,frame.premises,facts),overflow:false};
      candidates=resolution.candidates;
      if(resolution.overflow){unresolved(p,raw,line,last,{candidates,reason:'Too many matching formula citations; name a specific premise.'});continue;}
      if(candidates.length!==1){unresolved(p,raw,line,last,{frame,candidates,reason:candidates.length?'Multiple structural interpretations; specify the rule and ordered premises.':'No structural match for these premises. Name a rule or provide context types.'});continue;}
      application=candidates[0].term;
    }else if(p.ruleText&&p.ruleText!=='?'){
      const words=p.ruleText.split(/\s+/);
      if(words.length<=9&&words.every(w=>namePattern.test(w)&&visible.has(w)))application=words.join(' ');
      else {
       const r=parseRuleIntent(p.ruleText,{ordered:true});
       if(!r.rule||r.required.some(x=>!visible.has(x)))throw Error('Unknown or ambiguous premise; check scope and wording.');
       if((occupied.has(r.rule)||planned.has(r.rule))&&!visible.has(r.rule))throw Error('Ambiguous or forward local rule reference.');
       if(!r.required.length&&(structuralRules.has(r.rule)||visible.has(r.rule))){
         const resolution=implicitCandidates(p.type,[...visible],facts,{rule:r.rule});candidates=resolution.candidates;
         if(resolution.overflow||candidates.length!==1){unresolved(p,raw,line,last,{candidates,reason:'The named rule needs a unique premise correspondence; choose or specify its premises.'});continue;}
         application=candidates[0].term;
       }else application=[r.rule,...r.required].join(' ');
      }
    }else if(!p.ruleText){
      const resolution=implicitCandidates(p.type,[...visible],facts);candidates=resolution.candidates;
      // Bare conclusions specify no reasoning. Keep the proof obligation,
      // even when a limited schema finds just one possible proof.
    }
    const dependencies=[...new Set(application.split(/\s+/).filter(name=>openNames.has(name)))];
    const proofStatus=application==='?'?'open':dependencies.length?'depends-on-open':'candidate';
    const step=makeStep(p,last,application);
    if(step.kind==='establish'&&proofStatus!=='candidate')openNames.add(step.name);
    rows.push({...p,line,status:blocked?'provisional':'translated',proofStatus,dependencies,step,candidates});steps.push(step);
   }catch(e){unresolved(p,raw,line,last,{reason:e.message});}
 }
 const complete=lines.length>0&&!blocked&&steps.at(-1)?.kind==='conclude';
 return {rows,steps,complete,openBindings:[...openNames],graph:buildDraftGraph(scope,context,rows),term:complete?renderChain(steps):null};
}
export function compileNaturalDraft(input,scope,context){
 const r=draftProof(input,scope,context);
 if(!r.complete){const unresolved=r.rows.find(x=>x.status==='unresolved');throw Error(unresolved?'Line '+unresolved.line+': '+unresolved.reason:'No complete conclusion.');}
 return r;
}
