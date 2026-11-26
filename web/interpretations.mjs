import {compileFormula} from './math-formula.mjs';
import {parseRuleIntent} from './rule-intent.mjs';
import {premiseFrame,contextCandidates} from './context-grammar.mjs';
// Only these explicitly enumerated discourse markers are separated.
// Arbitrary qualifiers ("nonzero", "uniformly", etc.) are NOT removed.
const marker=/^(?:(?:therefore|hence|thus|clearly|obviously|indeed)(?:\s*[,，:：]\s*|\s+)|(?:因此|从而|于是|显然|事实上|故)[，、：:\s]*)/iu;
const simple=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
const rule=/^[A-Za-z_][A-Za-z0-9_'.]{0,159}$/;
export function interpretations(input,scope=[],facts=new Map()){
  if(typeof input!=='string'||input.length>12000)throw Error('Exploration input exceeds limit.');
  const alternatives=[],unresolved=[],seen=new Set();
  const visible=new Set(scope.filter((x,i)=>scope.indexOf(x)===i&&scope.lastIndexOf(x)===i));
  function add(a){const key=JSON.stringify([a.formula,a.rule,a.required,a.term]);if(!seen.has(key)&&alternatives.length<8){seen.add(key);alternatives.push(a);}}
  const lines=input.split(/\r?\n/).map(s=>s.trim()).filter(Boolean);
  for(const raw of lines.slice(8))unresolved.push({raw,reason:'Outside the eight-line check limit.'});
  for(const raw of lines.slice(0,8)){
    let body=raw,modifiers=[];
    for(let i=0;i<4;i++){const m=marker.exec(body);if(!m)break;modifiers.push(m[0].trim());body=body.slice(m[0].length);}
    try{
      let formula='',rest=body;
      const m=/^(\$[^$]+\$|\\\([\s\S]+?\\\)|\\\[[\s\S]+?\\\])(?:\s*[|,，:：]\s*(.*))?$/.exec(body);
      if(m){formula=compileFormula(m[1]).lean;rest=m[2]||'';}
      const base={raw,modifiers,formula,rule:'',required:[],term:''};
      if(!rest){if(!formula)throw Error('No interpretation.');add({...base,origin:'formula search',specificity:2});continue;}
      const frame=premiseFrame(rest,scope);
      if(frame&&formula){
        const candidates=contextCandidates(formula,frame.premises,facts);
        if(!candidates.length)throw Error('No structural match for named premises; retain the wording or specify a rule.');
        for(const c of candidates)add({...base,term:c.term,required:[...new Set(c.premises)],origin:'context schema · '+c.schema,specificity:5});
        continue;
      }
      const words=rest.split(/\s+/);
      if(words.length<=8&&rule.test(words[0])&&words.slice(1).every(x=>simple.test(x)&&visible.has(x))&&visible.has(words[0])){
        add({...base,term:words.join(' '),required:[...new Set(words)],origin:'local application',specificity:5});continue;
      }
      const intent=parseRuleIntent(rest);
      if(intent.required.some(x=>!visible.has(x)))throw Error('Unknown or ambiguous premise.');
      if(!intent.rule&&!formula&&!intent.required.length)throw Error('Provide mathematical content.');
      if(visible.has(intent.rule)){
        if(new Set([intent.rule,...intent.required]).size>8)throw Error('Too many local premises.');
        add({...base,term:[intent.rule,...intent.required].join(' '),required:[...new Set([intent.rule,...intent.required])],origin:'ordered local application',specificity:5});
      }else{
        add({...base,...intent,origin:'named rule search',specificity:4+Number(!!formula)});
        if(intent.rule&&intent.required.length)add({...base,term:[intent.rule,...intent.required].join(' '),required:intent.required,origin:'explicit application',specificity:4+Number(!!formula)});
      }
    }catch(e){unresolved.push({raw,reason:e.message});}
  }
  return {alternatives,unresolved};
}
// A deterministic preference, not a probability or proof of authorial intent.
export function rankInterpretations(plan,checked){
  const rows=[];
  for(const row of checked.interpretations||[]){
    const a=plan.alternatives[row.index];if(!a)continue;
    for(const c of row.candidates||[])rows.push({...c,interpretation:a,score:a.specificity});
  }
  return rows.sort((a,b)=>b.score-a.score||a.term.length-b.term.length||a.term.localeCompare(b.term));
}

export function mergeInterpretations(primary,reviewed){
 const alternatives=[...primary.alternatives],unresolved=[...primary.unresolved];
 const seen=new Set(alternatives.map(a=>JSON.stringify([a.formula,a.rule,a.required,a.term])));
 for(const a of reviewed.alternatives){
   const k=JSON.stringify([a.formula,a.rule,a.required,a.term]);
   if(seen.has(k))continue;
   if(alternatives.length>=8){unresolved.push({raw:a.raw,reason:'Reviewed AI alternative outside the eight-candidate check limit.'});continue;}
   seen.add(k);alternatives.push({...a,origin:'reviewed AI · '+a.origin,specificity:Math.max(0,a.specificity-1)});
 }
 for(const a of reviewed.unresolved)unresolved.push({...a,reason:'AI suggestion: '+a.reason});
 return {alternatives,unresolved};
}
