import {compileFormula} from './math-formula.mjs';
import {parseRuleIntent,statementMarker} from './rule-intent.mjs';
// Ordered application grammar. This is not free prose or search.
// A rule is a declaration or a local function; named arguments are positional.
const ident=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
export function compileChain(text,scope){
  if(typeof text!=='string'||text.length>12000||!Array.isArray(scope))throw Error('Invalid chain or scope.');
  const lines=text.split(/\r?\n/).map(x=>x.trim()).filter(Boolean);
  if(!lines.length||lines.length>16)throw Error('Use 1–16 inference lines.');
  const counts=new Map();
  for(const n of scope)counts.set(n,(counts.get(n)||0)+1);
  const visible=new Set([...counts].filter(([,c])=>c===1).map(([n])=>n));
  const occupied=new Set(scope),steps=[];
  const planned=new Set(lines.map(l=>statementMarker(l.split('|')[0])?.name).filter(Boolean));
  let done=false;
  function application(phrase,line){
    if(phrase.trim()==='?')return '?';
    const {rule,required}=parseRuleIntent(phrase,{ordered:true});
    if(!rule)throw Error('Line '+line+': name an explicit rule; automatic search is not part of this grammar.');
    for(const arg of required)if(!visible.has(arg))throw Error('Line '+line+': unknown, ambiguous or forward reference '+arg);
    if(planned.has(rule)&&!visible.has(rule))throw Error('Line '+line+': forward rule reference '+rule);
    if(counts.get(rule)>1)throw Error('Line '+line+': ambiguous local rule '+rule);
    return [rule,...required].join(' ');
  }
  for(let i=0;i<lines.length;i++){
    if(done)throw Error('No statements may follow the conclusion.');
    const line=lines[i],parts=line.split('|');
    if(parts.length!==2)throw Error('Line '+(i+1)+': separate the statement and rule with |.');
    const [left,right]=parts.map(s=>s.trim());
    const marker=statementMarker(left);
    if(marker?.kind==='conclude'){
      steps.push({kind:'conclude',application:application(right,i+1)});done=true;continue;
    }
    if(marker?.kind!=='establish')throw Error('Line '+(i+1)+': expected an intermediate name, optionally with : proposition.');
    const {name}=marker;
    const type=marker.type?.startsWith('$')||marker.type?.startsWith('\\(')?compileFormula(marker.type).lean:marker.type;
    if(occupied.has(name))throw Error('Line '+(i+1)+': binding already exists: '+name);
    // Type is an explicit Lean proposition expression, not a translated sentence.
    if(type!==null&&/[;{}]|(?:\/-|--|:=|\b(?:by|sorry|admit)\b)/.test(type))throw Error('Line '+(i+1)+': supply a single Lean proposition expression.');
    const app=application(right,i+1);
    if(app==='?'&&type===null)throw Error('Line '+(i+1)+': a proof hole requires an explicit proposition.');
    steps.push({kind:'establish',name,type,application:app});
    occupied.add(name);visible.add(name);
  }
  if(!done)throw Error('Finish with Conclude | rule using premises.');
  return {steps,term:renderChain(steps)};
}

// One formula per line; no prose or rule name is required.
export function compileFormulaSequence(text,scope){
  if(typeof text!=='string'||text.length>12000||!Array.isArray(scope))throw Error('Invalid formula sequence or scope.');
  const lines=text.split(/\r?\n/).map(x=>x.trim()).filter(Boolean);
  if(!lines.length||lines.length>16)throw Error('Use 1–16 formulas, one per line.');
  const used=new Set(scope),steps=[];
  let serial=1;
  for(let i=0;i<lines.length;i++){
    const line=lines[i],named=/^([A-Za-z_][A-Za-z0-9_']{0,63})\s*:\s*(\$.*|\\\(.*|\\\[.*)$/.exec(line);
    const input=named?named[2]:line;
    if(!((input.startsWith('$')&&input.endsWith('$'))||(input.startsWith('\\(')&&input.endsWith('\\)'))||(input.startsWith('\\[')&&input.endsWith('\\]'))))throw Error('Line '+(i+1)+': enclose a formula in LaTeX delimiters.');
    const formula=compileFormula(input);
    if(i===lines.length-1){
      if(named)throw Error('The final formula is the conclusion; do not name it.');
      steps.push({kind:'conclude',type:formula.lean,application:'?'});
    }else{
      let name=named?.[1];
      if(name&&used.has(name))throw Error('Line '+(i+1)+': binding already exists: '+name);
      if(!name){do{name='duet_h'+serial++;}while(used.has(name));}
      used.add(name);steps.push({kind:'establish',name,type:formula.lean,application:'?'});
    }
  }
  return {steps,term:renderChain(steps)};
}
export function renderChain(steps){
  const lines=['by'];
  for(const s of steps){
    if(['introduce','assume'].includes(s.kind))lines.push('  intro '+s.name,'  change '+s.type+' at '+s.name);
    else if(s.kind==='obtain')lines.push('  have '+s.copy+' := '+s.source,'  rcases '+s.copy+' with ⟨'+s.name+', '+s.evidenceName+'⟩','  change '+s.type+' at '+s.name,'  change '+s.evidenceType+' at '+s.evidenceName);
    else if(s.kind==='cases'){
      lines.push('  have '+s.name+' : '+s.type+' := by','    cases '+s.source+' with');
      for(const branch of s.branches||[]){
        lines.push('    | '+branch.constructor+' '+branch.name+' =>','      change '+branch.type+' at '+branch.name);
        const body=renderChain(branch.steps).split('\n').slice(1);
        lines.push(...body.map(line=>'    '+line));
      }
    }
    else if(['and-intro','iff-intro'].includes(s.kind)){
      lines.push('  constructor');
      for(const subgoal of s.subgoals||[]){
        lines.push('  ·');
        const body=renderChain(subgoal.steps).split('\n').slice(1);
        lines.push(...body.map(line=>'  '+line));
      }
    }
    else if(s.kind==='exists-intro'){
      lines.push('  refine ⟨'+s.witness+', ?_⟩','  ·');
      const body=renderChain(s.subgoals?.[0]?.steps||[]).split('\n').slice(1);
      lines.push(...body.map(line=>'  '+line));
    }
    else if(s.kind==='define')lines.push('  let '+s.name+' : '+s.type+' := '+s.value);
    else if(s.kind==='establish')lines.push('  have '+s.name+(s.type===null?'':' : '+s.type)+' := '+(s.application==='?'?'by exact?':s.application));
    else {
      if(s.type!=null)lines.push('  show '+s.type);
      lines.push(s.application==='?'?'  exact?':'  exact '+s.application);
    }
  }
  return lines.join('\n');
}
