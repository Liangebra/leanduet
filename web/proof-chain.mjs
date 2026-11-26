import {parseRuleIntent} from './rule-intent.mjs';
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
  const planned=new Set(lines.map(l=>/^(?:Establish\s+|建立\s+|示す\s+)([A-Za-z_][A-Za-z0-9_']{0,63})(?:\s*:|\s*$)/i.exec(l)?.[1]).filter(Boolean));
  let done=false;
  function application(phrase,line){
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
    if(/^(?:Conclude|结论|結論)$/i.test(left)){
      steps.push({kind:'conclude',application:application(right,i+1)});done=true;continue;
    }
    const m=/^(?:Establish\s+|建立\s+|示す\s+)([A-Za-z_][A-Za-z0-9_']{0,63})(?:\s*:\s*(.+))?$/i.exec(left);
    if(!m||!ident.test(m[1]))throw Error('Line '+(i+1)+': expected Establish name, optionally with : proposition.');
    const [,name,annotation]=m;
    const type=annotation??null;
    if(occupied.has(name))throw Error('Line '+(i+1)+': binding already exists: '+name);
    // Type is an explicit Lean proposition expression, not a translated sentence.
    if(type!==null&&/[;{}]|(?:\/-|--|:=|\b(?:by|sorry|admit)\b)/.test(type))throw Error('Line '+(i+1)+': supply a single Lean proposition expression.');
    steps.push({kind:'establish',name,type,application:application(right,i+1)});
    occupied.add(name);visible.add(name);
  }
  if(!done)throw Error('Finish with Conclude | rule using premises.');
  const term='by\n'+steps.map(s=>s.kind==='establish'?'  have '+s.name+(s.type===null?'':' : '+s.type)+' := '+s.application:'  exact '+s.application).join('\n');
  return {steps,term};
}
