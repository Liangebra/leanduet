import {compileFormula} from './math-formula.mjs';
import {parseRuleIntent} from './rule-intent.mjs';
import {renderChain} from './proof-chain.mjs';
const marker=/^(?:(?:therefore|hence|thus|clearly|obviously|indeed|then)(?:\s*[,，:：]\s*|\s+)|(?:因此|从而|于是|显然|事实上|故|则)[，、：:\s]*)/iu;
const formulaPattern=/\$[^$\n]+\$|\\\([^]*?\\\)|\\\[[^]*?\\\]/g;
const namePattern=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
function unwrap(s){let body=s.trim(),modifiers=[];for(let i=0;i<4;i++){const m=marker.exec(body);if(!m)break;modifiers.push(m[0].trim());body=body.slice(m[0].length);}return {body,modifiers};}
function parseLine(raw){
 const {body,modifiers}=unwrap(raw);
 const occurrences=[...body.matchAll(formulaPattern)];
 if(occurrences.length!==1)throw Error('Write one delimited proposition in each inference.');
 const f=occurrences[0],formula=f[0],before=body.slice(0,f.index).trim(),after=body.slice(f.index+formula.length).trim().replace(/[。.]$/,'').trim();
 let name=null,ruleText='',conclusion=false;
 const binding=/^(?:建立|记|令|let|establish|have|置く|示す)\s*([A-Za-z_][A-Za-z0-9_']{0,63})\s*[:：]$/iu.exec(before);
 if(binding){name=binding[1];ruleText=after.replace(/^[,，|；;]\s*/,'');}
 else if(/^(?:结论|证明|推出|conclude|show|therefore|示す)\s*[:：]?$/iu.test(before)){conclusion=true;ruleText=after.replace(/^[,，|；;]\s*/,'');}
 else if(!before){ruleText=after.replace(/^[,，|；;]\s*/,'');}
 else{
  const forward=/^(?:由|利用|应用|by\s+|using\s+)(.+?)\s*(?:[，,]\s*)?(?:得到|可得|推出|we obtain|we get|gives|yields|を得る)\s*[:：]?$/iu.exec(before);
  if(!forward||after)throw Error('Unrecognized mathematical wording; retained without guessing.');
  ruleText=forward[1].trim().replace(/[,，]$/,'').trim();
 }
 return {raw,formula,type:compileFormula(formula).lean,name,ruleText,conclusion,modifiers};
}
export function draftProof(input,scope=[]){
 if(typeof input!=='string'||input.length>12000)throw Error('Draft exceeds 12000 characters.');
 const lines=input.split(/\r?\n/).map((raw,i)=>({raw,line:i+1})).filter(x=>x.raw.trim());
 if(lines.length>16)throw Error('Use at most sixteen inference lines.');
 const occupied=new Set(scope),visible=new Set(scope.filter((x,i)=>scope.indexOf(x)===i&&scope.lastIndexOf(x)===i));
 let serial=1;const rows=[],steps=[];let blocked=false;
 for(let i=0;i<lines.length;i++){
   const {raw,line}=lines[i];
   try{
    const p=parseLine(raw),last=i===lines.length-1;
    if(p.conclusion&&!last)throw Error('A conclusion must be the last inference.');
    if(last&&p.name)throw Error('The final inference must conclude the goal, not name a fact.');
    let application='?';
    if(p.ruleText&&p.ruleText!=='?'){
      const words=p.ruleText.split(/\s+/);
      if(words.length<=9&&words.every(w=>namePattern.test(w)&&visible.has(w)))application=words.join(' ');
      else {
       const r=parseRuleIntent(p.ruleText,{ordered:true});
       if(!r.rule||r.required.some(x=>!visible.has(x)))throw Error('Unknown or ambiguous premise; check scope and wording.');
       if(occupied.has(r.rule)&&!visible.has(r.rule))throw Error('Ambiguous local rule.');
       application=[r.rule,...r.required].join(' ');
      }
    }
    let step;
    if(last)step={kind:'conclude',type:p.type,application};
    else{
      let name=p.name;
      if(name&&occupied.has(name))throw Error('This intermediate name already exists.');
      if(!name){do{name='duet_h'+serial++;}while(occupied.has(name));}
      occupied.add(name);visible.add(name);
      step={kind:'establish',name,type:p.type,application};
    }
    rows.push({...p,line,status:blocked?'provisional':'translated',step});steps.push(step);
   }catch(e){blocked=true;rows.push({raw,line,status:'unresolved',reason:e.message});}
 }
 const complete=lines.length>0&&!blocked&&steps.at(-1)?.kind==='conclude';
 return {rows,steps,complete,term:complete?renderChain(steps):null};
}
export function compileNaturalDraft(input,scope){
 const r=draftProof(input,scope);
 if(!r.complete){const unresolved=r.rows.find(x=>x.status==='unresolved');throw Error(unresolved?'Line '+unresolved.line+': '+unresolved.reason:'No complete conclusion.');}
 return r;
}
