// Resolve explicit discourse references against preceding introduction
// occurrences. The target proposition constrains the referent; recency alone
// is never used to choose an "above result".
import {contextCandidates} from './context-grammar.mjs';
const simple=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
export function discourseFrame(text){
 const m=/^(?:由|根据|利用|使用|from\s+|using\s+)(.+)$/iu.exec(text.trim());
 if(!m)return null;
 const tokens=m[1].trim().split(/\s*(?:[,，、]|与|和|\band\b)\s*/iu);
 if(!tokens.length||tokens.length>4)return null;
 const refs=tokens.map(token=>{
  if(/^(?:上述结论|前述结论|the above result|an earlier result)$/iu.test(token))return {kind:'earlier'};
  if(/^(?:上一步结论|上一结论|the previous result)$/iu.test(token))return {kind:'previous'};
  if(/^(?:前两步结论|the previous two results)$/iu.test(token))return {kind:'previous-two'};
  const line=/^(?:第(\d+)行(?:的结论)?|the result on line (\d+))$/iu.exec(token);
  if(line)return {kind:'line',line:Number(line[1]||line[2])};
  if(simple.test(token))return {kind:'name',name:token};
  return {kind:'unsupported',raw:token};
 });
 return refs.some(r=>!['name','unsupported'].includes(r.kind))?{kind:'discourse-frame',refs}:null;
}
export function discourseCandidates(frame,goal,rows,scope,facts,{limit=8,budget=64}={}){
 const visible=new Set(scope.filter((n,i)=>scope.indexOf(n)===i&&scope.lastIndexOf(n)===i));
 const prior=rows.filter(r=>r.step?.kind==='establish'&&visible.has(r.step.name));
 const domains=frame.refs.map(r=>{
  if(r.kind==='name')return visible.has(r.name)?[[r.name]]:[];
  if(r.kind==='previous')return prior.length?[[prior.at(-1).step.name]]:[];
  if(r.kind==='previous-two')return prior.length>=2?[prior.slice(-2).map(x=>x.step.name)]:[];
  if(r.kind==='line')return prior.filter(x=>x.line===r.line).map(x=>[x.step.name]);
  if(r.kind==='earlier')return prior.map(x=>[x.step.name]);
  return [];
 });
 let combinations=1;for(const d of domains)combinations*=d.length;
 if(combinations>budget)return {candidates:[],overflow:true,domains};
 const candidates=[],seen=new Set();let overflow=false;
 function visit(i,names,referents){
  if(i<domains.length){
   for(const choice of domains[i])visit(i+1,[...names,...choice],[...referents,choice]);
   return;
  }
  if(names.length>4)return;
  for(const c of contextCandidates(goal,names,facts)){
   const key=JSON.stringify([c.term,referents]);
   if(seen.has(key))continue;seen.add(key);
   if(candidates.length>=limit){overflow=true;continue;}
   candidates.push({...c,referents});
  }
 }
 visit(0,[],[]);
 return {candidates,overflow,domains};
}
