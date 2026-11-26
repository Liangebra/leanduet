// A small relational semantic parser: explicit premise identities and a
// goal constrain inference schemas. This is a candidate generator, not Lean.
import {compileFormula} from './math-formula.mjs';
const simple=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
const binary=(a,op)=>a?.kind==='binary'&&a.op===op;
const equal=(a,b)=>!!a&&!!b&&JSON.stringify(a)===JSON.stringify(b);
const parse=s=>{try{return compileFormula(s).scoped;}catch{return null;}};
export function premiseFrame(text,scope){
 const m=/^(?:由|根据|利用|使用|from\s+|using\s+)(.+)$/iu.exec(text.trim());
 if(!m)return null;
 const names=m[1].trim().replace(/[，,。.]$/,'').split(/\s*(?:[,，、]|与|和|\band\b)\s*/iu);
 if(!names.length||names.length>4||names.some(n=>!simple.test(n)||scope.filter(x=>x===n).length!==1))return null;
 return {kind:'premise-frame',premises:names};
}
export function contextCandidates(goal,names,facts){
 const target=parse(goal),out=[],seen=new Set();
 if(!target||!Array.isArray(names)||names.length<1||names.length>4||names.some(n=>!simple.test(n)))return out;
 const entries=names.map(name=>({name,type:parse(facts.get(name)||'')}));
 if(entries.some(e=>!e.type))return out;
 function add(schema,rule,args){
  const term=[rule,...args].join(' ');
  if(seen.has(term))return;
  seen.add(term);out.push({schema,term,premises:[...names],arguments:args,rule});
 }
 if(entries.length===1){
  const {name,type:t}=entries[0];
  if(equal(t,target))add('exact premise',name,[]);
  if(binary(t,'∧')){
   if(equal(t.left,target))add('left conjunction elimination','And.left',[name]);
   if(equal(t.right,target))add('right conjunction elimination','And.right',[name]);
  }
  if(binary(t,'=')&&binary(target,'=')&&equal(t.left,target.right)&&equal(t.right,target.left))add('equality symmetry','Eq.symm',[name]);
 }
 if(entries.length===2){
  for(const [a,b] of [entries,[entries[1],entries[0]]]){
   if(binary(a.type,'→')&&equal(a.type.left,b.type)&&equal(a.type.right,target))add('implication elimination',a.name,[b.name]);
   if(binary(a.type,'↔')){
    if(equal(a.type.left,b.type)&&equal(a.type.right,target))add('equivalence forward','Iff.mp',[''+a.name,b.name]);
    if(equal(a.type.right,b.type)&&equal(a.type.left,target))add('equivalence backward','Iff.mpr',[a.name,b.name]);
   }
   if(binary(target,'∧')&&equal(a.type,target.left)&&equal(b.type,target.right))add('conjunction introduction','And.intro',[a.name,b.name]);
   for(const [op,rule] of [['=','Eq.trans'],['≤','le_trans'],['<','lt_trans']]){
    if(binary(a.type,op)&&binary(b.type,op)&&binary(target,op)&&equal(a.type.right,b.type.left)&&equal(a.type.left,target.left)&&equal(b.type.right,target.right))add('transitivity '+op,rule,[a.name,b.name]);
   }
  }
 }
 return out;
}
export function factsFromScope(scope){
 const result=new Map(),counts=new Map();
 for(const d of scope||[])if(typeof d?.name==='string')counts.set(d.name,(counts.get(d.name)||0)+1);
 for(const d of scope||[])if(counts.get(d?.name)===1&&typeof d.type==='string')result.set(d.name,d.type);
 return result;
}
