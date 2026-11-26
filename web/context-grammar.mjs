// A small relational semantic parser: explicit premise identities and a
// goal constrain inference schemas. This is a candidate generator, not Lean.
import {compileFormula} from './math-formula.mjs';
const simple=/^[A-Za-z_][A-Za-z0-9_']{0,63}$/;
const binary=(a,op)=>a?.kind==='binary'&&a.op===op;
const equal=(a,b)=>!!a&&!!b&&JSON.stringify(a)===JSON.stringify(b);
const parsedTypes=new Map();
const parse=s=>{
 if(typeof s!=='string'||s.length>3000)return null;
 if(parsedTypes.has(s))return parsedTypes.get(s);
 let result=null;try{result=compileFormula(s).scoped;}catch{}
 if(parsedTypes.size>=256)parsedTypes.delete(parsedTypes.keys().next().value);
 parsedTypes.set(s,result);return result;
};
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

// A formula citation identifies a set of possible local declarations,
// not an arbitrary proof of the same proposition. Delimiters protect
// conjunctions, commas and quantifier bodies inside formulas.
const formulaToken=/\$[^$\n]+\$|\\\([^]*?\\\)|\\\[[^]*?\\\]/g;
export function formulaPremiseSentence(body){
 const hits=[...body.matchAll(formulaToken)];
 if(hits.length<2||hits.length>5)return null;
 const last=hits.at(-1);
 if(!/^[。.]?$/.test(body.slice(last.index+last[0].length).trim()))return null;
 const head=/^(?:由|根据|利用|from\s+|using\s+)\s*/iu.exec(body);
 if(!head)return null;
 const beforeGoal=body.slice(head[0].length,last.index);
 const bridge=/(?:[，,]\s*)?(?:可知|可得|得到|推出|we obtain|we get|it follows that|yields)\s*[:：]?\s*$/iu.exec(beforeGoal);
 if(!bridge)return null;
 const premiseText=beforeGoal.slice(0,bridge.index).trim().replace(/[,，]$/,'').trim();
 const refs=[];let cursor=0;
 // Tokenize one citation at a time; separators must occur outside math.
 const token=/^(?:\$[^$\n]+\$|\\\([^]*?\\\)|\\\[[^]*?\\\]|[A-Za-z_][A-Za-z0-9_']{0,63})/;
 while(cursor<premiseText.length){
   const m=token.exec(premiseText.slice(cursor));if(!m)return null;
   const text=m[0];refs.push({kind:simple.test(text)?'name':'formula',text});
   cursor+=text.length;
   if(cursor===premiseText.length)break;
   const sep=/^\s*(?:[,，、]|与|和|\band\b)\s*/iu.exec(premiseText.slice(cursor));
   if(!sep)return null;cursor+=sep[0].length;
   if(cursor===premiseText.length)return null;
 }
 if(!refs.length||refs.length>4||!refs.some(r=>r.kind==='formula'))return null;
 return {kind:'formula-citation-frame',refs,goal:last[0]};
}
export function citationCandidates(frame,scope,facts,{limit=8}={}){
 const available=[...facts.keys()].filter(n=>scope.filter(x=>x===n).length===1&&simple.test(n));
 const choices=frame.refs.map(ref=>{
   if(ref.kind==='name')return available.includes(ref.text)?[ref.text]:[];
   const target=parse(ref.text);
   return available.filter(n=>equal(parse(facts.get(n)),target));
 });
 if(choices.some(x=>!x.length))return {candidates:[],overflow:false,choices};
 let combinations=1;
 for(const c of choices)combinations*=c.length;
 // Do not silently resolve a truncated ambiguity by retaining one candidate.
 if(combinations>32)return {candidates:[],overflow:true,choices};
 const out=[],seen=new Set();let overflow=false;
 function visit(i,names){
   if(i<choices.length){for(const n of choices[i])visit(i+1,[...names,n]);return;}
   for(const c of contextCandidates(frame.goal,names,facts)){
     const key=JSON.stringify([c.term,c.premises]);
     if(seen.has(key))continue;seen.add(key);
     if(out.length>=limit){overflow=true;continue;}out.push(c);
   }
 }
 visit(0,[]);
 return {candidates:out,overflow,choices};
}
