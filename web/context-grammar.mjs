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
 let result=null;try{
  // Delimited math and Lean context are distinct concrete syntaxes.
  const syntax=/^\s*(?:\$|\\)/.test(s)||s.includes('\\')?'math':'lean';
  result=compileFormula(s,{syntax}).scoped;
 }catch{}
 if(parsedTypes.size>=256)parsedTypes.delete(parsedTypes.keys().next().value);
 parsedTypes.set(s,result);return result;
};
const isTypeLevelSort=raw=>/^(?:Prop|Type(?:\s+[A-Za-z0-9_'.]+)?|Sort(?:\s+[A-Za-z0-9_'.]+)?)$/.test(String(raw||'').trim());
export function premiseFrame(text,scope){
 const m=/^(?:由|根据|利用|使用|from\s+|using\s+)(.+)$/iu.exec(text.trim());
 if(!m)return null;
 const names=m[1].trim().replace(/[，,。.]$/,'').split(/\s*(?:[,，、]|与|和|\band\b)\s*/iu);
 if(!names.length||names.length>4||names.some(n=>!simple.test(n)||scope.filter(x=>x===n).length!==1))return null;
 return {kind:'premise-frame',premises:names};
}
// Capture-safe removal of the outer binder for a free local witness.
function specialize(tree,witness,depth=0){
 if(tree.kind==='bound'){
  if(tree.index===depth)return {kind:'free',name:witness};
  return tree.index>depth?{kind:'bound',index:tree.index-1}:tree;
 }
 if(tree.kind==='binder')return {...tree,domain:tree.domain?specialize(tree.domain,witness,depth):null,body:specialize(tree.body,witness,depth+1)};
 if(tree.kind==='binary')return {...tree,left:specialize(tree.left,witness,depth),right:specialize(tree.right,witness,depth)};
 if(tree.kind==='unary')return {...tree,body:specialize(tree.body,witness,depth)};
 if(tree.kind==='call')return {...tree,fn:specialize(tree.fn,witness,depth),args:tree.args.map(a=>specialize(a,witness,depth))};
 return tree;
}
export function contextCandidates(goal,names,facts){
 const target=parse(goal),out=[],seen=new Set();
 if(!target||!Array.isArray(names)||names.length<1||names.length>4||names.some(n=>!simple.test(n)))return out;
 const classified=names.map(name=>{
  const raw=facts.get(name)||'';
  return {name,raw,type:parse(raw),isSort:isTypeLevelSort(raw)};
 });
 // Lean sorts describe types, even when the surface formula parser can read
 // the sort name as a free token. They are context declarations, not proof
 // premises. Other unparsed local types keep this search conservative.
 if(classified.some(entry=>!entry.type&&!entry.isSort))return out;
 const entries=classified.filter(entry=>entry.type&&!entry.isSort);
 if(!entries.length)return out;
 function add(schema,rule,args){
  const term=[rule,...args].join(' ');
  if(seen.has(term))return;
  const referenced=new Set([rule,...args].flatMap(part=>String(part).match(/[A-Za-z_][A-Za-z0-9_']*/g)||[]));
  const premises=names.filter(name=>referenced.has(name));
  seen.add(term);out.push({schema,term,premises,arguments:args,rule});
 }
 if(entries.length===1){
  const {name,type:t}=entries[0];
  if(equal(t,target))add('exact premise',name,[]);
  if(binary(t,'∧')){
   if(equal(t.left,target))add('left conjunction elimination','And.left',[name]);
   if(equal(t.right,target))add('right conjunction elimination','And.right',[name]);
  }
  if(binary(t,'=')&&binary(target,'=')&&equal(t.left,target.right)&&equal(t.right,target.left))add('equality symmetry','Eq.symm',[name]);
  if(equal(t,parse('False')))add('false elimination','False.elim',[name]);
 }
 if(entries.length===2){
  for(const [a,b] of [entries,[entries[1],entries[0]]]){
   if(binary(a.type,'→')&&equal(a.type.left,b.type)&&equal(a.type.right,target))add('implication elimination',a.name,[b.name]);
   if(target.kind==='binder'&&target.op==='∃'&&equal(target.domain,a.type)&&equal(specialize(target.body,a.name),b.type))add('existential introduction','Exists.intro',[a.name,b.name]);
   if(a.type.kind==='binder'&&a.type.op==='∀'&&equal(a.type.domain,b.type)&&equal(specialize(a.type.body,b.name),target))add('universal specialization',a.name,[b.name]);
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
 if(entries.length===3){
  for(let i=0;i<3;i++)for(let j=0;j<3;j++){
   if(i===j)continue;
   const a=entries[i],b=entries[j],e=entries[3-i-j];
   // For an inferred domain, membership and the specialized formula constrain
   // the witness; Lean must still elaborate its actual type.
   if(a.type.kind==='binder'&&a.type.op==='∀'&&(!a.type.domain||equal(a.type.domain,b.type))){
    const body=specialize(a.type.body,b.name);
    if(binary(body,'→')&&equal(body.left,e.type)&&equal(body.right,target)&&(a.type.domain||binary(body.left,'∈')))add('bounded universal elimination',a.name,[b.name,e.name]);
   }
   if(target.kind==='binder'&&target.op==='∃'&&!target.domain){
    const body=specialize(target.body,a.name);
    if(binary(body,'∧')&&binary(body.left,'∈')&&equal(body.left,b.type)&&equal(body.right,e.type))add('bounded existential introduction','Exists.intro',[a.name,'(And.intro '+b.name+' '+e.name+')']);
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


// Retrieve premises by formula structure, not by the author's chosen names.
// Only the supported small-arity schemas are searched; no Lean call.
// Index matching uses canonical surface trees, not definitional equality.
export function implicitCandidates(goal,scope,facts,{rule='',limit=8}={}){
 const target=parse(goal);
 if(!target)return {candidates:[],overflow:false};
 const counts=new Map();for(const name of scope)counts.set(name,(counts.get(name)||0)+1);
 const entries=[],types=new Map(),relations=new Map();
 function insert(index,key,entry){if(!index.has(key))index.set(key,[]);index.get(key).push(entry);}
 const key=t=>JSON.stringify(t);
 for(const [name,raw] of facts){
  if(counts.get(name)!==1||!simple.test(name))continue;
  const t=parse(raw);if(!t)continue;
  if(entries.length>=128)return {candidates:[],overflow:true};
  const e={name,t};entries.push(e);insert(types,key(t),e);
  if(t.kind==='binary'&&['=','≤','<'].includes(t.op))insert(relations,key([t.op,t.left,t.right]),e);
 }
 const out=[],seen=new Set();let overflow=false,probes=0;
 function probe(names){
  if(overflow)return;
  if(++probes>4096){overflow=true;return;}
  for(const c of contextCandidates(goal,names,facts)){
   if(rule&&rule!==c.rule||seen.has(c.term))continue;
   seen.add(c.term);
   if(out.length===limit){overflow=true;return;}
   out.push({...c,premiseFacts:c.premises.map(name=>({name,type:facts.get(name)}))});
  }
 }
 const lookup=t=>types.get(key(t))||[];
 for(const e of entries){probe([e.name]);if(overflow)break;}
 if(!overflow)for(const e of entries){
  const t=e.t;
  let partners=[];
  if(binary(t,'→')&&equal(t.right,target))partners.push(...lookup(t.left));
  if(t.kind==='binder'&&t.op==='∀'&&t.domain)partners.push(...lookup(t.domain));
  if(target.kind==='binder'&&target.op==='∃'&&equal(target.domain,t))partners.push(...lookup(specialize(target.body,e.name)));
  if(binary(t,'↔')){
   if(equal(t.right,target))partners.push(...lookup(t.left));
   if(equal(t.left,target))partners.push(...lookup(t.right));
  }
  if(binary(target,'∧')&&equal(t,target.left))partners.push(...lookup(target.right));
  if(t.kind==='binary'&&['=','≤','<'].includes(t.op)&&binary(target,t.op)&&equal(t.left,target.left)){
   partners.push(...(relations.get(key([t.op,t.right,target.right]))||[]));
  }
  for(const p of partners){probe([e.name,p.name]);if(overflow)break;}
  if(overflow)break;
 }
 // Search indexed antecedents/evidence rather than a cubic Cartesian product.
 if(!overflow)for(const h of entries){
  if(h.t.kind!=='binder'||h.t.op!=='∀'||!binary(h.t.body,'→'))continue;
  for(const w of h.t.domain?lookup(h.t.domain):entries){
   const body=specialize(h.t.body,w.name);
   if(!equal(body.right,target)||(!h.t.domain&&!binary(body.left,'∈')))continue;
   for(const evidence of lookup(body.left)){probe([h.name,w.name,evidence.name]);if(overflow)break;}
   if(overflow)break;
  }
  if(overflow)break;
 }
 if(!overflow&&target.kind==='binder'&&target.op==='∃'&&!target.domain&&binary(target.body,'∧')&&binary(target.body.left,'∈')){
  for(const w of entries){
   const body=specialize(target.body,w.name);
   for(const membership of lookup(body.left)){
    for(const evidence of lookup(body.right)){probe([w.name,membership.name,evidence.name]);if(overflow)break;}
    if(overflow)break;
   }
   if(overflow)break;
  }
 }
 return {candidates:out,overflow};
}
export const structuralRules=new Set(['And.left','And.right','And.intro','Eq.symm','Eq.trans','Iff.mp','Iff.mpr','le_trans','lt_trans','Exists.intro','False.elim']);
