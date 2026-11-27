// Finite relational inference over proposition holes. Supported domains are
// distinct projection proofs of a cited conjunction; equality of types does
// not collapse proofs. Relations constrain assignments, not just marginal
// domains. No Lean calls or claims of completeness over mathematical proofs.
import {compileFormula,renderFormula} from './math-formula.mjs';
import {premiseFrame,contextCandidates} from './context-grammar.mjs';

export function projectionDomain(source,scope,facts){
 if(!scope.includes(source)||!facts.has(source))return [];
 let tree;
 try{tree=compileFormula(facts.get(source),{syntax:'lean'}).ast;}catch{}
 if(tree?.kind!=='binary'||tree.op!=='∧')return [];
 return [
  {schema:'left conjunction elimination',term:'And.left '+source,type:renderFormula(tree.left),premises:[source]},
  {schema:'right conjunction elimination',term:'And.right '+source,type:renderFormula(tree.right),premises:[source]}
 ];
}
// Bounded relational join. Keep whole compatible assignments, so a later
// choice cannot independently combine mutually inconsistent marginals.
export function solveFiniteRelations(variables,relations,choices=new Map(),{budget=4096,limit=256}={}){
 const byName=new Map(variables.map(v=>[v.name,v]));
 const names=new Set(byName.keys());
 const domains=new Map(variables.map(v=>[v.name,v.domain.filter(c=>!choices.has(v.line)||choices.get(v.line)===c.term)]));
 const active=relations.filter(r=>r.status==='matched');
 const assignments=[];let explored=0,overflow=false;
 const partial=new Map();
 // Check support even for partial assignments, not only complete tuples.
 function supported(r){
  return r.tuples.some(tuple=>r.names.every((n,i)=>!partial.has(n)||partial.get(n).term===tuple[i]));
 }
 const order=[...variables].sort((a,b)=>domains.get(a.name).length-domains.get(b.name).length||active.filter(r=>r.names.includes(b.name)).length-active.filter(r=>r.names.includes(a.name)).length||a.line-b.line);
 function visit(i){
  if(overflow)return;
  if(++explored>budget){overflow=true;return;}
  if(active.some(r=>!supported(r)))return;
  if(i===order.length){
   if(assignments.length>=limit){overflow=true;return;}
   assignments.push(variables.map(v=>partial.get(v.name).term));return;
  }
  const n=order[i].name;
  if(!names.has(n))return;
  for(const c of domains.get(n)){partial.set(n,c);visit(i+1);if(overflow)break;}
  partial.delete(n);
 }
 visit(0);
 // An incomplete enumeration cannot establish a singleton or contradiction.
 // Do not expose partial marginals as the complete supported domains.
 return {status:overflow?'overflow':!assignments.length?'contradiction':assignments.length===1?'unique':'ambiguous',
  assignments:overflow?[]:assignments,explored,
  candidates:variables.map((v,i)=>overflow?v.domain:v.domain.filter(c=>assignments.some(a=>a[i]===c.term)))};
}
function buildRelation(row,frame,byName,facts){
 const names=[...new Set(frame.premises.filter(n=>byName.has(n)))];
 if(!names.length||frame.premises.some(n=>!byName.has(n)&&!facts.has(n)))return null;
 const tuples=[],extended=new Map(facts);
 function visit(i,terms){
  if(i===names.length){
   if(contextCandidates(row.parsed.type,frame.premises,extended).length)tuples.push(terms);
   return;
  }
  const v=byName.get(names[i]);
  for(const c of v.domain){extended.set(v.name,c.type);visit(i+1,[...terms,c.term]);}
  extended.delete(v.name);
 }
 visit(0,[]);
 return {line:row.line,names,status:tuples.length?'matched':'unsupported',tuples};
}
export function constrainPropositions(first,scope,facts,future,choices=new Map(),excludedLines=new Set()){
 const domain=projectionDomain(first.parsed.source,scope,facts);
 if(!domain.length)return new Map([[first.line,{domain:[],candidates:[],constraints:[],reason:'This proposition hole requires a cited typed conjunction in the current grammar.'}]]);
 const variables=[{line:first.line,name:first.parsed.name,domain}],byName=new Map([[first.parsed.name,variables[0]]]);
 const used=new Set([...scope,first.parsed.name]),relations=[];
 // Independently sourced holes may share relations in the current linear
 // scope. A context-changing operation is a conservative barrier. A future
 // declaration cannot be used before its source occurrence.
 for(const row of future){
  const p=row.parsed;
  if(!p)continue;
  if(['introduce','assume','define'].includes(p.kind))break;
  if(p.kind==='infer-proposition'){
   if(!used.has(p.name)&&!excludedLines.has(row.line)){
    const next=projectionDomain(p.source,scope,facts);
    if(next.length){const v={line:row.line,name:p.name,domain:next};variables.push(v);byName.set(v.name,v);}
   }
   used.add(p.name);continue;
  }
  if(p.type&&!p.kind&&!p.citation){
   const frame=premiseFrame(p.forwardText||p.ruleText||'',[...scope,...byName.keys()]);
   if(frame){const relation=buildRelation(row,frame,byName,facts);if(relation)relations.push(relation);}
  }
  if(p.name)used.add(p.name);
 }
 // Solve each connected component independently. Unsupported relations are
 // reported but never used to eliminate assignments or connect components.
 const pending=new Set(variables.map(v=>v.name)),result=new Map();
 while(pending.size){
  const component=new Set([pending.values().next().value]);
  let changed=true;
  while(changed){
   changed=false;
   for(const r of relations)if(r.status==='matched'&&r.names.some(n=>component.has(n))){
    for(const n of r.names)if(!component.has(n)){component.add(n);changed=true;}
   }
  }
  for(const n of component)pending.delete(n);
  const members=variables.filter(v=>component.has(v.name));
  const linked=relations.filter(r=>r.status==='matched'&&r.names.every(n=>component.has(n)));
  const solved=solveFiniteRelations(members,linked,choices);
  const relevant=relations.filter(r=>r.names.some(n=>component.has(n)));
  const group={id:'constraint:'+members[0].line,variables:members.map(v=>({line:v.line,name:v.name})),
   relations:relevant,status:solved.status,assignments:solved.assignments,explored:solved.explored};
  members.forEach((v,i)=>{
   const constraints=relevant.filter(r=>r.names.includes(v.name)).map(r=>({line:r.line,status:r.status,
    compatible:[...new Set(r.tuples.map(tuple=>tuple[r.names.indexOf(v.name)]))]}));
   result.set(v.line,{domain:v.domain,candidates:solved.candidates[i],constraints,group,
    overflow:solved.status==='overflow',
    reason:solved.status==='contradiction'?'No joint structural match for the subsequent explicit constraints or choices.':solved.status==='overflow'?'Joint constraint search exceeded its budget; specify more candidate choices.':''});
  });
 }
 return result;
}
// Compatibility helper for callers interested in one hole.
export function constrainProposition(parsed,scope,facts,future){
 const line=0;
 return constrainPropositions({line,parsed},scope,facts,future).get(line);
}
