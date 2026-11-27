// Finite type-domain constraint propagation for a missing intermediate
// proposition. The current supported domain is projections of a cited
// conjunction; pruning is evidence about supported schemas, not Lean
// provability or authorial intent.
import {compileFormula,renderFormula} from './math-formula.mjs';
import {premiseFrame,contextCandidates} from './context-grammar.mjs';
export function constrainProposition({name,source},scope,facts,future){
 if(!scope.includes(source)||!facts.has(source))return {domain:[],candidates:[],constraints:[],reason:'The cited source is not a typed local premise.'};
 let tree;
 try{tree=compileFormula(facts.get(source),{syntax:'lean'}).ast;}catch{}
 if(tree?.kind!=='binary'||tree.op!=='∧')return {domain:[],candidates:[],constraints:[],reason:'This proposition hole requires a cited conjunction in the current grammar.'};
 const domain=[
  {schema:'left conjunction elimination',term:'And.left '+source,type:renderFormula(tree.left),premises:[source]},
  {schema:'right conjunction elimination',term:'And.right '+source,type:renderFormula(tree.right),premises:[source]}
 ];
 const constraints=[];
 let remaining=[...domain];
 for(const row of future){
  const p=row.parsed;
  if(!p?.type||p.kind||p.citation)continue;
  const frame=premiseFrame(p.forwardText||p.ruleText||'',[...scope,name]);
  if(!frame?.premises.includes(name))continue;
  // Only explicit relations whose other premises already have known
  // types can constrain this domain. Unsupported rows do not prune it.
  if(frame.premises.some(n=>n!==name&&!facts.has(n)))continue;
  const compatible=domain.filter(candidate=>{
   const extended=new Map(facts);extended.set(name,candidate.type);
   return contextCandidates(p.type,frame.premises,extended).length>0;
  });
  constraints.push({line:row.line,status:compatible.length?'matched':'unsupported',compatible:compatible.map(c=>c.term)});
  if(compatible.length)remaining=remaining.filter(c=>compatible.includes(c));
 }
 return {domain,candidates:remaining,constraints,reason:remaining.length?'':'No joint structural match for the subsequent explicit constraints.'};
}
