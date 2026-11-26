// Explicit, reviewed aliases. Do not silently guess names from arbitrary prose.
// The actual availability and applicability of a declaration is checked by Lean.
export const concepts = [
  {en:'symmetry of equality',zh:'等式对称性',rule:'Eq.symm'},
  {en:'transitivity of equality',zh:'等式传递性',rule:'Eq.trans'},
  {en:'conjunction introduction',zh:'合取引入',rule:'And.intro'},
  {en:'first conjunct',zh:'合取左消去',rule:'And.left'},
  {en:'second conjunct',zh:'合取右消去',rule:'And.right'},
  {en:'equality transport',zh:'等式运输',rule:'Eq.mp'},
  {en:'continuous image of a compact set',zh:'紧集的连续像',rule:'IsCompact.image'},
  {en:'composition of continuous functions',zh:'连续映射的复合',rule:'Continuous.comp'},
  {en:'transitivity of order',zh:'序关系传递性',rule:'le_trans'},
  {en:'subgroup multiplication closure',zh:'子群乘法封闭性',rule:'Subgroup.mul_mem'}
];
export function resolveIntent(value){
  if(typeof value!=='string')throw Error('Expected a mathematical rule or declaration name.');
  const input=value.trim();
  if(!input||input==='automatic'||input==='自动检索')return '';
  const key=input.toLowerCase().replace(/^(?:by |use |apply |由|利用|应用)\s*/i,'').replace(/[。.]$/,'').trim();
  const match=concepts.find(x=>x.en===key||x.zh===key||x.rule.toLowerCase()===key);
  if(match)return match.rule;
  if(/^[A-Za-z_][A-Za-z0-9_'.]{0,159}$/.test(input))return input;
  throw Error('Unsupported phrase. Choose a known mathematical concept, enter an exact Lean declaration, or leave blank for type search.');
}
