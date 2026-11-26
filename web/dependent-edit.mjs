// Construct a candidate only. The local Lean backend elaborates and checks it.
export function witnessTerm(witness,evidence){
  if(typeof witness!=='string'||typeof evidence!=='string'||!witness.trim()||!evidence.trim())throw Error('A witness and its dependent evidence are both required.');
  const term='Exists.intro ('+witness.trim()+') ('+evidence.trim()+')';
  if(term.length>16000)throw Error('Replacement term is too long.');
  return term;
}
