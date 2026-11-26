import test from 'node:test';
import assert from 'node:assert/strict';
import {contextCandidates,factsFromScope} from '../web/context-grammar.mjs';
import {draftProof} from '../web/natural-draft.mjs';
import {interpretations} from '../web/interpretations.mjs';
test('context determines rule and argument order without a Lean invocation',()=>{
 const facts=new Map([['hab','a = b'],['hbc','b = c']]);
 assert.deepEqual(contextCandidates('a = c',['hbc','hab'],facts).map(x=>x.term),['Eq.trans hab hbc']);
 const r=draftProof('由 hbc 与 hab 得到 $a=c$',['hab','hbc'],facts);
 assert.equal(r.term,'by\n  show (a = c)\n  exact Eq.trans hab hbc');
 const p=interpretations('$a=c$，由 hbc 与 hab',['hab','hbc'],facts);
 assert.equal(p.alternatives[0].term,'Eq.trans hab hbc');
 assert.deepEqual(p.alternatives[0].required,['hbc','hab']);
});
test('ambiguous identical conjuncts remain distinct candidate proofs',()=>{
 const facts=new Map([['h','P ∧ P']]);
 const r=draftProof('$P$，由 h',['h'],facts);
 assert.equal(r.term,null);
 assert.deepEqual(r.rows[0].candidates.map(x=>x.term),['And.left h','And.right h']);
 assert.equal(interpretations('$P$，由 h',['h'],facts).alternatives.length,2);
});
test('no silent type or premise invention',()=>{
 assert.deepEqual(contextCandidates('Q',['h'],new Map([['h','P']])),[]);
 assert.equal(factsFromScope([{name:'h',type:'P'},{name:'h',type:'Q'}]).has('h'),false);
 assert.equal(draftProof('由 h 得到 $Q$',['h'],new Map([['h','P']])).complete,false);
});
test('new intermediate facts constrain subsequent rules',()=>{
 const r=draftProof('建立 hq : $Q$，由 f，使用 p\n由 hq 与 g 得到 $R$',['f','p','g'],new Map([['g','Q → R']]));
 assert.match(r.term,/exact g hq/);
});
