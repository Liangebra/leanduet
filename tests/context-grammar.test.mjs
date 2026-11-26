import test from 'node:test';
import assert from 'node:assert/strict';
import {contextCandidates,factsFromScope,formulaPremiseSentence,citationCandidates,implicitCandidates} from '../web/context-grammar.mjs';
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

test('mathematical formula citations resolve by actual local identities',()=>{
 const facts=new Map([['hab','a = b'],['hbc','b = c']]);
 const draft='由 $a=b$ 与 $b=c$ 可得 $a=c$';
 const r=draftProof(draft,['hab','hbc'],facts);
 assert.equal(r.term,'by\n  show (a = c)\n  exact Eq.trans hab hbc');
 const p=interpretations(draft,['hab','hbc'],facts);
 assert.equal(p.alternatives[0].term,'Eq.trans hab hbc');
 assert.deepEqual(p.alternatives[0].required,['hab','hbc']);
});
test('identical formulas do not identify their proofs',()=>{
 const facts=new Map([['h1','a = b'],['h2','a = b'],['h3','b = c']]);
 const r=draftProof('From $a=b$ and h3, we obtain $a=c$',[...facts.keys()],facts);
 assert.equal(r.term,null);
 assert.deepEqual(r.rows[0].candidates.map(c=>c.term),['Eq.trans h1 h3','Eq.trans h2 h3']);
});
test('unsupported qualifiers and unbound citations are not discarded',()=>{
 const frame=formulaPremiseSentence('由 $a=b$ 和 $b=c$ 可得 $a=c$');
 assert.equal(citationCandidates(frame,['h'],new Map([['h','a=b']])).candidates.length,0);
 assert.equal(formulaPremiseSentence('由 $a=b$ 与 $b=c$ 一致地得到 $a=c$'),null);
});

test('a named mathematical rule retrieves premises without requiring their names in prose',()=>{
 const facts=new Map([['firstProof','a=b'],['secondProof','b=c'],['unused','Q']]);
 const r=draftProof('由等式传递性得到 $a=c$',[...facts.keys()],facts);
 assert.equal(r.term,'by\n  show (a = c)\n  exact Eq.trans firstProof secondProof');
 const renamed=new Map([['u','a=b'],['v','b=c'],['unused','Q']]);
 assert.equal(draftProof('由等式传递性得到 $a=c$',[...renamed.keys()],renamed).rows[0].step.application,'Eq.trans u v');
});
test('a bare conclusion exposes possible inference without asserting author intent',()=>{
 const facts=new Map([['h','P ∧ P']]);
 const r=draftProof('因此 $P$',['h'],facts);
 assert.equal(r.rows[0].step.application,'?');
 assert.deepEqual(r.rows[0].candidates.map(x=>x.term),['And.left h','And.right h']);
 const p=interpretations('$P$',['h'],facts);
 assert.deepEqual(p.alternatives.map(x=>x.term),['And.left h','And.right h','']);
});
test('indexed retrieval keeps ambiguity and excludes irrelevant premises',()=>{
 const facts=new Map([['h1','a=b'],['h2','a=b'],['h3','b=c'],['bad','b=d']]);
 const r=implicitCandidates('a=c',[...facts.keys()],facts,{rule:'Eq.trans',limit:1});
 assert.equal(r.overflow,true);
 assert.equal(r.candidates.length,1);
 assert.equal(draftProof('由等式传递性得到 $a=c$',[...facts.keys()],facts).term,null);
});

test('Lean application syntax participates in citations and contextual inference',()=>{
 const facts=new Map([['h','P x'],['f','P x → Q x']]);
 assert.deepEqual(contextCandidates('(Q x)',['h','f'],facts).map(c=>c.term),['f h']);
 assert.equal(draftProof('由 $P(x)$ 与 f 得到 $Q(x)$',['h','f'],facts).rows[0].step.application,'f h');
});
test('universal specialization uses typed local witnesses and preserves nested binders',()=>{
 const facts=new Map([['h','∀ x : Nat, ∃ y : Nat, R x y'],['a','Nat'],['b','Int']]);
 const r=implicitCandidates('(∃ z : Nat, R a z)',[...facts.keys()],facts);
 assert.deepEqual(r.candidates.map(c=>c.term),['h a']);
 assert.equal(contextCandidates('(∃ z : Nat, R b z)',['h','b'],facts).length,0);
 assert.equal(contextCandidates('(∃ z : Nat, R z z)',['h','a'],facts).length,0);
});
test('bounded math citations match the generated Lean binder representation',()=>{
 const facts=new Map([['h','∀ x, x ∈ S → P x']]);
 const frame=formulaPremiseSentence('由 $∀ y ∈ S, P(y)$ 可得 $∀ z ∈ S, P(z)$');
 assert.equal(citationCandidates(frame,['h'],facts).candidates[0].term,'h');
});
