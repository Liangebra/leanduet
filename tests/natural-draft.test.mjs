import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,compileNaturalDraft} from '../web/natural-draft.mjs';
test('Chinese mathematical prose generates named intermediate results without Lean',()=>{
 const d=compileNaturalDraft('建立 hq : $Q$，由 f，使用 p\n因此 $R$，由 g，使用 hq',['P','Q','R','f','g','p']);
 assert.equal(d.term,'by\n  have hq : Q := f p\n  show R\n  exact g hq');
 assert.deepEqual(d.rows[1].modifiers,['因此']);
});
test('English rule-first phrasing and formula-only lines',()=>{
 const d=compileNaturalDraft('By f using p, we obtain $Q$\nHence $R$ | g duet_h1',['f','g','p','Q','R']);
 assert.match(d.term,/have duet_h1 : Q := f p/);
 assert.match(d.term,/exact g duet_h1/);
});
test('unknown assumptions do not vanish and block executable export',()=>{
 const d=draftProof('uniformly $Q$\n$R$',['Q','R']);
 assert.equal(d.complete,false);assert.equal(d.term,null);
 assert.equal(d.rows[0].raw,'uniformly $Q$');assert.equal(d.rows[1].status,'provisional');
});

test('a final inference must match the selected goal, up to bound-variable renaming',()=>{
 const facts=new Map([['P','Prop'],['hp','P']]);
 const mismatch=draftProof('$P$ | hp',['P','hp'],facts,{goal:'Q'});
 assert.equal(mismatch.complete,false);
 assert.equal(mismatch.term,null);
 assert.match(mismatch.rows.at(-1).reason,/remaining goal/);
 const alpha=draftProof('任取 x : $Nat$\n假设 hp : $P(x)$\n$P(x)$ | hp',['P'],new Map(),{goal:'∀ y : Nat, P y → P y'});
 assert.equal(alpha.complete,true);
});

test('future intermediate names cannot masquerade as global declarations',()=>{
 const d=draftProof('$P$ | later\nestablish later : $Q$ | f\n$R$ | g',['f','g']);
 assert.equal(d.complete,false);
 assert.match(d.rows[0].reason,/forward/);
});
test('automatic naming does not collide with a later explicit binding',()=>{
 const d=draftProof('$P$ | f\nestablish duet_h1 : $Q$ | g\n$R$ | h',['f','g','h']);
 assert.equal(d.complete,true);
 assert.equal(d.steps[0].name,'duet_h2');
});

test('ambiguous proofs retain typed intermediate objects without exporting a proof',()=>{
 const facts=new Map([['h','P ∧ P'],['f','P → Q'],['g','Q → R']]);
 const r=draftProof('establish hp : $P$ | from h\nestablish hq : $Q$ | from hp and f\n$R$ | from hq and g',[...facts.keys()],facts);
 assert.equal(r.complete,false);assert.equal(r.term,null);
 assert.equal(r.rows[0].status,'unresolved');
 assert.equal(r.rows[0].step.name,'hp');
 assert.equal(r.rows[0].candidates.length,2);
 assert.equal(r.rows[1].step.application,'f hp');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.deepEqual(r.rows[1].dependencies,['hp']);
 assert.equal(r.rows[2].step.application,'g hq');
 assert.deepEqual(r.openBindings,['hp','hq']);
});
test('formula-only obligations are distinct from verified proofs',()=>{
 const r=draftProof('establish hp : $P$\n$Q$ | f hp',['f']);
 assert.equal(r.complete,true); // structurally exportable for Lean search
 assert.equal(r.rows[0].proofStatus,'open');
 assert.equal(r.rows[1].proofStatus,'depends-on-open');
 assert.match(r.term,/by exact\?/);
});

test('explicit candidate choice resolves an ambiguity without rewriting the original prose',()=>{
 const input='establish hp : $P$ | from h\n$Q$ | from f and hp';
 const facts=new Map([['h','P ∧ P'],['f','P → Q']]);
 const r=draftProof(input,['h','f'],facts,{choices:new Map([[1,'And.right h']])});
 assert.equal(r.complete,true);assert.match(r.term,/have hp : P := And.right h/);
 assert.equal(r.rows[0].raw,input.split('\n')[0]);
 assert.equal(r.rows[1].proofStatus,'candidate');
 assert.equal(r.graph.nodes.at(-2).selectedCandidate,'line:1:candidate:1');
 const stale=draftProof(input,['h','f'],facts,{choices:new Map([[1,'And.right nonexistent']])});
 assert.equal(stale.complete,false);assert.match(stale.rows[0].reason,/no longer available/);
});
test('bare conclusion remains an open search unless the user chooses a candidate',()=>{
 const facts=new Map([['h','P']]);
 const plain=draftProof('$P$',['h'],facts);
 const chosen=draftProof('$P$',['h'],facts,{choices:new Map([[1,'h']])});
 assert.equal(plain.rows[0].proofStatus,'open');
 assert.equal(plain.rows[0].resolutionStatus,'needs-choice');
 assert.equal(chosen.rows[0].step.application,'h');
 assert.equal(chosen.rows[0].proofStatus,'candidate');
 assert.equal(chosen.rows[0].resolutionStatus,'candidate-unverified');
 assert.equal(chosen.leanVerification,'not-run');
 assert.equal(chosen.semanticFidelity,'not-assessed');
 assert.equal(chosen.completionKind,'structural-export-ready');
});

test('draft results separate structural readiness, Lean verification, and semantic fidelity',()=>{
 const result=draftProof('$P$ | hp',['hp'],new Map([['hp','P']]));
 assert.equal(result.complete,true);
 assert.equal(result.completionKind,'structural-export-ready');
 assert.equal(result.leanVerification,'not-run');
 assert.equal(result.semanticFidelity,'not-assessed');
 assert.equal(result.rows[0].resolutionStatus,'candidate-unverified');
 assert.equal(result.graph.nodes.at(-1).resolutionStatus,'candidate-unverified');
});

test('semantic resolution distinguishes unsupported wording, missing context, and unsupported matches',()=>{
 const unsupported=draftProof('I conjecture this statement',['h']);
 assert.equal(unsupported.rows[0].resolutionStatus,'unsupported');
 const missing=draftProof('建立 hp : $?$,由 future\n$P$',['P']);
 assert.equal(missing.rows[0].resolutionStatus,'needs-context');
 const noMatch=draftProof('由 hp 与 f 得到 $Z$',['hp','f'],new Map([['hp','P'],['f','P → Q']]));
 assert.equal(noMatch.rows[0].resolutionStatus,'no-supported-match');
});

test('semantic resolution preserves candidate ambiguity and reports stale choices',()=>{
 const facts=new Map([['h','P ∧ P']]);
 const ambiguous=draftProof('建立 hp : $?$,由 h\n$P$',[...facts.keys()],facts);
 assert.equal(ambiguous.rows[0].resolutionStatus,'ambiguous');
 assert.equal(ambiguous.rows[0].candidates.length,2);
 const stale=draftProof('建立 hp : $?$,由 h\n$P$',[...facts.keys()],facts,{choices:new Map([[1,'And.left missing']])});
 assert.equal(stale.rows[0].resolutionStatus,'incompatible-choice');
});

test('jointly incompatible proposition constraints are not reported as missing context',()=>{
 const facts=new Map([['h','P ∧ Q'],['f','P → R'],['g','Q → R']]);
 const draft='建立 hp : $?$,由 h\n由 hp 与 f 得到 $R$\n由 hp 与 g 得到 $R$';
 const result=draftProof(draft,[...facts.keys()],facts);
 assert.equal(result.rows[0].resolutionStatus,'incompatible-constraints');
 assert.equal(result.rows[0].constraintGroup.status,'contradiction');
});
