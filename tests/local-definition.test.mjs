import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,createDraftSession} from '../web/natural-draft.mjs';
import {dependentNodes} from '../web/draft-graph.mjs';
import {reconcileDraftIdentity} from '../web/draft-identity.mjs';
const facts=new Map([['f','Nat → Nat'],['x','Nat'],['h','∀ z : Nat, P z']]);
const scope=['P',...facts.keys()];
test('a typed local definition extends context with a value, not an equality proof',()=>{
 const r=draftProof('令 y : $Nat$ := $f(x)$\n由 h 与 y 得到 $P(y)$',scope,facts);
 assert.equal(r.complete,true);
 assert.equal(r.term,'by\n  let y : Nat := (f x)\n  show (P y)\n  exact h y');
 const n=r.graph.nodes.at(-2);
 assert.equal(n.kind,'define');assert.deepEqual(n.value.refs,['context:1','context:2']);
 assert.deepEqual(dependentNodes(r.graph,['context:2']),['context:2','line:1','line:2']);
});
test('definitions reject duplicates, forward and self references; not proof holes',()=>{
 for(const s of ['令 x : $Nat$ := $f(x)$\n$P(x)$','令 y : $Nat$ := $y$\n$P(y)$','令 y : $Nat$ := $z$\n令 z : $Nat$ := $x$\n$P(y)$','令 y : $Nat$ := $x$']){
  const r=draftProof(s,scope,facts);assert.equal(r.term,null,s);
  assert.equal(r.rows[0].step,undefined,s);
 }
});
test('definition values and open dependencies survive incremental reuse',()=>{
 const s=createDraftSession();
 const input='建立 hp : $P(x)$\n令 y : $Nat$ := $f(x)$\n$P(y)$';
 s.evaluate(input,scope,facts);
 const next=input.replace('$P(y)$','$P(y)$ | h y');
 const a=s.evaluate(next,scope,facts),b=draftProof(next,scope,facts);
 assert.equal(a.reusedRows,2);assert.deepEqual(a.rows,b.rows);assert.deepEqual(a.graph,b.graph);
});
test('a changed definition retires the identity of its dependent formula',()=>{
 const old=reconcileDraftIdentity(null,draftProof('令 y : $Nat$ := $x$\n$P(y)$',scope,facts).graph);
 const next=reconcileDraftIdentity(old,draftProof('令 y : $Nat$ := $f(x)$\n$P(y)$',scope,facts).graph);
 assert.notEqual(next.ids.get('line:2'),old.ids.get('line:2'));
});
