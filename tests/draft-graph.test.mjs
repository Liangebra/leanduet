import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof} from '../web/natural-draft.mjs';
import {dependentNodes} from '../web/draft-graph.mjs';
test('object identity is independent of display names within the same introduction order',()=>{
 const a=draftProof('establish hp : $P$ | from h\n$Q$ | from hp and f',['P','Q','h','f'],new Map([['h','P ∧ P'],['f','P → Q']]));
 const b=draftProof('establish renamed : $X$ | from k\n$Y$ | from renamed and g',['X','Y','k','g'],new Map([['k','X ∧ X'],['g','X → Y']]));
 const x=a.graph.nodes.at(-2),y=b.graph.nodes.at(-2);
 assert.equal(x.id,y.id);assert.deepEqual(x.formula.tree,y.formula.tree);
 assert.equal(x.alternatives.length,2);assert.equal(x.selectedCandidate,null);
 assert.deepEqual(a.graph.nodes.at(-1).dependencies,b.graph.nodes.at(-1).dependencies);
 assert.deepEqual(dependentNodes(a.graph,['context:2']),['context:2','line:1','line:2']);
});
test('same proposition does not collapse distinct local objects or candidate edges',()=>{
 const facts=new Map([['h1','P'],['h2','P']]);
 const r=draftProof('由 $P$ 得到 $P$',['P','h1','h2'],facts);
 const n=r.graph.nodes.at(-1);
 assert.equal(n.alternatives.length,2);
 assert.notDeepEqual(n.alternatives[0].dependencies,n.alternatives[1].dependencies);
 assert.equal(n.selectedCandidate,null);
 assert.deepEqual(n.dependencies,['context:0']);
});
test('ambiguous local names are not silently bound',()=>{
 const r=draftProof('$P$',['P','P'],new Map([['P','Prop']]));
 assert.equal(r.graph.nodes[0].ambiguousName,true);
 assert.equal(r.graph.nodes[1].ambiguousName,true);
 assert.deepEqual(r.graph.nodes.at(-1).formula.unresolvedNames,['P']);
});
test('formula dependencies and candidate dependencies are distinguishable',()=>{
 const r=draftProof('$P$ | h',['P','h'],new Map([['h','P']]));
 const n=r.graph.nodes.at(-1);
 assert.deepEqual(n.formula.refs,['context:0']);
 assert.deepEqual(n.dependencies,['context:0','context:1']);
});
