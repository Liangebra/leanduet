import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof} from '../web/natural-draft.mjs';
import {reconcileDraftIdentity,migrateDraftChoices} from '../web/draft-identity.mjs';
const scope=['P','Q','h','f'];
const facts=new Map([['h','P ∧ P'],['f','P → Q']]);
const original='establish hp : $P$ | from h\n$Q$ | from hp and f';
const graph=(s,ctx=facts,choices=new Map())=>draftProof(s,scope,ctx,{choices}).graph;
test('unique unchanged occurrences retain identity when source lines move',()=>{
 const choices=new Map([[1,'And.right h']]);
 const old=reconcileDraftIdentity(null,graph(original,facts,choices));
 const current=reconcileDraftIdentity(old,graph('\n'+original));
 assert.equal(current.ids.get('line:2'),old.ids.get('line:1'));
 assert.equal(current.ids.get('line:3'),old.ids.get('line:2'));
 assert.deepEqual([...migrateDraftChoices(old,current,choices)],[[2,'And.right h']]);
});
test('changing a statement does not automatically transfer its identity or selection',()=>{
 const choices=new Map([[1,'And.right h']]);
 const old=reconcileDraftIdentity(null,graph(original,facts,choices));
 const current=reconcileDraftIdentity(old,graph(original.replace('from h','And.right using h')));
 assert.notEqual(current.ids.get('line:1'),old.ids.get('line:1'));
 assert.equal(migrateDraftChoices(old,current,choices).size,0);
});
test('same wording with ambiguous repeated occurrences is not reconciled',()=>{
 const old=reconcileDraftIdentity(null,graph('$P$\n$Q$'));
 const current=reconcileDraftIdentity(old,graph('$P$\n$P$\n$Q$'));
 assert.notEqual(current.ids.get('line:1'),old.ids.get('line:1'));
 assert.notEqual(current.ids.get('line:2'),old.ids.get('line:1'));
});
test('changed context conservatively retires all identities and choices',()=>{
 const choices=new Map([[1,'And.right h']]);
 const old=reconcileDraftIdentity(null,graph(original,facts,choices));
 const current=reconcileDraftIdentity(old,graph(original,new Map([...facts,['h','P']])));
 assert.notEqual(current.ids.get('context:0'),old.ids.get('context:0'));
 assert.equal(migrateDraftChoices(old,current,choices).size,0);
});
test('unchanged formula references cannot point to a newly introduced object unnoticed',()=>{
 const old=reconcileDraftIdentity(null,graph('establish hp : $P$\n$hp = hp$'));
 const current=reconcileDraftIdentity(old,graph('establish hp : $Q$\n$hp = hp$'));
 assert.notEqual(current.ids.get('line:2'),old.ids.get('line:2'));
});

test('a selected type hole survives harmless source edits, but not contradictory constraints',()=>{
 const ctx=new Map([['h','P ∧ Q'],['f','P → R']]),sc=['P','Q','R','h','f'];
 const input='建立 hp : $?$,由 h\n$R$';
 const choices=new Map([[1,'And.right h']]);
 const old=reconcileDraftIdentity(null,draftProof(input,sc,ctx,{choices}).graph);
 const unselected=reconcileDraftIdentity(old,draftProof('\n'+input,sc,ctx).graph);
 assert.equal(unselected.ids.get('line:2'),old.ids.get('line:1'));
 assert.deepEqual([...migrateDraftChoices(old,unselected,choices)],[[2,'And.right h']]);
 const incompatible=reconcileDraftIdentity(old,draftProof('建立 hp : $?$,由 h\n由 hp 与 f 得到 $R$',sc,ctx).graph);
 assert.equal(incompatible.ids.get('line:1'),old.ids.get('line:1'));
 assert.equal(migrateDraftChoices(old,incompatible,choices).size,0);
});
