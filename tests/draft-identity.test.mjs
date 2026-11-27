import test from 'node:test';
import assert from 'node:assert/strict';
import {draftProof,compileNaturalDraft} from '../web/natural-draft.mjs';
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
test('ambiguous duplicates stay fresh while a repeated step after a unique anchor keeps identity',()=>{
 const old=reconcileDraftIdentity(null,graph('$P$\n$Q$\n$P$'));
 const current=reconcileDraftIdentity(old,graph('$P$\n$P$\n$Q$\n$P$'));
 assert.notEqual(current.ids.get('line:1'),old.ids.get('line:1'));
 assert.notEqual(current.ids.get('line:2'),old.ids.get('line:1'));
 assert.equal(current.ids.get('line:4'),old.ids.get('line:3'));
});
test('deleting one repeated step preserves only the uniquely anchored suffix',()=>{
 const old=reconcileDraftIdentity(null,graph('$P$\n$P$\n$Q$\n$P$'));
 const current=reconcileDraftIdentity(old,graph('$P$\n$Q$\n$P$'));
 assert.notEqual(current.ids.get('line:1'),old.ids.get('line:1'));
 assert.notEqual(current.ids.get('line:1'),old.ids.get('line:2'));
 assert.equal(current.ids.get('line:2'),old.ids.get('line:3'));
 assert.equal(current.ids.get('line:3'),old.ids.get('line:4'));
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

test('branch-local candidate choices follow their scoped proof identity after line shifts',()=>{
 const ctx=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ Q'],['p1','P'],['p2','P']]);
 const input='cases h, establish hR : $P$\n  left case hp\n    $P$\n  right case hq\n    $P$\n$P$ | hR';
 const choices=new Map([[3,'hp'],[5,'p1']]);
 const original=compileNaturalDraft(input,[...ctx.keys()],ctx,{goal:'P',choices});
 const old=reconcileDraftIdentity(null,original.graph);
 const shifted=reconcileDraftIdentity(old,compileNaturalDraft('\n'+input,[...ctx.keys()],ctx,{goal:'P'}).graph);
 const migrated=migrateDraftChoices(old,shifted,choices);
 assert.deepEqual([...migrated].sort((a,b)=>a[0]-b[0]),[[4,'hp'],[6,'p1']]);
 assert.equal(shifted.ids.get('root/case:2:inl:binding'),old.ids.get('root/case:1:inl:binding'));
});

test('candidate selection and graph identities use physical lines inside branches and continuation',()=>{
 const ctx=new Map([['P','Prop'],['Q','Prop'],['h','P ∨ Q'],['p1','P'],['p2','P']]);
 const input='cases h, establish hR : $P$\n  left case hp\n    establish ha : $P$ | hp\n\n    $P$\n  right case hq\n    $P$\n$P$ | hR\n\n$P$';
 const choices=new Map([[5,'hp'],[7,'p1'],[10,'hR']]);
 const r=compileNaturalDraft(input,[...ctx.keys()],ctx,{goal:'P',choices});
 assert.deepEqual(r.rows.map(row=>row.line),[1,3,5,7,8,10]);
 assert.equal(r.rows.find(row=>row.line===5).step.application,'hp');
 assert.equal(r.rows.find(row=>row.line===7).step.application,'p1');
 assert.equal(r.rows.find(row=>row.line===10).step.application,'hR');
 const before=reconcileDraftIdentity(null,r.graph);
 const edited=input.replace('    establish ha : $P$ | hp\n\n','    establish ha : $P$ | hp\n\n\n');
 const shifted=reconcileDraftIdentity(before,compileNaturalDraft(edited,[...ctx.keys()],ctx,{goal:'P',choices:new Map([[6,'hp'],[8,'p1'],[11,'hR']])}).graph);
 assert.deepEqual([...migrateDraftChoices(before,shifted,choices)].sort((a,b)=>a[0]-b[0]),[[6,'hp'],[8,'p1'],[11,'hR']]);
});

test('candidate choices inside child goals follow a unique unchanged subgoal after line shifts',()=>{
 const ctx=new Map([['p1','P'],['p2','P'],['q','Q']]),sc=[...ctx.keys()];
 const input='split conjunction\n  first goal\n    $P$\n  second goal\n    $Q$ | q';
 const choices=new Map([[3,'p1']]);
 const oldResult=compileNaturalDraft(input,sc,ctx,{goal:'P ∧ Q',choices});
 const old=reconcileDraftIdentity(null,oldResult.graph);
 const shiftedText=input.replace('  first goal\n','  first goal\n\n');
 const shiftedResult=compileNaturalDraft(shiftedText,sc,ctx,{goal:'P ∧ Q'});
 const shifted=reconcileDraftIdentity(old,shiftedResult.graph);
 assert.equal(shifted.ids.get('root/subgoal:1:first/line:4'),old.ids.get('root/subgoal:1:first/line:3'));
 assert.deepEqual([...migrateDraftChoices(old,shifted,choices)],[[4,'p1']]);
});
