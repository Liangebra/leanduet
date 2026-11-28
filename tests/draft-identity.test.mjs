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


const goalGraph=(goal,type='Nat')=>({schema:1,identity:'revision-local',goal,nodes:[
 {id:'context:0',kind:'context',name:'h',type,ambiguousName:false}
]});
test('alpha-renaming a bound goal variable preserves the surrounding object identity',()=>{
 const original=reconcileDraftIdentity(null,goalGraph('∀ n : Nat, n = n'));
 const renamed=reconcileDraftIdentity(original,goalGraph('∀ k : Nat, k = k'));
 assert.equal(renamed.ids.get('context:0'),original.ids.get('context:0'));
 assert.equal(renamed.matches.get('context:0'),'context:0');
});
test('alpha-renaming a binder inside a context type preserves identity but a structural type change retires it',()=>{
 const original=reconcileDraftIdentity(null,goalGraph('R','∀ n : Nat, n = n'));
 const renamed=reconcileDraftIdentity(original,goalGraph('R','∀ k : Nat, k = k'));
 assert.equal(renamed.ids.get('context:0'),original.ids.get('context:0'));
 assert.equal(renamed.matches.get('context:0'),'context:0');
 const changed=reconcileDraftIdentity(original,goalGraph('R','∀ k : Nat, k + 1 = k'));
 assert.notEqual(changed.ids.get('context:0'),original.ids.get('context:0'));
 assert.equal(changed.matches.has('context:0'),false);
});
test('changing a bound goal proposition retires identities even when its binder is renamed',()=>{
 const original=reconcileDraftIdentity(null,goalGraph('∀ n : Nat, n = n'));
 const changed=reconcileDraftIdentity(original,goalGraph('∀ k : Nat, k + 1 = k'));
 assert.notEqual(changed.ids.get('context:0'),original.ids.get('context:0'));
 assert.equal(changed.matches.has('context:0'),false);
});

test('alpha-renamed nested goal scopes reconcile against their shared parent objects',()=>{
 const makeGraph=(goal,childGoal,scopeId)=>({
  schema:1,identity:'revision-local',goal,nodes:[
   {id:'context:0',kind:'context',name:'h',type:'Nat',ambiguousName:false},
   {id:'line:1',kind:'and-intro',origin:'and-intro',raw:'split conjunction',scopeRefs:[],dependencies:[],
    formula:{tree:{kind:'id',value:'P'}},value:null,alternatives:[],
    goalOperation:{kind:'conjunction-introduction',subgoals:[
     {id:'first',scopeId,goal:childGoal,contextDelta:[]}
    ]},
    subgoals:[{id:scopeId,key:'first',kind:'subgoal',goal:childGoal,dependencies:[],graph:{
     goal:childGoal,nodes:[{id:'context:0',kind:'context',name:'h',type:'Nat',ambiguousName:false}]
    }}]
   }
  ]
 });
 const original=reconcileDraftIdentity(null,makeGraph('∀ n : Nat, n = n','∀ n : Nat, n = n','root/subgoal:1:first'));
 const renamed=reconcileDraftIdentity(original,makeGraph('∀ k : Nat, k = k','∀ k : Nat, k = k','root/subgoal:1:first'));
 assert.equal(renamed.ids.get('context:0'),original.ids.get('context:0'));
 assert.equal(renamed.ids.get('root/subgoal:1:first'),original.ids.get('root/subgoal:1:first'));
});

test('renaming an operation-local assumption preserves its scoped object identity',()=>{
 const scope=['h'],facts=new Map([['h','¬ ¬ P']]);
 const source='classical reductio hnot\n  contradiction\n    $False$ | h hnot';
 const renamed=source.replaceAll('hnot','notP');
 const original=compileNaturalDraft(source,scope,facts,{goal:'P'});
 const edited=compileNaturalDraft(renamed,scope,facts,{goal:'P'});
 assert.equal(original.complete,true,JSON.stringify(original.rows,null,2));
 assert.equal(edited.complete,true,JSON.stringify(edited.rows,null,2));
 const before=reconcileDraftIdentity(null,original.graph);
 const after=reconcileDraftIdentity(before,edited.graph);
 const oldOperation=original.graph.nodes.find(node=>node.kind==='classical-reductio');
 const newOperation=edited.graph.nodes.find(node=>node.kind==='classical-reductio');
 const oldBinding=original.rows[0].subgoals[0].graph.nodes.find(node=>node.kind==='context'&&node.name==='hnot');
 const newBinding=edited.rows[0].subgoals[0].graph.nodes.find(node=>node.kind==='context'&&node.name==='notP');
 assert.ok(oldOperation&&newOperation&&oldBinding&&newBinding);
 assert.equal(after.ids.get(newOperation.id),before.ids.get(oldOperation.id));
 assert.equal(after.ids.get(newBinding.id),before.ids.get(oldBinding.id));
});
test('subgoal-local assumption identities survive unrelated source-line shifts',()=>{
 const scope=['h'],facts=new Map([['h','¬ ¬ P']]);
 const source='classical reductio hnot\n  contradiction\n    $False$ | h hnot';
 const original=compileNaturalDraft(source,scope,facts,{goal:'P'});
 assert.equal(original.complete,true,JSON.stringify(original.rows,null,2));
 const old=reconcileDraftIdentity(null,original.graph);
 const oldBinding=original.rows[0].subgoals[0].graph.nodes.find(node=>node.kind==='context'&&node.name==='hnot');
 assert.ok(oldBinding);
 const shifted=compileNaturalDraft('\n'+source,scope,facts,{goal:'P'});
 const current=reconcileDraftIdentity(old,shifted.graph);
 const newBinding=shifted.rows[0].subgoals[0].graph.nodes.find(node=>node.kind==='context'&&node.name==='hnot');
 assert.ok(newBinding);
 assert.notEqual(newBinding.id,oldBinding.id,'the source path shifts with the block');
 assert.equal(current.ids.get(newBinding.id),old.ids.get(oldBinding.id),
  'the same scoped assumption retains identity after a harmless line insertion');
});


test('renaming a universal-introduction variable preserves its object and dependent uses',()=>{
 const scope=['hall'],facts=new Map([['hall','∀ x : Nat, P x']]);
 const make=name=>compileNaturalDraft(`take ${name} : $Nat$\n$P(${name})$ | hall ${name}`,scope,facts,
  {goal:`∀ ${name} : Nat, P ${name}`});
 const original=make('n'),renamed=make('k');
 assert.equal(original.complete,true,JSON.stringify(original.rows,null,2));
 assert.equal(renamed.complete,true,JSON.stringify(renamed.rows,null,2));
 const before=reconcileDraftIdentity(null,original.graph);
 const after=reconcileDraftIdentity(before,renamed.graph);
 assert.equal(after.ids.get('line:1'),before.ids.get('line:1'),
  'the explicit universal binder keeps identity when its display name changes');
 assert.equal(after.ids.get('line:2'),before.ids.get('line:2'),
  'a later use follows the introduced object identity, not the old spelling');
});


test('a selected proof candidate follows uniquely matched local objects through alpha-renaming',()=>{
 const scope=['hall','hall2'];
 const facts=new Map([['hall','∀ x : Nat, P x'],['hall2','∀ x : Nat, P x']]);
 const make=(name,choices=new Map())=>compileNaturalDraft(
  'take '+name+' : $Nat$\\n$P('+name+')$',scope,facts,
  {goal:'∀ '+name+' : Nat, P '+name,choices});
 const selected=new Map([[2,'hall n']]);
 const original=make('n',selected),renamed=make('k');
 assert.equal(original.complete,true,JSON.stringify(original.rows,null,2));
 const oldRow=original.graph.nodes.find(node=>node.id==='line:2');
 const newRow=renamed.graph.nodes.find(node=>node.id==='line:2');
 assert.ok(oldRow?.alternatives.some(candidate=>(candidate.choice??candidate.term)==='hall n'));
 assert.ok(newRow?.alternatives.some(candidate=>(candidate.choice??candidate.term)==='hall k'));
 const before=reconcileDraftIdentity(null,original.graph);
 const after=reconcileDraftIdentity(before,renamed.graph);
 assert.equal(after.ids.get('line:2'),before.ids.get('line:2'));
 assert.deepEqual([...migrateDraftChoices(before,after,selected)],[[2,'hall k']]);
});

test('alpha-renaming preserves a later use only when its cited premise identity is unchanged',()=>{
 const scope=['hall','hall2'],facts=new Map([['hall','∀ x : Nat, P x'],['hall2','∀ x : Nat, P x']]);
 const make=(name,premise='hall')=>compileNaturalDraft(`take ${name} : $Nat$\n$P(${name})$ | ${premise} ${name}`,scope,facts,
  {goal:`∀ ${name} : Nat, P ${name}`});
 const original=make('n'),renamed=make('k'),differentPremise=make('k','hall2');
 const before=reconcileDraftIdentity(null,original.graph);
 const alpha=reconcileDraftIdentity(before,renamed.graph);
 const changedRoute=reconcileDraftIdentity(before,differentPremise.graph);
 assert.equal(alpha.ids.get('line:1'),before.ids.get('line:1'));
 assert.equal(alpha.ids.get('line:2'),before.ids.get('line:2'));
 assert.notEqual(changedRoute.ids.get('line:2'),before.ids.get('line:2'),
  'a changed premise identity is not mistaken for alpha-renaming');
});
