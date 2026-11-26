import test from 'node:test';
import assert from 'node:assert/strict';
import {positionAt,offsetAt,completionEdit} from '../web/completion.mjs';
test('positions use UTF-16, not Unicode code points',()=>{
 const s='a\n𝕏 Nat.su';assert.deepEqual(positionAt(s,s.length),{line:1,character:9});assert.equal(offsetAt(s,{line:1,character:9}),s.length);
});
test('Lean LSP replacement ranges are honored',()=>{
 const s='exact Nat.su';const cursor=s.length;
 assert.deepEqual(completionEdit(s,cursor,{label:'succ',textEdit:{newText:'Nat.succ',range:{start:{line:0,character:6},end:{line:0,character:12}}}}),{start:6,end:12,text:'Nat.succ'});
 assert.throws(()=>completionEdit(s,cursor,{label:'x',insertTextFormat:2}));
});
