import test from 'node:test';
import assert from 'node:assert/strict';
import {tokenize} from '../web/editor.mjs';
test('lexical highlighting preserves source exactly including Unicode and nested comments',()=>{
 const source='theorem t : True := by\n  /- outer /- inner -/ -/ exact True.intro -- end\n  "a\\"b"\n';
 const tokens=tokenize(source);assert.equal(tokens.map(t=>t.text).join(''),source);
 assert(tokens.some(t=>t.kind==='comment'&&t.text.includes('inner')));
 assert(tokens.some(t=>t.kind==='keyword'&&t.text==='theorem'));
});
