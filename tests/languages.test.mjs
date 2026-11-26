import test from 'node:test';
import assert from 'node:assert/strict';
import {registerPack,languagePack,validatePack} from '../web/languages.mjs';
import {parseRuleIntent} from '../web/rule-intent.mjs';
import {compileChain} from '../web/proof-chain.mjs';
import {narrate} from '../web/typed-narrative.mjs';
import fs from 'node:fs';
const p=JSON.parse(fs.readFileSync(new URL('../examples/language-fr.json',import.meta.url),'utf8'));
test('external language data drives parsing and rendering without changing the proof core',()=>{
 registerPack(p);
 assert.equal(languagePack('fr').label,'Français');
 assert.equal(parseRuleIntent('par symétrie de l’égalité avec h').rule,'Eq.symm');
 assert.equal(compileChain('Établir q | f avec p\nConclure | g avec q',['f','g','p']).term,'by\n  have q := f p\n  exact g q');
 assert.match(narrate({kind:'apply',reference:'Eq.symm',type:'P',children:[]},'fr')[0].phrase,/symétrie/);
});
test('malformed packs and built-in replacement are rejected',()=>{
 assert.throws(()=>validatePack({...p,words:{}}));
 assert.throws(()=>registerPack({...p,id:'en'}));
 assert.throws(()=>validatePack({...p,grammar:{...p.grammar,using:[{}]}}));
});
