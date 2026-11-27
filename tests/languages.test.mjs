import test from 'node:test';
import assert from 'node:assert/strict';
import {registerPack,languagePack,validatePack} from '../web/languages.mjs';
import {parseRuleIntent} from '../web/rule-intent.mjs';
import {compileChain} from '../web/proof-chain.mjs';
import {narrate} from '../web/typed-narrative.mjs';
import fs from 'node:fs';

const p=JSON.parse(fs.readFileSync(new URL('../examples/language-fr.json',import.meta.url),'utf8'));
const ur=JSON.parse(fs.readFileSync(new URL('../examples/language-ur.json',import.meta.url),'utf8'));

test('external language data drives parsing and rendering without changing the proof core',()=>{
  registerPack(p);
  assert.equal(languagePack('fr').label,'Français');
  assert.equal(parseRuleIntent('par symétrie de l’égalité avec h').rule,'Eq.symm');
  assert.equal(compileChain('Établir q | f avec p\nConclure | g avec q',['f','g','p']).term,'by\n  have q := f p\n  exact g q');
  assert.match(narrate({kind:'apply',reference:'Eq.symm',type:'P',children:[]},'fr')[0].phrase,/symétrie/);
});

test('Urdu pack resolves exact Lean aliases and renders localized rule phrases',()=>{
  registerPack(ur);
  assert.equal(languagePack('ur').label,'اردو');
  assert.equal(Object.keys(ur.aliases).length,5);

  for(const [declaration,aliases] of Object.entries(ur.aliases)){
    assert.ok(aliases.length>0,`Expected at least one alias for ${declaration}`);
    for(const alias of aliases){
      assert.equal(parseRuleIntent(alias).rule,declaration,`Alias should resolve to ${declaration}: ${alias}`);
    }
  }

  assert.deepEqual(
    parseRuleIntent(`بذریعہ ${ur.aliases['Eq.symm'][0]} کے ساتھ h`),
    {rule:'Eq.symm',required:['h']}
  );

  assert.equal(
    compileChain(
      'متعارف کروائیں q | f کے ساتھ p\nنتیجہ اخذ کریں | g کے ساتھ q',
      ['f','g','p']
    ).term,
    'by\n  have q := f p\n  exact g q'
  );

  const [row]=narrate(
    {kind:'apply',reference:'Eq.symm',type:'P',children:[]},
    'ur'
  );
  assert.ok(row.phrase.startsWith(ur.rules['Eq.symm']));
});

test('malformed packs and built-in replacement are rejected',()=>{
  assert.throws(()=>validatePack({...p,words:{}}));
  assert.throws(()=>registerPack({...p,id:'en'}));
  assert.throws(()=>validatePack({...p,grammar:{...p.grammar,using:[{}]}}));
});
