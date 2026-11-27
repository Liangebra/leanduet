import test from 'node:test';
import assert from 'node:assert/strict';
import {translate} from '../web/interface-language.mjs';

test('semantic resolution labels are available in all built-in interface languages',()=>{
 assert.equal(translate('Candidate generated · Lean not checked','zh'),'已生成候选 · 尚未交由 Lean 检查');
 assert.equal(translate('Multiple supported interpretations remain','ja'),'複数の対応可能な解釈が残っています');
 assert.equal(translate('No match in the supported rule set','en'),'No match in the supported rule set');
});
