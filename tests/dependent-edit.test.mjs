import test from 'node:test';
import assert from 'node:assert/strict';
import {witnessTerm} from '../web/dependent-edit.mjs';
test('dependent witness edits include both witness and evidence',()=>assert.equal(witnessTerm('1','rfl'),'Exists.intro (1) (rfl)'));
test('incomplete dependent edits are rejected',()=>{assert.throws(()=>witnessTerm('1',''));assert.throws(()=>witnessTerm('','rfl'));});
