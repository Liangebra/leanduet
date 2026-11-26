import test from 'node:test';
import assert from 'node:assert/strict';
import {authoredNarrative} from '../web/narratives.mjs';
import {EXAMPLES,parseLean} from '../web/core.mjs';
test('authored examples cover each nonblank step',()=>{for(const e of EXAMPLES){const n=authoredNarrative(e.source);assert.ok(n);for(const step of parseLean(e.source).nodes.filter(x=>x.kind!=='blank'))assert.ok(n.steps[step.leanLine]);}});
test('narrative is never reused after source changes',()=>assert.equal(authoredNarrative(EXAMPLES[0].source.replace('hqr hq','hqr (hpq hp)')),null));
