import test from 'node:test';
import assert from 'node:assert/strict';
import {parseLean,renderLean,parseProse,renderProse,planSync,EXAMPLES} from '../web/core.mjs';
for(const e of EXAMPLES) {
  test('exact Lean round trip: '+e.name,()=>assert.equal(renderLean(parseLean(e.source)),e.source));
  test('exact prose round trip: '+e.name,()=>assert.equal(renderLean(parseProse(renderProse(parseLean(e.source)))),e.source));
}
test('nested lexical parent',()=>{const ir=parseLean(EXAMPLES[2].source);assert.equal(ir.nodes[1].parent,ir.nodes[0].id)});
test('prose edit changes Lean',()=>{const lean=EXAMPLES[0].source,prose=renderProse(parseLean(lean));assert.match(planSync({lean,prose},lean,prose.replace('hqr hq','hqr (hpq hp)'),'prose').lean,/exact hqr \(hpq hp\)/)});
test('conflicting edits rejected',()=>{const lean=EXAMPLES[0].source,prose=renderProse(parseLean(lean));assert.throws(()=>planSync({lean,prose},lean+'  rfl\n',prose+'changed','lean'),/Both sides/)});
test('changed theorem rejected',()=>{const lean=EXAMPLES[0].source,prose=renderProse(parseLean(lean));assert.throws(()=>planSync({lean,prose},lean.replace('P → R := by','P → P := by'),prose,'lean'),/Statement/)});
test('blank lines and missing final newline preserved',()=>{const s='theorem t : True := by\n\n  trivial';assert.equal(renderLean(parseProse(renderProse(parseLean(s)))),s)});
test('multiple declarations rejected',()=>assert.throws(()=>parseLean(EXAMPLES[0].source+'theorem t : True := by\n  trivial\n')));
test('block comments rejected',()=>assert.throws(()=>parseLean('theorem t : True := by\n  /- test -/\n  trivial\n')));
