import test from 'node:test';
import assert from 'node:assert/strict';
import {emptyExploration,addObject,updateObject,validateExploration,referencedObjects,explorationMarkdown} from '../web/exploration.mjs';
test('unfinished and conflicting objects coexist with stable identities',()=>{
 let c=addObject(emptyExploration(),{label:'x',expression:'x / 0 = ?',links:'#2 #99'});
 c=addObject(c,{label:'x',expression:'x ≠ x',links:'#1',state:'doubtful'});
 assert.equal(c.items.length,2);
 assert.deepEqual(referencedObjects(c,c.items[0]),[{id:2,present:true},{id:99,present:false}]);
 c=updateObject(c,1,{state:'discarded'});
 assert.equal(c.items[0].expression,'x / 0 = ?');
 assert.equal(c.items[1].links,'#1');
 assert.deepEqual(validateExploration(JSON.parse(JSON.stringify(c))),c);
 assert.match(explorationMarkdown(c),/discarded \(unverified\)/);
});
test('shape bounds are not mathematical restrictions',()=>{
 assert.deepEqual(validateExploration(undefined),emptyExploration());
 const c=addObject(emptyExploration());
 assert.equal(c.items[0].expression,'');
 assert.throws(()=>updateObject(c,1,{state:'verified'}));
 assert.throws(()=>validateExploration({...c,items:[c.items[0],c.items[0]]}));
});
