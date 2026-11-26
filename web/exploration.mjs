// Open research objects are not Lean declarations. No parsing, name uniqueness,
// acyclicity, type correctness or proof validity is imposed on their contents.
const STATES=['idea','working','doubtful','discarded'];
const str=(v,max)=>typeof v==='string'&&v.length<=max;
export function emptyExploration(){return {schema:1,next:1,items:[]};}
export function validateExploration(value){
  if(value===undefined)return emptyExploration();
  if(!value||value.schema!==1||!Number.isSafeInteger(value.next)||value.next<1||
      !Array.isArray(value.items)||value.items.length>100)throw Error('Invalid exploration collection.');
  const ids=new Set();
  for(const item of value.items){
    if(!item||!Number.isSafeInteger(item.id)||item.id<1||item.id>=value.next||ids.has(item.id)||
      !str(item.label,256)||!str(item.expression,12000)||!str(item.comment,12000)||
      !str(item.links,1000)||!STATES.includes(item.state))throw Error('Invalid exploration object.');
    ids.add(item.id);
  }
  // Only transport shape and resource bounds are checked. Even unknown
  // references and contradictory expressions are legitimate research data.
  return {schema:1,next:value.next,items:value.items.map(({id,label,expression,comment,links,state})=>({id,label,expression,comment,links,state}))};
}
export function addObject(collection,initial={}){
  const c=validateExploration(collection);
  if(c.items.length>=100||c.next>=Number.MAX_SAFE_INTEGER)throw Error('Exploration object limit reached.');
  return validateExploration({...c,next:c.next+1,items:[...c.items,{id:c.next,label:initial.label??'',expression:initial.expression??'',comment:initial.comment??'',links:initial.links??'',state:initial.state??'idea'}]});
}
export function updateObject(collection,id,changes){
  const c=validateExploration(collection);
  if(!c.items.some(x=>x.id===id))throw Error('Unknown exploration object.');
  return validateExploration({...c,items:c.items.map(x=>x.id===id?{...x,...changes,id}:x)});
}
export function referencedObjects(collection,item){
  const ids=new Set(collection.items.map(x=>x.id));
  const refs=[...new Set([...item.links.matchAll(/#([1-9]\d*)/g)].map(m=>Number(m[1])).filter(Number.isSafeInteger))];
  return refs.map(id=>({id,present:ids.has(id)}));
}
export function explorationMarkdown(collection){
  const c=validateExploration(collection);
  return c.items.map(x=>'### #'+x.id+' '+(x.label||'(untitled)')+' — '+x.state+' (unverified)\n\n'+x.expression+'\n\n'+x.comment+(x.links?'\n\nRelated: '+x.links:'')).join('\n\n');
}
