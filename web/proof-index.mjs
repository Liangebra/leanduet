import {anchorFor} from './wording.mjs';
// One traversal, shared by the narrative, occurrence lookup and annotation matching.
export function indexProof(root){
 const paths=new Map(),anchors=new Map(),keys=new WeakMap(),counts=new WeakMap();
 let visits=0;
 function walk(node,depth=0){
  if(!node||depth>64)return 0;
  visits++;if(typeof node.path==='string')paths.set(node.path,node);
  const key=anchorFor(node);keys.set(node,key);
  if(anchors.has(key))anchors.set(key,null);else anchors.set(key,node);
  const size=1+(node.children||[]).reduce((n,c)=>n+walk(c,depth+1),0);counts.set(node,size);return size;
 }
 walk(root);
 return {paths,anchors,keys,counts,visits,
  find:path=>paths.get(path)||null,
  unique:anchor=>anchors.get(anchor)||null,
  wording(node,items){const key=keys.get(node);return anchors.get(key)===node?(items.get(key)||''):'';}
 };
}
