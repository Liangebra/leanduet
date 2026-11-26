// Wording is an author's annotation, not a formal inference.
// Only exact, unique structural fingerprints permit automatic reattachment.
export function anchorFor(node){
  if(!node)return null;
  return JSON.stringify([node.kind,node.reference||'',node.term||'',node.type||'',(node.scope||[]).map(d=>[d.name,d.type,d.contextIndex])]);
}
export function validateWording(value){
  if(value===undefined)return [];
  if(!Array.isArray(value)||value.length>50)throw Error('Invalid wording collection.');
  return value.map(a=>{
    if(!a||typeof a.anchor!=='string'||a.anchor.length>16000||typeof a.text!=='string'||a.text.length>2000||typeof a.path!=='string'||a.path.length>256)throw Error('Invalid wording annotation.');
    return {anchor:a.anchor,path:a.path,text:a.text};
  });
}
export function uniqueMatch(root,anchor){
  const hits=[];
  function walk(n){if(!n)return;if(anchorFor(n)===anchor)hits.push(n);for(const c of n.children||[])walk(c);}
  walk(root);
  return hits.length===1?hits[0]:null;
}
export function wordingFor(root,node,items){
  const key=anchorFor(node);
  if(!key||uniqueMatch(root,key)!==node)return '';
  return items.find(a=>a.anchor===key)?.text||'';
}
export function putWording(items,root,node,text){
  const anchor=anchorFor(node);
  if(!anchor||uniqueMatch(root,anchor)!==node)throw Error('This occurrence is ambiguous. Keep the wording in exploration instead.');
  const rest=items.filter(a=>a.anchor!==anchor);
  return validateWording(text?[...rest,{anchor,path:node.path,text}]:rest);
}
