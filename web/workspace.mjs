import {parseLean,renderProse,sameStatement} from './core.mjs';
function replaceStep(source,id,fragment){
  const ir=parseLean(source),node=ir.nodes.find(n=>n.id===id&&n.kind!=="blank");
  if(!node)throw Error("Select an existing proof step.");
  if(typeof fragment!=="string"||!fragment.trim()||fragment!==fragment.trimStart()||/[\r\n]/.test(fragment))throw Error("Enter a single Lean fragment without leading indentation.");
  const lines=source.split("\n");
  lines[node.leanLine-1]=" ".repeat(node.indent)+fragment;
  const next=parseLean(lines.join("\n"));
  if(!sameStatement(ir,next))throw Error("The statement changed.");
  return next;
}

function snapshot(base,drafts,notes,name){
  return {format:"leanduet-workspace",version:1,name,base:{lean:base.lean,prose:base.prose},drafts:{lean:drafts.lean,prose:drafts.prose},notes};
}

function restore(data){
  if(!data||data.format!=="leanduet-workspace"||data.version!==1)throw Error("Unsupported workspace format.");
  for(const v of [data.name,data.base?.lean,data.base?.prose,data.drafts?.lean,data.drafts?.prose,data.notes])if(typeof v!=="string"||v.length>131072)throw Error("Invalid or oversized workspace field.");
  const ir=parseLean(data.base.lean);
  if(renderProse(ir)!==data.base.prose)throw Error("Workspace base representations do not match.");
  return {...data,ir};
}

function lineRange(source,line){
  const lines=source.split("\n");
  if(!Number.isInteger(line)||line<1||line>lines.length)throw Error("Invalid line.");
  const start=lines.slice(0,line-1).reduce((n,s)=>n+s.length+1,0);
  return [start,start+lines[line-1].length];
}
export {replaceStep,snapshot,restore,lineRange};
