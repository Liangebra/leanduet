// LSP uses UTF-16 positions, as do JavaScript string offsets.
export function positionAt(source,offset){
 const prior=source.slice(0,offset).split('\n');return {line:prior.length-1,character:prior.at(-1).length};
}
export function offsetAt(source,p){
 if(!Number.isInteger(p?.line)||!Number.isInteger(p?.character)||p.line<0||p.character<0)throw Error('Invalid completion range.');
 const lines=source.split('\n');if(p.line>=lines.length||p.character>lines[p.line].length)throw Error('Completion range outside source.');
 return lines.slice(0,p.line).reduce((a,l)=>a+l.length+1,0)+p.character;
}
export function completionEdit(source,cursor,item){
 if(item.insertTextFormat===2||item.additionalTextEdits?.length||item.command)throw Error('Complex completion edits are not supported yet.');
 const e=item.textEdit;
 if(e){
  const range=e.replace||e.range||e.insert;
  const start=offsetAt(source,range?.start),end=offsetAt(source,range?.end);
  if(start>cursor||end<cursor||start>end||typeof e.newText!=='string')throw Error('Invalid completion edit.');
  return {start,end,text:e.newText};
 }
 const prefix=/[\p{L}\p{N}_'.]*$/u.exec(source.slice(0,cursor))[0];
 return {start:cursor-prefix.length,end:cursor,text:item.insertText||item.label};
}
