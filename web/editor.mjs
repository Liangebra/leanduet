// Layout preferences and lexical source presentation; the textarea remains
// the editable, accessible source of truth. This is not Lean's semantic lexer.
const words=new Set('theorem lemma def abbrev example import namespace end section variable universe open set_option by intro intros exact apply have let show from fun forall match with if then else do cases rcases constructor refine rw simp simpa rfl trivial assumption induction calc sorry admit first all_goals obtain'.split(' '));
export function tokenize(source){
  const out=[];let i=0;
  while(i<source.length){
    const start=i;let kind='';
    if(source.startsWith('--',i)){i=source.indexOf('\n',i);if(i<0)i=source.length;kind='comment';}
    else if(source.startsWith('/-',i)){i+=2;let depth=1;while(i<source.length&&depth){if(source.startsWith('/-',i)){depth++;i+=2;}else if(source.startsWith('-/',i)){depth--;i+=2;}else i++;}kind='comment';}
    else if(source[i]==='"'){i++;while(i<source.length){if(source[i]==='\\'){i=Math.min(i+2,source.length);continue;}if(source[i++]==='"')break;}kind='string';}
    else {const m=/^[\p{L}_][\p{L}\p{N}_']*/u.exec(source.slice(i));const n=/^\d+(?:\.\d+)?/.exec(source.slice(i));if(m){i+=m[0].length;kind=words.has(m[0])?'keyword':'';}else if(n){i+=n[0].length;kind='number';}else{i+=1;if('∀∃→↔∧∨¬:=λ'.includes(source[start]))kind='symbol';}}
    out.push({text:source.slice(start,i),kind});
  }return out;
}
export function mountEditor(){
  const lean=document.getElementById('lean'),highlight=document.getElementById('highlight'),splitter=document.getElementById('splitter'),panes=document.querySelector('.panes');
  let rendered=null;
  function refresh(){
    if(rendered!==lean.value){rendered=lean.value;const fragment=document.createDocumentFragment();for(const t of tokenize(rendered)){if(t.kind){const span=document.createElement('span');span.className='tok-'+t.kind;span.textContent=t.text;fragment.append(span);}else fragment.append(document.createTextNode(t.text));}fragment.append(document.createTextNode('\n'));highlight.replaceChildren(fragment);}
    // Match the editable viewport including native scrollbar geometry.
    highlight.style.width=lean.clientWidth+'px';highlight.style.height=lean.clientHeight+'px';highlight.scrollTop=lean.scrollTop;highlight.scrollLeft=lean.scrollLeft;
  }
  const storage=(key,value)=>{try{if(value===undefined)return localStorage.getItem(key);localStorage.setItem(key,value);}catch{return null;}};
  let split=50;
  function size(value){split=Math.max(25,Math.min(75,Number(value)||50));document.documentElement.style.setProperty('--split',split+'%');splitter.setAttribute('aria-valuenow',String(Math.round(split)));storage('leanduet.split',String(split));refresh();}
  size(storage('leanduet.split')||50);
  splitter.addEventListener('pointerdown',e=>{if(e.button!==0)return;splitter.setPointerCapture(e.pointerId);splitter.classList.add('dragging');e.preventDefault();});
  splitter.addEventListener('pointermove',e=>{if(!splitter.hasPointerCapture(e.pointerId))return;const r=panes.getBoundingClientRect();size(100*(e.clientX-r.left)/r.width);});
  for(const evt of ['pointerup','pointercancel','lostpointercapture'])splitter.addEventListener(evt,()=>splitter.classList.remove('dragging'));
  splitter.addEventListener('keydown',e=>{if(['ArrowLeft','ArrowRight','Home','End'].includes(e.key)){e.preventDefault();size(e.key==='Home'?25:e.key==='End'?75:split+(e.key==='ArrowRight'?5:-5));}});
  const layout=document.getElementById('toggleLayout'),explorer=document.getElementById('toggleExplorer');
  function setLayout(notebook){document.body.classList.toggle('notebook-layout',notebook);layout.setAttribute('aria-pressed',String(notebook));layout.textContent=notebook?'Split view':'Notebook';storage('leanduet.layout',notebook?'notebook':'split');refresh();}
  function setExplorer(visible){document.body.classList.toggle('explorer-hidden',!visible);explorer.setAttribute('aria-pressed',String(visible));storage('leanduet.explorer',visible?'show':'hide');refresh();}
  layout.onclick=()=>setLayout(!document.body.classList.contains('notebook-layout'));explorer.onclick=()=>setExplorer(document.body.classList.contains('explorer-hidden'));
  setLayout(storage('leanduet.layout')==='notebook');setExplorer(storage('leanduet.explorer')!=='hide');
  lean.addEventListener('input',refresh);lean.addEventListener('scroll',refresh);
  if(typeof ResizeObserver!=='undefined')new ResizeObserver(refresh).observe(lean);
  refresh();return refresh;
}
