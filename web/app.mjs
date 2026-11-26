import {parseLean,renderLean,renderProse,planSync,sameStatement,stepSentence,sentenceFragment,EXAMPLES} from './core.mjs';
import {replaceStep,snapshot,restore,lineRange} from './workspace.mjs';
import {authoredNarrative} from './narratives.mjs';
const $=id=>document.getElementById(id),lean=$('lean'),prose=$('prose'),notes=$('prompt');
const KEY='leanduet.workspace.v1',THEME='leanduet.theme';
let ir,base,rev=0,candidate=null,narrative=null,timer,selected=null,name='proof',exampleIndex=null,view='reading';
const clean=()=>lean.value===base.lean&&prose.value===base.prose;
const state=(id,label,kind='')=>{$(id).textContent=label;$(id).dataset.state=kind;};
function notice(s,error=false){$('notice').textContent=s;$('notice').classList.toggle('error',error);}
function persist(){try{localStorage.setItem(KEY,JSON.stringify(snapshot(base,{lean:lean.value,prose:prose.value},notes.value,name)));state('saveState','Saved locally','pass');}catch{state('saveState','Not saved','dirty');}}
function invalidate(){rev++;$('typedTree').replaceChildren();$('informathOutput').textContent='';$('typedStatus').textContent='Proof changed or not inspected. Run extraction for this revision.';candidate=null;narrative=null;$('accept').disabled=true;$('useNarrative').disabled=true;$('proposal').textContent='No proposal yet.';$('output').textContent='Run the local checker to see diagnostics for this revision.';state('verifyState','Not checked');if(location.hostname!=='127.0.0.1'&&location.hostname!=='localhost'){state('verifyState','Local server required');$('output').textContent='Browser-only demo. Run python server.py locally for verification.';}}
function dirty(){state('leanDirty',lean.value===base.lean?'Synced':'Edited',lean.value===base.lean?'':'dirty');state('proseDirty',prose.value===base.prose?'Synced':'Edited',prose.value===base.prose?'':'dirty');gutter();}
function gutter(){$('gutter').textContent=lean.value.split('\n').map((_,i)=>i+1).join('\n');$('gutter').scrollTop=lean.scrollTop;$('cursor').textContent='Ln '+(lean.value.slice(0,lean.selectionStart).split('\n').length);}
function element(tag,txt,cls){const e=document.createElement(tag);if(txt!==undefined)e.textContent=txt;if(cls)e.className=cls;return e;}
function formula(parent,source){
  // Conservative offline token rendering. Unknown syntax is kept as source.
  if(!source||!/^[\p{L}\p{N}\s_=:→∧∨¬↔∀∃()+*≤≥<>∘∈∉⊆∪∩-]+$/u.test(source)){parent.append(element('code',source));return;}
  const ns='http://www.w3.org/1998/Math/MathML',m=document.createElementNS(ns,'math');
  m.setAttribute('aria-label',source);
  for(const token of source.match(/\p{L}[\p{L}\p{N}_]*|\p{N}+|[^\s]/gu)||[]){
    const tag=/^\p{L}/u.test(token)?'mi':/^\p{N}/u.test(token)?'mn':'mo',child=document.createElementNS(ns,tag);
    child.textContent=token;m.append(child);
  }parent.append(m);
}
function appendNarrative(parent,parts){for(const part of parts){if(typeof part==='string')parent.append(document.createTextNode(part));else formula(parent,part.math);}}
function describe(n){
  const labels={intro:'Introduce',exact:'Conclude using',have:'Establish',apply:'Apply',rw:'Rewrite using',simp:'Simplify',show:'Show',refine:'Refine using',change:'Change the goal to',cases:'Split into cases on',induction:'Proceed by induction on',opaque:'Formal step'};
  return labels[n.kind]||n.label;
}
function setView(next){view=next;for(const key of ['reading','prose','typed','notes']){$(key+'View').hidden=key!==view;}document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view===view)));}
function selection(id,locate=false){
  if(!clean()){notice('Synchronize edits before navigating or editing a step.',true);return;}
  const n=ir.nodes.find(x=>x.id===id&&x.kind!=='blank');if(!n)return;
  selected=n.id;$('stepEditor').hidden=true;
  $('inspectName').textContent='Line '+n.leanLine+' · '+describe(n);$('inspectCode').textContent=n.lean;
  $('inspectParent').textContent=n.parent?'Nested under '+n.parent:'Top-level proof step';$('editStep').disabled=false;
  document.querySelectorAll('[data-node]').forEach(b=>{b.classList.toggle('selected',b.dataset.node===id);b.classList.toggle('active',b.dataset.node===id);});
  if(locate&&document.body.classList.contains('focus-reading'))return;
  if(locate){const [start,end]=lineRange(lean.value,n.leanLine);lean.focus();lean.setSelectionRange(start,end);lean.scrollTop=Math.max(0,(n.leanLine-3)*24);gutter();}
}
function resetStepInput(){
  const n=ir.nodes.find(x=>x.id===selected);if(!n)return;
  const guided=$('stepMode').value==='guided';
  $('stepInput').value=guided?stepSentence(n):n.lean;
  $('stepHelp').textContent=guided?'Try: Introduce hp · Establish hq : Q := hpq hp · Conclude using hqr hq. Use Lean step for opaque fragments.':'Edit one Lean source line. The theorem and surrounding lines are preserved.';
}
function startEdit(){if(!selected||!clean()){notice('Select a synchronized proof step first.',true);return;}const n=ir.nodes.find(x=>x.id===selected);setView('reading');$('stepLabel').textContent='Edit line '+n.leanLine+' · '+describe(n);$('stepMode').value='guided';resetStepInput();$('stepEditor').hidden=false;$('stepInput').focus();}
function reading(){
  const title=/^(?:theorem|lemma)\s+(\S+)/.exec(ir.header)?.[1]||'Proof';
  $('theoremName').textContent=title.replaceAll('_',' ');$('docname').textContent=name;$('codeFilename').textContent=title+'.lean';$('theoremMeta').textContent=ir.nodes.filter(n=>n.kind!=='blank').length+' proof steps · '+(ir.prelude.filter(x=>x.startsWith('import ')).length)+' imports';
  const h=$('statement');h.replaceChildren();const statement=ir.header.replace(/^(?:theorem|lemma)\s+\S+\s*/,'').replace(/\s*:= by$/,'');const authored=authoredNarrative(renderLean(ir));if(authored)appendNarrative(h,authored.statement);else formula(h,statement);$('narrativeStatus').textContent=authored?'Authored example · alignment not formally certified':'Structural view · not a mathematical narrative';
  const box=$('reading'),outline=$('outline');box.replaceChildren();outline.replaceChildren();$('stepCount').textContent=ir.nodes.filter(n=>n.kind!=='blank').length;
  for(const n of ir.nodes){if(n.kind==='blank')continue;const b=element('button',undefined,'step');b.dataset.node=n.id;b.style.marginLeft=Math.min(n.indent-2,8)*5+'px';b.style.width='calc(100% - '+Math.min(n.indent-2,8)*5+'px)';b.append(element('span',String(n.leanLine),'line'));const content=element('span',undefined,'steptext');if(authored?.steps[n.leanLine])appendNarrative(content,authored.steps[n.leanLine]);else{content.append(document.createTextNode(describe(n)+(n.argument===null?'':' ')));if(n.argument!==null)formula(content,n.argument);}b.append(content);b.onclick=()=>selection(n.id,true);b.ondblclick=()=>{selection(n.id);startEdit();};box.append(b);
    const item=element('button',n.leanLine+'  '+n.lean,'outlineItem');item.dataset.node=n.id;item.style.paddingLeft=(10+Math.min(n.indent-2,8)*4)+'px';item.onclick=()=>{setView('reading');selection(n.id,true);};outline.append(item);}
  selected=null;$('stepEditor').hidden=true;$('editStep').disabled=true;$('inspectName').textContent='No step selected';$('inspectCode').textContent='';$('inspectParent').textContent='—';
}
function install(next,{save=true}={}){clearTimeout(timer);ir=next;const l=renderLean(ir),p=renderProse(ir);if(lean.value!==l)lean.value=l;if(prose.value!==p)prose.value=p;base={lean:l,prose:p};invalidate();dirty();reading();notice('Representations synchronized. Lean verification and narrative review are separate.');if(save)persist();}
function sync(side){clearTimeout(timer);try{install(planSync(base,lean.value,prose.value,side).ir);}catch(e){notice(e.message,true);persist();}}
for(const [el,side] of [[lean,'lean'],[prose,'prose']])el.addEventListener('input',()=>{clearTimeout(timer);invalidate();$('stepEditor').hidden=true;$('editStep').disabled=true;dirty();notice('Unsynchronized edits · both drafts are retained.');persist();if($('auto').checked)timer=setTimeout(()=>sync(side),450);});
notes.addEventListener('input',()=>{rev++;candidate=null;narrative=null;$('accept').disabled=true;$('useNarrative').disabled=true;$('proposal').textContent='Notes changed. Request a new proposal.';persist();});
for(const evt of ['click','keyup','scroll','select'])lean.addEventListener(evt,gutter);
function cursorLink(){
  if(!clean()||document.activeElement!==lean)return;
  const line=lean.value.slice(0,lean.selectionStart).split('\n').length;
  const node=ir.nodes.find(n=>n.leanLine===line&&n.kind!=='blank');
  if(node&&node.id!==selected)selection(node.id,false);
}
for(const evt of ['click','keyup'])lean.addEventListener(evt,cursorLink);
$('focusMode').onclick=()=>{const active=$('focusMode').getAttribute('aria-pressed')!=='true';$('focusMode').setAttribute('aria-pressed',String(active));$('focusMode').textContent=active?'Show Lean':'Focus reading';document.body.classList.toggle('focus-reading',active);setView('reading');};
$('newDoc').onclick=()=>{if(!mayReplace())return;name='Untitled proof';notes.value='';install(parseLean('theorem my_theorem : True := by\n  sorry\n'));setView('reading');lean.focus();};
$('stepInput').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();$('applyStep').click();}if(e.key==='Escape')$('cancelStep').click();});
$('fromLean').onclick=()=>sync('lean');$('fromProse').onclick=()=>sync('prose');
document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>setView(b.dataset.view));
$('editStep').onclick=startEdit;$('cancelStep').onclick=()=>{$('stepEditor').hidden=true;};
$('stepMode').onchange=resetStepInput;
$('applyStep').onclick=()=>{if(!clean()){notice('Synchronize changes first.',true);return;}try{const fragment=$('stepMode').value==='guided'?sentenceFragment($('stepInput').value):$('stepInput').value;const id=selected;install(replaceStep(lean.value,id,fragment));selection(id);}catch(e){notice(e.message,true);}};
for(const [id,el,key] of [['revertLean',lean,'lean'],['revertProse',prose,'prose']])$(id).onclick=()=>{clearTimeout(timer);if(el.value!==base[key]&&!confirm('Discard unsynchronized changes on this side?'))return;el.value=base[key];invalidate();dirty();persist();notice('Reverted this side.');};
$('adopt').onclick=()=>{try{const next=parseLean(lean.value);if(!confirm('Adopt this Lean source as a new baseline? This replaces the controlled-text draft. Export your workspace first if needed.'))return;install(next);}catch(e){notice(e.message,true);}};
function mayReplace(){return (clean()&&!notes.value&&authoredNarrative(base.lean)!==null)||confirm('Replace current workspace? Export it first to preserve both drafts and notes.');}
EXAMPLES.forEach((e,i)=>{const b=element('button',e.name,'example');b.onclick=()=>{if(!mayReplace())return;name=e.name;notes.value='';exampleIndex=i;install(parseLean(e.source));document.querySelectorAll('.example').forEach((x,j)=>x.classList.toggle('active',j===i));};$('examples').append(b);});
function loadWorkspace(data){const r=restore(data);name=r.name;notes.value=r.notes;install(r.ir,{save:false});lean.value=r.drafts.lean;prose.value=r.drafts.prose;dirty();if(!clean())notice('Restored unsynchronized drafts. Synchronize from the edited side.');persist();}
$('open').onclick=()=>$('file').click();
$('file').onchange=async()=>{try{const f=$('file').files[0];if(!f||!mayReplace())return;if(f.size>1024*1024)throw Error('File exceeds 1 MiB.');const s=await f.text();if(f.name.endsWith('.json'))loadWorkspace(JSON.parse(s));else{const next=parseLean(s.replace(/\r\n/g,'\n'));name=f.name;notes.value='';install(next);}}catch(e){notice(e.message,true);}finally{$('file').value='';}};
function download(content,filename,type){const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([content],{type}));a.download=filename;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);}
$('download').onclick=()=>download(lean.value,'proof.lean','text/plain');
$('saveDoc').onclick=()=>download(JSON.stringify(snapshot(base,{lean:lean.value,prose:prose.value},notes.value,name),null,2),'proof.leanduet.json','application/json');
async function api(path,payload){const r=await fetch('/api/'+path,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});if(!r.headers.get('content-type')?.includes('application/json'))throw Error('Local backend not available. Start python server.py.');const d=await r.json();if(!r.ok)throw Error(d.error||'Request failed');return d;}
$('check').onclick=async()=>{if(!clean()){notice('Synchronize first.',true);return;}const snapshotRev=rev;$('check').disabled=true;state('verifyState','Checking…');$('output').textContent='Running Lean…';try{const r=await api('check',{source:lean.value});if(snapshotRev!==rev)return;$('output').textContent=r.output;state('verifyState',r.status==='passed'?'Lean passed':r.status,r.status==='passed'?'pass':'dirty');notice('Lean check: '+r.status,r.status!=='passed');}catch(e){if(snapshotRev===rev){state('verifyState','Unavailable','dirty');$('output').textContent=e.message;notice('Checker unavailable: '+e.message,true);}}finally{$('check').disabled=false;}};
function renderTyped(node,container,depth=0){
  if(!node||typeof node.kind!=='string'||depth>12)return;
  const block=element('details',undefined,'typedNode');block.open=depth<3;
  const title=element('summary');
  const label={assume:'Assume',introduce:'Introduce',apply:'Apply',let:'Establish local binding',hypothesis:'Use hypothesis',reference:'Use declaration',opaque:'Opaque term'}[node.kind]||node.kind;
  title.append(element('strong',label+(node.binder?' '+node.binder:node.reference?' '+node.reference:'')));
  block.append(title);
  const typ=element('div',undefined,'typedType');typ.append(element('span','Type / conclusion','eyebrow'));typ.append(element('code',node.type||''));block.append(typ);
  if(node.binderType)block.append(element('code','Binder: '+node.binderType));
  if(node.referenceType)block.append(element('code','Reference type: '+node.referenceType));
  const term=element('details');term.append(element('summary','Elaborated term'));term.append(element('pre',node.term||''));block.append(term);
  for(const child of node.children||[])renderTyped(child,block,depth+1);
  container.append(block);
}
async function typedRequest(mode){
  if(!clean()){notice('Synchronize first.',true);return;}
  const snapshotRev=rev;
  $('extractTerm').disabled=$('informath').disabled=true;
  $('typedStatus').textContent=mode==='structure'?'Elaborating trusted proof locally…':'Running separately installed Informath…';
  try{const r=await api(mode,{source:lean.value});if(snapshotRev!==rev)return;
    if(mode==='structure'){$('typedTree').replaceChildren();renderTyped(r.tree,$('typedTree'));$('typedStatus').textContent='Extracted from Lean elaboration. Tree is depth-limited; inspect the original proof separately.';}
    else{$('informathOutput').textContent=r.narrative;$('typedStatus').textContent='Informath output · alignment not certified.';}
  }catch(e){if(snapshotRev===rev)$('typedStatus').textContent=e.message;}
  finally{$('extractTerm').disabled=$('informath').disabled=false;}
}
$('extractTerm').onclick=()=>typedRequest('structure');$('informath').onclick=()=>typedRequest('informath');
async function ai(mode){if(!clean()){notice('Synchronize first.',true);return;}if(mode==='propose'&&!notes.value.trim()){notice('Enter a mathematical argument first.',true);return;}if(!confirm('Send the current Lean proof and notes to your configured AI provider?'))return;const snapshotRev=rev;candidate=null;narrative=null;$('accept').disabled=$('useNarrative').disabled=true;$('propose').disabled=$('explain').disabled=true;$('proposal').textContent='Requesting unverified output…';try{const r=await api(mode,{source:lean.value,prose:notes.value});if(snapshotRev!==rev)return;if(mode==='explain'){narrative=r.narrative;$('proposal').textContent=narrative;$('useNarrative').disabled=false;notice('AI explanation · unverified.');return;}const next=parseLean(r.source);if(!sameStatement(ir,next))throw Error('Theorem header or environment changed.');candidate=next;$('proposal').textContent=r.source;$('accept').disabled=false;notice('Unverified proposal · review before applying and checking.');}catch(e){if(snapshotRev===rev){$('proposal').textContent=e.message;notice('AI unavailable or rejected.',true);}}finally{$('propose').disabled=$('explain').disabled=false;}}
$('propose').onclick=()=>ai('propose');$('explain').onclick=()=>ai('explain');$('accept').onclick=()=>{if(candidate&&clean()&&confirm('Apply the proposed Lean source? Review before running Lean.'))install(candidate);};
$('useNarrative').onclick=()=>{if(narrative&&(!notes.value||confirm('Replace your free-prose notes with this unverified explanation?'))){notes.value=narrative;persist();}};
function theme(t){document.documentElement.dataset.theme=t;$('theme').textContent=t==='dark'?'Light mode':'Dark mode';try{localStorage.setItem(THEME,t);}catch{}}
$('theme').onclick=()=>theme(document.documentElement.dataset.theme==='dark'?'light':'dark');
try{theme(localStorage.getItem(THEME)||'light');}catch{theme('light');}
try{const saved=localStorage.getItem(KEY);if(saved)loadWorkspace(JSON.parse(saved));else{name=EXAMPLES[0].name;install(parseLean(EXAMPLES[0].source));}}catch(e){name=EXAMPLES[0].name;install(parseLean(EXAMPLES[0].source),{save:false});notice('Saved workspace could not be restored: '+e.message+'. Original storage retained until the next edit.',true);}
const local=location.hostname==='127.0.0.1'||location.hostname==='localhost';
$('envState').textContent=local?'Local workspace':'Static demo · checker and AI require local server';
if(!local){for(const id of ['check','propose','explain','extractTerm','informath']){$(id).disabled=true;$(id).title='Start the local Python server to use this feature.';}$('output').textContent='Browser-only demo. To verify in Lean or use AI, clone the repository and run python server.py.';state('verifyState','Local server required');}
document.addEventListener('keydown',e=>{if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='s'){e.preventDefault();persist();notice('Workspace saved locally. Export for a portable backup.');}});
