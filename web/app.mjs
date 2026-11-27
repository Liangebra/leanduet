import {parseLean,renderLean,renderProse,planSync,sameStatement,stepSentence,sentenceFragment,EXAMPLES} from './core.mjs';
import {replaceStep,snapshot,restore,lineRange} from './workspace.mjs';
import {emptyExploration,addObject,updateObject,referencedObjects,explorationMarkdown} from './exploration.mjs';
import {authoredNarrative} from './narratives.mjs';
import {narrate,outlinePaths} from './typed-narrative.mjs';
import {witnessTerm} from './dependent-edit.mjs';
import {conceptLabels,parseRuleIntent} from './rule-intent.mjs';
import {validateJudgment} from './semantic-ir.mjs';
import {compileFormula} from './math-formula.mjs';
import {compileChain,compileFormulaSequence} from './proof-chain.mjs';
import {createDraftSession} from './natural-draft.mjs';
import {reconcileDraftIdentity,migrateDraftChoices} from './draft-identity.mjs';
import {factsFromScope} from './context-grammar.mjs';
import {languagePacks,registerPack,customPacks,phrase} from './languages.mjs';
import {positionAt,completionEdit} from './completion.mjs';
import {interpretations,rankInterpretations,mergeInterpretations} from './interpretations.mjs';
import {wordingFor,putWording,reattachWording} from './wording.mjs';
import {indexProof} from './proof-index.mjs';
import {mountEditor} from './editor.mjs';
import {mountInterface} from './interface-language.mjs';
const $=id=>document.getElementById(id),lean=$('lean'),prose=$('prose'),notes=$('prompt');
const local=(location.hostname==='127.0.0.1'||location.hostname==='localhost')&&!new URLSearchParams(location.search).has('demo');
const staticProofs=new Map();let staticToolchain='';
const ui=mountInterface(()=>{if(!local)showStaticNarrative();});
const refreshEditor=mountEditor();
const KEY='leanduet.workspace.v1',THEME='leanduet.theme';
let typedRoot=null, proofIndex=null, patchNode=null, patchCandidate=null;
let lastTypedSource=null,lastTypedProfile=null,lastTypedTree=null,saveTimer;
let liveTimer,interpretTimer,interpretVersion=0,interpretBusy=false,typedBusy=false;
let exploration=emptyExploration(),wording=[];
let foldedPaths=new Set();
const draftChoices=new Map();let draftChoiceVersion=0,draftIdentity=null;
const draftSession=createDraftSession(),offlineSession=createDraftSession();
function clearDraftChoices(){draftChoices.clear();draftIdentity=null;draftChoiceVersion++;}
let ir,base,rev=0,notesRev=0,candidate=null,narrative=null,timer,selected=null,name='proof',exampleIndex=null,view='reading';
const clean=()=>lean.value===base.lean&&prose.value===base.prose;
const state=(id,label,kind='')=>{$(id).textContent=label;$(id).dataset.state=kind;};
function notice(s,error=false){$('notice').textContent=s;$('notice').classList.toggle('error',error);}
function persist(){clearTimeout(saveTimer);try{localStorage.setItem(KEY,JSON.stringify(snapshot(base,{lean:lean.value,prose:prose.value},notes.value,name,exploration,wording)));state('saveState','Saved locally','pass');}catch{state('saveState','Not saved','dirty');}}
function persistSoon(){clearTimeout(saveTimer);saveTimer=setTimeout(persist,160);}
window.addEventListener('pagehide',()=>{if(base)persist();});
function invalidate({retainReading=false}={}){rev++;clearTimeout(liveTimer);clearTimeout(interpretTimer);interpretVersion++;typedRoot=null;proofIndex=null;foldedPaths.clear();patchNode=null;patchCandidate=null;$('typedPatch').hidden=true;$('applyPatch').disabled=true;$('patchPreview').textContent='';if(retainReading){$('typedNarrative').classList.add('staleReading');$('typedTree').classList.add('staleReading');}else{$('typedNarrative').replaceChildren();$('typedTree').replaceChildren();$('typedNarrative').classList.remove('staleReading');$('typedTree').classList.remove('staleReading');}$('informathOutput').textContent='';$('typedStatus').textContent='Proof changed or not inspected. Run extraction for this revision.';candidate=null;narrative=null;$('accept').disabled=true;$('useNarrative').disabled=true;$('proposal').textContent='No proposal yet.';$('output').textContent='Run the local checker to see diagnostics for this revision.';state('verifyState','Not checked');if(!local){state('verifyState','Local server required');$('output').textContent='Browser-only demo. Run python server.py locally for verification.';}}
function dirty(){state('leanDirty',lean.value===base.lean?'Synced':'Edited',lean.value===base.lean?'':'dirty');state('proseDirty',prose.value===base.prose?'Synced':'Edited',prose.value===base.prose?'':'dirty');gutter();if(!local)showStaticNarrative();}
function gutter(){refreshEditor();$('gutter').textContent=lean.value.split('\n').map((_,i)=>i+1).join('\n');$('gutter').scrollTop=lean.scrollTop;$('cursor').textContent='Ln '+(lean.value.slice(0,lean.selectionStart).split('\n').length);}
function element(tag,txt,cls){const e=document.createElement(tag);if(txt!==undefined)e.textContent=txt;if(cls)e.className=cls;return e;}
const resolutionLabels={
 'candidate-unverified':'Candidate generated · Lean not checked',
 'depends-on-open':'Depends on an open obligation',
 'open-obligation':'Open proof obligation',
 'needs-context':'Needs more context',
 'needs-type-annotation':'Needs an explicit element type',
 'incompatible-type':'Element type conflicts with the known carrier',
 'ambiguous-context':'Set restriction names more than one local object',
 'needs-choice':'A candidate is available · choose how to proceed',
 'ambiguous':'Multiple supported interpretations remain',
 'budget-exhausted':'Candidate search budget exhausted',
 'incompatible-choice':'Current choice no longer fits',
 'incompatible-constraints':'Draft constraints conflict',
 'no-supported-match':'No match in the supported rule set',
 'unsupported':'Wording or rule is not supported',
 'incompatible-target':'Does not match the current goal'
};
function appendResolutionStatus(parent,row){
 const status=row.resolutionStatus||'open-obligation';
 parent.dataset.resolutionStatus=status;
 parent.append(element('small',ui.t(resolutionLabels[status]||status),'resolutionStatus'));
}
function formula(parent,source){
  // Conservative offline token rendering. Unknown syntax is kept as source.
  if(!source||!/^[\p{L}\p{N}\s_=:→∧∨¬↔∀∃()'+*≤≥<>∘∈∉⊆∪∩-]+$/u.test(source)){parent.append(element('code',source));return;}
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
function setView(next){view=next;if(next==='notes')refreshStage();for(const key of ['reading','prose','typed','notes']){$(key+'View').hidden=key!==view;}document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view===view)));}
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
  const h=$('statement');h.replaceChildren();const statement=ir.header.replace(/^(?:theorem|lemma)\s+\S+\s*/,'').replace(/\s*:= by$/,'');const authored=authoredNarrative(renderLean(ir),$('typedLanguage').value);if(authored)appendNarrative(h,authored.statement);else formula(h,statement);$('narrativeStatus').textContent=authored?'Authored example · alignment not formally certified':'Structural view · not a mathematical narrative';
  const box=$('reading'),outline=$('outline');box.replaceChildren();outline.replaceChildren();$('stepCount').textContent=ir.nodes.filter(n=>n.kind!=='blank').length;
  for(const n of ir.nodes){if(n.kind==='blank')continue;const b=element('button',undefined,'step');b.dataset.node=n.id;b.style.marginLeft=Math.min(n.indent-2,8)*5+'px';b.style.width='calc(100% - '+Math.min(n.indent-2,8)*5+'px)';b.append(element('span',String(n.leanLine),'line'));const content=element('span',undefined,'steptext');if(authored?.steps[n.leanLine])appendNarrative(content,authored.steps[n.leanLine]);else{content.append(document.createTextNode(describe(n)+(n.argument===null?'':' ')));if(n.argument!==null)formula(content,n.argument);}b.append(content);b.onclick=()=>selection(n.id,true);b.ondblclick=()=>{selection(n.id);startEdit();};box.append(b);
    const item=element('button',n.leanLine+'  '+n.lean,'outlineItem');item.dataset.node=n.id;item.style.paddingLeft=(10+Math.min(n.indent-2,8)*4)+'px';item.onclick=()=>{setView('reading');selection(n.id,true);};outline.append(item);}
  selected=null;$('stepEditor').hidden=true;$('editStep').disabled=true;$('inspectName').textContent='No step selected';$('inspectCode').textContent='';$('inspectParent').textContent='—';
  refreshAuthoredReading();
}
function install(next,{save=true}={}){clearTimeout(timer);ir=next;const l=renderLean(ir),p=renderProse(ir);if(lean.value!==l)lean.value=l;if(prose.value!==p)prose.value=p;base={lean:l,prose:p};invalidate({retainReading:$('liveNarrative').checked});dirty();reading();notice('Representations synchronized. Lean verification and narrative review are separate.');if(save)persist();scheduleTypedReading();}
function sync(side){clearTimeout(timer);try{install(planSync(base,lean.value,prose.value,side).ir);}catch(e){notice(e.message,true);persist();}}
for(const [el,side] of [[lean,'lean'],[prose,'prose']])el.addEventListener('input',()=>{clearTimeout(timer);invalidate({retainReading:true});$('stepEditor').hidden=true;$('editStep').disabled=true;dirty();notice('Unsynchronized edits · both drafts are retained.');persistSoon();if($('auto').checked)timer=setTimeout(()=>sync(side),450);});
notes.addEventListener('input',()=>{notesRev++;candidate=null;narrative=null;$('accept').disabled=true;$('useNarrative').disabled=true;$('proposal').textContent='Notes changed. Request a new proposal.';$('exploreStatus').textContent='Exploration edited independently of the proof.';refreshStage();persist();});
for(const evt of ['click','keyup','scroll','select'])lean.addEventListener(evt,gutter);
function cursorLink(){
  if(!clean()||document.activeElement!==lean)return;
  const line=lean.value.slice(0,lean.selectionStart).split('\n').length;
  const node=ir.nodes.find(n=>n.leanLine===line&&n.kind!=='blank');
  if(node&&node.id!==selected)selection(node.id,false);
}
for(const evt of ['click','keyup'])lean.addEventListener(evt,cursorLink);
$('focusMode').onclick=()=>{const active=$('focusMode').getAttribute('aria-pressed')!=='true';$('focusMode').setAttribute('aria-pressed',String(active));$('focusMode').textContent=active?'Show Lean':'Focus reading';document.body.classList.toggle('focus-reading',active);setView('reading');};
$('newDoc').onclick=()=>{if(!mayReplace())return;name='Untitled proof';notes.value='';exploration=emptyExploration();wording=[];drawExploration();install(parseLean('theorem my_theorem : True := by\n  sorry\n'));setView('reading');lean.focus();};
$('stepInput').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();$('applyStep').click();}if(e.key==='Escape')$('cancelStep').click();});
$('fromLean').onclick=()=>sync('lean');$('fromProse').onclick=()=>sync('prose');
document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>setView(b.dataset.view));
$('editStep').onclick=startEdit;$('cancelStep').onclick=()=>{$('stepEditor').hidden=true;};
$('stepMode').onchange=resetStepInput;
$('applyStep').onclick=()=>{if(!clean()){notice('Synchronize changes first.',true);return;}try{const fragment=$('stepMode').value==='guided'?sentenceFragment($('stepInput').value):$('stepInput').value;const id=selected;install(replaceStep(lean.value,id,fragment));selection(id);}catch(e){notice(e.message,true);}};
for(const [id,el,key] of [['revertLean',lean,'lean'],['revertProse',prose,'prose']])$(id).onclick=()=>{clearTimeout(timer);if(el.value!==base[key]&&!confirm('Discard unsynchronized changes on this side?'))return;el.value=base[key];invalidate();dirty();persist();notice('Reverted this side.');};
$('adopt').onclick=()=>{try{const next=parseLean(lean.value);if(!confirm('Adopt this Lean source as a new baseline? This replaces the controlled-text draft. Export your workspace first if needed.'))return;install(next);}catch(e){notice(e.message,true);}};
function mayReplace(){return (clean()&&!notes.value&&!exploration.items.length&&!wording.length&&authoredNarrative(base.lean)!==null)||confirm('Replace current workspace? Export it first to preserve both drafts and notes.');}
EXAMPLES.forEach((e,i)=>{const b=element('button',e.name,'example');b.onclick=()=>{if(!mayReplace())return;name=e.name;notes.value='';exploration=emptyExploration();wording=[];drawExploration();exampleIndex=i;install(parseLean(e.source));document.querySelectorAll('.example').forEach((x,j)=>x.classList.toggle('active',j===i));};$('examples').append(b);});
function loadWorkspace(data){const r=restore(data);name=r.name;notes.value=r.notes;exploration=r.exploration;wording=r.wording;drawExploration();install(r.ir,{save:false});lean.value=r.drafts.lean;prose.value=r.drafts.prose;dirty();if(!clean())notice('Restored unsynchronized drafts. Synchronize from the edited side.');persist();}
$('open').onclick=()=>$('file').click();
$('file').onchange=async()=>{try{const f=$('file').files[0];if(!f||!mayReplace())return;if(f.size>1024*1024)throw Error('File exceeds 1 MiB.');const s=await f.text();if(f.name.endsWith('.json'))loadWorkspace(JSON.parse(s));else{const next=parseLean(s.replace(/\r\n/g,'\n'));name=f.name;notes.value='';exploration=emptyExploration();wording=[];drawExploration();install(next);}}catch(e){notice(e.message,true);}finally{$('file').value='';}};
function download(content,filename,type){const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([content],{type}));a.download=filename;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);}
$('download').onclick=()=>download(lean.value,'proof.lean','text/plain');
$('saveDoc').onclick=()=>download(JSON.stringify(snapshot(base,{lean:lean.value,prose:prose.value},notes.value,name,exploration,wording),null,2),'proof.leanduet.json','application/json');
$('exportNotes').onclick=()=>download(notes.value+(exploration.items.length?'\n\n## Working objects (unverified)\n\n'+explorationMarkdown(exploration):''),'exploration.md','text/markdown;charset=utf-8');
function drawExploration(){
  const target=$('exploreObjects');target.replaceChildren();
  for(const item of exploration.items){
    const detail=document.createElement('details');detail.className='exploreObject';
    const summary=document.createElement('summary');
    const title=()=>{const current=exploration.items.find(x=>x.id===item.id);summary.textContent='#'+item.id+' '+(current.label||'(untitled)')+' · '+current.state+' · unverified';};
    title();detail.append(summary);
    const refs=element('p','','hint');
    const showRefs=()=>{const current=exploration.items.find(x=>x.id===item.id);refs.textContent=referencedObjects(exploration,current).map(r=>'#'+r.id+(r.present?'':' (not recorded)')).join(', ');};
    function edit(key,value){try{exploration=updateObject(exploration,item.id,{[key]:value});title();showRefs();persist();}catch(e){$('objectStatus').textContent=e.message;}}
    function field(label,key,multi,max){
      const wrapper=document.createElement('label');wrapper.className='objectField';wrapper.append(document.createTextNode(label));
      const input=document.createElement(multi?'textarea':'input');input.value=item[key];input.maxLength=max;input.spellcheck=false;input.setAttribute('aria-label','#'+item.id+' '+label);input.oninput=()=>edit(key,input.value);wrapper.append(input);detail.append(wrapper);
    }
    field('Name or notation','label',false,256);
    field('Expression / provisional definition','expression',true,12000);
    field('Why it might work or fail','comment',true,12000);
    field('Related objects (free text, e.g. #1, #3)','links',false,1000);
    showRefs();detail.append(refs);
    const label=element('label','Research status (your assessment)','objectField'),select=document.createElement('select');
    for(const status of ['idea','working','doubtful','discarded']){const option=element('option',status);option.value=status;select.append(option);}
    select.value=item.state;select.setAttribute('aria-label','#'+item.id+' Research status');select.onchange=()=>edit('state',select.value);label.append(select);detail.append(label);
    const row=element('div',undefined,'panelactions exploreActions');
    const copy=element('button','Append to notes');copy.onclick=()=>{const current=exploration.items.find(x=>x.id===item.id);appendNotes(explorationMarkdown({schema:1,next:exploration.next,items:[current]}));};
    const alternative=element('button','Try an alternative');alternative.onclick=()=>{const current=exploration.items.find(x=>x.id===item.id);newObject({label:current.label,expression:current.expression,links:'#'+item.id,comment:'Alternative to #'+item.id});};
    const stage=element('button','Try as goal');stage.onclick=()=>{
      const current=exploration.items.find(x=>x.id===item.id);
      stageExplorationFormula(current.expression,'objectStatus');
    };
    row.append(copy,alternative,stage);detail.append(row);target.append(detail);
  }
}
function newObject(initial={}){
  try{exploration=addObject(exploration,initial);drawExploration();const last=$('exploreObjects').lastElementChild;if(last){last.open=true;last.querySelector('input').focus();}persist();$('objectStatus').textContent='Working object recorded. No mathematical validity is implied.';}
  catch(e){$('objectStatus').textContent=e.message;}
}
$('addObject').onclick=()=>newObject();
$('captureObject').onclick=()=>newObject({expression:notes.value.slice(notes.selectionStart,notes.selectionEnd)});
drawExploration();
let offlineTerm=null;
function refreshOffline(){
 const out=$('offlineResult');out.replaceChildren();offlineTerm=null;$('saveDraftFragment').disabled=true;
 try{
   const scope=$('offlineScope').value.trim().split(/\s+/).filter(Boolean);
   if(scope.length>128||scope.some(s=>!/^[A-Za-z_][A-Za-z0-9_']{0,63}$/.test(s)))throw Error('Enter up to 128 simple Lean context names.');
   const r=offlineSession.evaluate($('offlineDraft').value,scope);
   for(const row of r.rows){
     const p=element('div',undefined,'ruleResult');p.append(element('small','Line '+row.line+' · '+row.status+(row.proofStatus?' · '+row.proofStatus:'')),element('span',row.raw));appendResolutionStatus(p,row);
     if(row.reason)p.append(element('small',row.reason));out.append(p);
   }
   if(r.term){offlineTerm=r.term;out.append(element('p','Candidate fragment · not checked','hint'),element('pre',r.term));$('saveDraftFragment').disabled=false;}
 }catch(e){out.append(element('p',e.message));}
}
$('offlineDraft').oninput=refreshOffline;$('offlineScope').oninput=refreshOffline;
$('copyNotesToDraft').onclick=()=>{const selected=notes.value.slice(notes.selectionStart,notes.selectionEnd);$('offlineDraft').value=(selected||notes.value).slice(0,12000);refreshOffline();};
$('saveDraftFragment').onclick=()=>{if(offlineTerm)download(offlineTerm+'\n','candidate-fragment.lean','text/plain;charset=utf-8');};
function refreshStage(){
  $('stageFormula').disabled=!(patchNode&&typedRoot&&clean()&&patchNode.kind!=='witness'&&notes.selectionStart!==notes.selectionEnd);
}
for(const evt of ['select','keyup','mouseup','focus'])notes.addEventListener(evt,refreshStage);
function appendNotes(text){
  const separator=notes.value&&!notes.value.endsWith('\n\n')?(notes.value.endsWith('\n')?'\n':'\n\n'):'';
  notes.value+=separator+text;
  notes.dispatchEvent(new Event('input'));
}
$('noteGoal').onclick=()=>{
  if(!patchNode||!typedRoot||!clean())return;
  const n=patchNode;
  const context=(n.scope||[]).map(d=>d.name+' : '+d.type).join('\n');
  appendNotes('### Goal snapshot — unverified notes\n\n'+
    'Source: '+name+' · '+n.path+'\n\n'+(context?'Context:\n'+context+'\n\n':'')+
    'Goal:\n'+n.type+'\n\nIdeas:\n');
  setView('notes');notes.focus();notes.setSelectionRange(notes.value.length,notes.value.length);
};
$('stageFormula').onclick=()=>stageExplorationFormula(notes.value.slice(notes.selectionStart,notes.selectionEnd),'exploreStatus');
function stageExplorationFormula(raw,statusId){
  if(!patchNode||!typedRoot||!clean()||patchNode.kind==='witness'){
    $(statusId).textContent='Select a typed proof goal first. Your working expression is retained.';return;
  }
  const selected=raw.trim();
  try{
    if(!((selected.startsWith('$')&&selected.endsWith('$'))||(selected.startsWith('\\(')&&selected.endsWith('\\)'))||(selected.startsWith('\\[')&&selected.endsWith('\\]'))))throw Error('Select one delimited LaTeX formula, not the entire argument.');
    compileFormula(selected);
    $('formulaGoal').value=selected;$('formulaGoal').dispatchEvent(new Event('input'));
    $('ruleStatus').textContent='Staged from exploration. Find typed proofs to check the goal in Lean.';
    $(statusId).textContent='Formula staged; working objects, notes and Lean source are unchanged.';
    setView('typed');$('formulaGoal').focus();
  }catch(e){$(statusId).textContent='Not staged: '+e.message+' Your exploration is unchanged.';}
}
let completionVersion=0;
function hideCompletion(){completionVersion++;$('completionPanel').hidden=true;}
$('closeCompletion').onclick=hideCompletion;
lean.addEventListener('input',hideCompletion);
lean.addEventListener('keydown',e=>{
  if(e.ctrlKey&&e.code==='Space'&&local){e.preventDefault();$('completeLean').click();}
  if(e.key==='Escape')hideCompletion();
});
$('completeLean').onclick=async()=>{
  if(!local)return;
  if(lean.selectionStart!==lean.selectionEnd){notice('Place the cursor at a single completion position.',true);return;}
  const source=lean.value,cursor=lean.selectionStart,version=++completionVersion;
  $('completionPanel').hidden=false;$('completionItems').replaceChildren();$('completionStatus').textContent='Requesting native Lean language-server completion…';
  try{
    const r=await api('completion',{source,...positionAt(source,cursor)});
    if(version!==completionVersion||source!==lean.value)return;
    $('completionStatus').textContent=r.items.length?r.items.length+' suggestions from Lean LSP · select to insert.':'No completion suggestions at this position.';
    for(const item of r.items){
      const b=element('button',item.label,'completionItem');if(item.detail)b.title=item.detail;
      b.onclick=()=>{
        if(version!==completionVersion||source!==lean.value||lean.selectionStart!==cursor||lean.selectionEnd!==cursor){hideCompletion();notice('Source or cursor changed. Request completion again.',true);return;}
        try{const e=completionEdit(source,cursor,item);lean.setRangeText(e.text,e.start,e.end,'end');lean.dispatchEvent(new Event('input'));lean.focus();}
        catch(err){$('completionStatus').textContent=err.message;}
      };
      $('completionItems').append(b);
    }
  }catch(e){if(version===completionVersion)$('completionStatus').textContent=e.message;}
};
async function api(path,payload){const r=await fetch('/api/'+path,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});if(!r.headers.get('content-type')?.includes('application/json'))throw Error('Local backend not available. Start python server.py.');const d=await r.json();if(!r.ok)throw Error(d.error||'Request failed');return d;}
$('check').onclick=async()=>{if(!clean()){notice('Synchronize first.',true);return;}const snapshotRev=rev;$('check').disabled=true;state('verifyState','Checking…');$('output').textContent='Running Lean…';try{const r=await api('check',{source:lean.value});if(snapshotRev!==rev)return;$('output').textContent=r.output;state('verifyState',r.status==='passed'?'Lean passed':r.status,r.status==='passed'?'pass':'dirty');notice('Lean check: '+r.status,r.status!=='passed');}catch(e){if(snapshotRev===rev){state('verifyState','Unavailable','dirty');$('output').textContent=e.message;notice('Checker unavailable: '+e.message,true);}}finally{$('check').disabled=false;}};
function renderTyped(node,container,depth=0){
  if(!node||typeof node.kind!=='string'||depth>12)return;
  const block=element('details',undefined,'typedNode');block.open=depth<3;
  const title=element('summary');
  const label={assume:'Assume',introduce:'Introduce',apply:'Apply',let:'Establish local binding',hypothesis:'Use hypothesis',reference:'Use declaration',opaque:'Opaque term',witness:'Choose witness'}[node.kind]||node.kind;
  title.append(element('strong',label+(node.binder?' '+node.binder:node.reference?' '+node.reference:'')));
  block.append(title);
  if(node.editable&&node.path&&local){const edit=element('button',node.kind==='witness'?'Replace witness':'Replace this proof','typedEdit');edit.onclick=()=>openPatch(node);block.append(edit);}
  const typ=element('div',undefined,'typedType');typ.append(element('span','Type / conclusion','eyebrow'));typ.append(element('code',node.type||''));block.append(typ);
  if(node.binderType)block.append(element('code','Binder: '+node.binderType));
  if(node.referenceType)block.append(element('code','Reference type: '+node.referenceType));
  const term=element('details');term.append(element('summary','Elaborated term'));term.append(element('pre',node.term||''));block.append(term);
  for(const child of node.children||[])renderTyped(child,block,depth+1);
  container.append(block);
}
function findTypedNode(root,path){
  if(!root)return null;
  if(root===typedRoot&&proofIndex)return proofIndex.find(path);
  if(root.path===path)return root;
  for(const child of root.children||[]){const found=findTypedNode(child,path);if(found)return found;}
  return null;
}
// Only exact, synchronized built-in source gets an offline authored reading.
function showStaticNarrative(){
  const target=$('typedNarrative'), treeContainer=$('typedTree');target.replaceChildren();treeContainer.replaceChildren();
  target.classList.remove('staleReading');treeContainer.classList.remove('staleReading');
  const lang=$('typedLanguage').value;
  const source=base&&clean()?lean.value:null;
  const cached=staticProofs.get(source);
  if(cached){
    $('typedStatus').textContent='Build-time Lean extraction · exact built-in source · no live checking.';
    target.append(element('div',ui.t('BUILD-TIME LEAN EXTRACTION · READ-ONLY'),'eyebrow'));
    target.append(element('p',staticToolchain,'hint'));
    for(const row of narrate(cached,lang,{style:'detail'})){
      const line=element('div',undefined,'derivedStep');line.style.marginLeft=Math.min(row.depth,6)*9+'px';
      line.append(document.createTextNode(row.phrase+' '));formula(line,row.expr);
      if(row.truncated||row.omittedProofArguments)line.append(element('span',phrase(lang,'limited'),'foldCount'));
      target.append(line);
    }
    renderTyped(cached,treeContainer);
    return;
  }
  const authored=source?authoredNarrative(source,lang):null;
  $('typedStatus').textContent=authored?'Static example · authored reading, not an elaborated proof tree.':'Static demo: select a built-in example for multilingual reading; arbitrary proof extraction requires local Lean.';
  if(!authored)return;
  target.append(element('div',ui.t('AUTHORED EXAMPLE · NOT VERIFIED'),'eyebrow'));
  const statement=element('p');appendNarrative(statement,authored.statement);target.append(statement);
  for(const [line,parts] of Object.entries(authored.steps)){
    const row=element('div',undefined,'derivedStep');
    row.append(element('span',line+' ','inferenceNumber'));appendNarrative(row,parts);target.append(row);
  }
}
function refreshAuthoredReading(){
  if(!ir)return;
  const lang=$('typedLanguage').value, authored=authoredNarrative(renderLean(ir),lang);
  if(!authored)return;
  const statement=$('statement');statement.replaceChildren();appendNarrative(statement,authored.statement);
  for(const n of ir.nodes){
    const content=document.querySelector('#reading [data-node="'+n.id+'"] .steptext');
    if(content&&authored.steps[n.leanLine]){content.replaceChildren();appendNarrative(content,authored.steps[n.leanLine]);}
  }
  $('narrativeStatus').textContent=['en','zh','ja'].includes(lang)?'Authored example · alignment not formally certified':'Authored example · English fallback for this language pack.';
}
function showTypedNarrative(){
  if(!local){showStaticNarrative();return;}
  const target=$('typedNarrative');target.replaceChildren();if(!typedRoot)return;
  target.append(element('div','DERIVED READING · TYPE-DRIVEN','eyebrow'));
  const wordingByKey=new Map(wording.map(a=>[a.anchor,a.text]));
  const detached=wording.filter(a=>!proofIndex.unique(a.anchor));if(detached.length){const details=element('details');details.append(element('summary',detached.length+' detached author annotation(s)'));for(const a of detached){const p=element('p',a.path+' · '+a.text);const b=element('button','Copy to exploration');b.onclick=()=>appendNotes('Detached wording: '+a.text);const attach=element('button','Reattach to selected step');attach.type='button';
    attach.onclick=()=>{
     if(!patchNode||!clean()||proofIndex?.find(patchNode.path)!==patchNode){notice('Select a current proof step before reattaching wording.',true);return;}
     try{
      wording=reattachWording(wording,typedRoot,a.anchor,patchNode);
      $('wordingInput').value=wordingFor(typedRoot,patchNode,wording);
      $('wordingStatus').textContent='Reattached by author; Lean unchanged.';
      showTypedNarrative();persist();notice('Author wording reattached without changing Lean.');
     }catch(e){notice(e.message,true);}
    };
    p.append(b,attach);details.append(p);}target.append(details);}
  for(const row of narrate(typedRoot,$('typedLanguage').value,{collapsed:foldedPaths,counts:proofIndex.counts,style:$('narrativeStyle').value})){
    const line=element('div',undefined,'derivedStep');line.style.marginLeft=Math.min(row.depth,6)*9+'px';
    const lang=$('typedLanguage').value;
    if(row.foldable){
      const toggle=element('button',row.folded?'▸':'▾','proofDisclosure');
      toggle.setAttribute('aria-expanded',String(!row.folded));
      toggle.setAttribute('aria-label',(row.folded?'Expand ':'Collapse ')+row.path);
      toggle.onclick=()=>{if(row.folded)foldedPaths.delete(row.path);else foldedPaths.add(row.path);showTypedNarrative();};
      line.append(toggle);
    }
    const owner=findTypedNode(typedRoot,row.path);const authored=proofIndex.wording(owner,wordingByKey);if(row.stepLabel)line.append(element('span',row.stepLabel+' ','inferenceNumber'));if(authored)line.append(element('span',authored+' ','authorWording'));line.append(document.createTextNode(row.phrase+' '));formula(line,row.expr);
    if(row.bindingValue){line.append(document.createTextNode(' := '));formula(line,row.bindingValue);}
    if(row.premises?.length){const premises=element('div',undefined,'narrativePremises');premises.append(element('span',({en:'Premises shown:',zh:'所用前提：',ja:'表示された前提：'})[lang]||'Premises shown:'));for(const p of row.premises){const detail=element('span',p.label||p.term||p.type,'premiseRef');detail.title=p.type;if(p.path)detail.dataset.proofPath=p.path;premises.append(detail);}line.append(premises);}
    if(row.folded)line.append(element('span',' · '+row.hiddenCount+' '+phrase(lang,'hidden'),'foldCount'));
    if(row.truncated||row.omittedProofArguments)line.append(element('span',phrase(lang,'limited'),'foldCount'));
    if(local&&row.editable){
      const node=findTypedNode(typedRoot,row.path);
      if(node){
        const lang=$('typedLanguage').value;
        const edit=element('button',phrase(lang,'edit'),'narrativeEdit');
        edit.dataset.proofPath=row.path;
        edit.onclick=()=>{if(findTypedNode(typedRoot,row.path)===node)openPatch(node);};
        line.append(edit);
      }
    }
    target.append(line);
  }
}
function refreshLanguageOptions(selected){
  const select=$('typedLanguage');select.replaceChildren();
  for(const p of languagePacks()){const o=element('option',p.label);o.value=p.id;select.append(o);}
  select.value=languagePacks().some(p=>p.id===selected)?selected:'en';
  $('ruleConcepts').replaceChildren();
  for(const label of conceptLabels()){const o=element('option');o.value=label;$('ruleConcepts').append(o);}
}
try{for(const p of JSON.parse(localStorage.getItem('leanduet.languages.v1')||'[]'))registerPack(p);}catch(e){$('languageStatus').textContent='Stored language pack rejected: '+e.message;}
refreshLanguageOptions(localStorage.getItem('leanduet.language')||ui.language());
try{localStorage.setItem('leanduet.language',$('typedLanguage').value);}catch{}
$('typedLanguage').onchange=()=>{try{localStorage.setItem('leanduet.language',$('typedLanguage').value);}catch{}refreshAuthoredReading();showTypedNarrative();};
$('importLanguage').onclick=()=>$('languageFile').click();
$('languageFile').onchange=async()=>{
  const f=$('languageFile').files[0];if(!f)return;
  try{if(f.size>262144)throw Error('Language pack exceeds 256 KiB.');
    const p=registerPack(JSON.parse(await f.text()));
    localStorage.setItem('leanduet.languages.v1',JSON.stringify(customPacks()));
    refreshLanguageOptions(p.id);$('typedLanguage').onchange();$('languageStatus').textContent='Loaded '+p.label+' · data-only language pack.';
  }catch(e){$('languageStatus').textContent=e.message;}
  finally{$('languageFile').value='';}
};
$('narrativeStyle').onchange=showTypedNarrative;
$('collapseProof').onclick=()=>{foldedPaths=outlinePaths(typedRoot);showTypedNarrative();};
$('expandProof').onclick=()=>{foldedPaths.clear();showTypedNarrative();};
function openPatch(node){
  if(!clean()||!typedRoot||proofIndex?.find(node.path)!==node)return;
  clearDraftChoices();draftSession.reset();patchNode=node;patchCandidate=null;interpretVersion++;clearTimeout(interpretTimer);$('interpretPanel').hidden=node.kind==='witness';$('interpretPanel').open=false;$('interpretText').value='';$('aiInterpretText').value='';$('includeAiInterpret').checked=false;$('aiInterpretStatus').textContent='';$('interpretAiPanel').open=false;$('interpretResults').replaceChildren();$('interpretStatus').textContent='';$('typedPatch').hidden=false;$('applyPatch').disabled=true;
  $('irOutput').textContent='';$('irStatus').textContent='';$('irInspector').open=false;
  $('abstractPanel').hidden=node.kind==='witness';$('abstractPanel').open=false;$('abstractOutput').textContent='';$('abstractStatus').textContent='';$('factorProof').disabled=true;
  $('wordingInput').value=wordingFor(typedRoot,node,wording);$('wordingStatus').textContent='Author wording, not a checked assertion.';$('patchTarget').textContent=node.path+' · '+node.type;$('patchTerm').value=node.term||'';
  $('chainEditor').hidden=node.kind==='witness';$('chainEditor').open=false;$('chainText').value='';$('draftTranslation').replaceChildren();$('chainStatus').textContent='';$('chainBindings').replaceChildren();
  $('ruleSearch').hidden=node.kind==='witness';$('ruleResults').replaceChildren();$('ruleIntent').value='';$('formulaGoal').value='';$('formulaPreview').textContent='';$('ruleStatus').textContent='Leave blank for goal-type search. You can also specify a rule and required premises.';
  const witness=(node.children||[]).find(x=>x.kind==='witness');
  const evidence=(node.children||[]).find(x=>x.kind!=='witness');
  const paired=node.reference==='Exists.intro'&&witness&&evidence;
  $('witnessPair').hidden=!paired;
  if(paired){$('witnessValue').value=witness.term||'';$('witnessEvidence').value=evidence.term||'';}
  $('patchScope').replaceChildren();$('patchChoices').replaceChildren();$('usedContextOnly').checked=false;
  const scope=node.scope||[];
  for(const d of scope){
    const row=element('div',undefined,'scopeRow');
    const info=element('div');info.append(element('code',d.type));
    row.dataset.needed=String(d.neededForContext===true);
    const dependencies=(d.dependsOn||[]).map(index=>scope.find(x=>x.contextIndex===index)).filter(Boolean);
    if(dependencies.length||d.hiddenDependencies)info.append(element('small','Context dependencies: '+dependencies.map(x=>x.name+' (#'+x.contextIndex+')').join(', ')+(d.hiddenDependencies?' · '+d.hiddenDependencies+' internal declaration(s)':''),'dependencyUse'));
    const usage=[d.usedInTerm?'term':null,d.usedInType?'type':null].filter(Boolean);
    if(usage.length)info.append(element('small','Direct occurrence: '+usage.join(' + '),'dependencyUse'));
    else if(d.neededForContext)info.append(element('small','Indirect context dependency','dependencyUse'));
    if(scope.filter(x=>x.name===d.name).length>1)row.dataset.contextIndex=String(d.contextIndex);
    row.append(element('strong',d.name+(row.dataset.contextIndex?' (#'+d.contextIndex+')':'')),info);$('patchScope').append(row);
    // Only offer unambiguous simple names; the actual term must still pass Lean.
    if(d.matchesGoal&&/^[A-Za-z_][A-Za-z0-9_']*$/.test(d.name)&&scope.filter(x=>x.name===d.name).length===1){
      const button=element('button',(node.kind==='witness'?($('typedLanguage').value==='zh'?'选取对象 ':'Choose object '):($('typedLanguage').value==='zh'?'使用假设 ':'Use hypothesis '))+d.name,'suggestion');
      button.onclick=()=>{$('patchTerm').value=d.name;$('patchTerm').dispatchEvent(new Event('input'));$('patchTerm').focus();};
      $('patchChoices').append(button);
    }
  }
  for(const a of node.applications||[]){
    const safe=n=>/^[A-Za-z_][A-Za-z0-9_']*$/.test(n)&&scope.filter(x=>x.name===n).length===1;
    if(!safe(a.function)||!safe(a.argument))continue;
    const term=a.function+' '+a.argument;
    const button=element('button',($('typedLanguage').value==='zh'?'应用 ':'Apply ')+a.function+($('typedLanguage').value==='zh'?' 于 ':' to ')+a.argument,'suggestion');
    button.onclick=()=>{$('patchTerm').value=term;$('patchTerm').dispatchEvent(new Event('input'));$('patchTerm').focus();};
    $('patchChoices').append(button);
  }
  $('patchSuggestions').hidden=!$('patchChoices').children.length;
  $('patchPreview').textContent='';$('patchStatus').textContent=node.kind==='witness'?'Choose a new witness. Lean will recheck all dependent proof obligations; the unchanged evidence may become invalid.':'Edit the local proof term. Lean will check its type and the entire exported theorem.';
  $('typedPatch').scrollIntoView({block:'nearest'});$('patchTerm').focus();
}
$('abstractProof').onclick=async()=>{
  if(!patchNode||!clean()||!local||patchNode.kind==='witness')return;
  const node=patchNode,revision=rev;
  $('abstractProof').disabled=true;$('factorProof').disabled=true;$('abstractOutput').textContent='';$('abstractStatus').textContent='Abstracting the dependency-closed proof…';
  try{
    const r=await api('abstract',{source:lean.value,path:node.path});
    if(revision!==rev||node!==patchNode)return;
    $('abstractStatus').textContent=r.exportNote+' · '+r.parameters.length+' context declarations.';$('factorProof').disabled=!r.exportShapePreserved;
    $('abstractOutput').textContent=r.source||('Closed judgment (not certified as standalone source):\n'+r.type+'\n\n'+r.term);
  }catch(e){if(revision===rev&&node===patchNode)$('abstractStatus').textContent=e.message;}
  finally{$('abstractProof').disabled=false;}
};
$('factorProof').onclick=async()=>{
  if(!patchNode||!clean()||!local||patchNode.kind==='witness')return;
  const node=patchNode,revision=rev;
  $('factorProof').disabled=true;$('abstractOutput').textContent='';$('abstractStatus').textContent='Checking the factored two-theorem source…';
  try{
    const r=await api('factor',{source:lean.value,path:node.path});
    if(revision!==rev||node!==patchNode)return;
    $('abstractStatus').textContent=r.note+' Preview only: copy the source into a separate Lean document.';
    $('abstractOutput').textContent=r.source;
  }catch(e){if(revision===rev&&node===patchNode)$('abstractStatus').textContent=e.message;}
  finally{if(revision===rev&&node===patchNode)$('factorProof').disabled=false;}
};
$('inspectIR').onclick=async()=>{
  if(!patchNode||!clean()||!local)return;
  const node=patchNode,revision=rev,input=$('formulaGoal').value;
  $('inspectIR').disabled=true;$('irOutput').textContent='';$('irStatus').textContent='Reading structured Lean judgment…';
  try{
    const formula=node.kind!=='witness'&&input.trim()?compileFormula(input).lean:'';
    const ir=validateJudgment(await api('ir',{source:lean.value,path:node.path,formula}));
    if(revision!==rev||node!==patchNode||input!==$('formulaGoal').value)return;
    $('irOutput').textContent=JSON.stringify(ir,null,2);
    const match=ir.judgment.formula;
    $('irStatus').textContent=(ir.judgment.roundTrip?.checked?'Lean round trip checked · fresh context · ':'Scope and structure validated · ')+ir.judgment.context.length+' local declarations'+(match?(match.matchesGoal?' · formula matches goal':' · formula does not match goal'):'');
  }catch(e){if(revision===rev&&node===patchNode)$('irStatus').textContent=e.message;}
  finally{$('inspectIR').disabled=false;}
};
$('usedContextOnly').onchange=()=>{for(const row of $('patchScope').children)row.hidden=$('usedContextOnly').checked&&row.dataset.needed!=='true';};
$('ruleIntent').addEventListener('input',()=>{$('ruleResults').replaceChildren();$('ruleStatus').textContent='Query changed. Search again.';});
$('formulaGoal').addEventListener('input',()=>{
  $('irOutput').textContent='';$('irStatus').textContent='Formula changed. Inspect again.';
  $('ruleResults').replaceChildren();$('ruleStatus').textContent='Formula changed. Search again.';
  const s=$('formulaGoal').value.trim();
  try{$('formulaPreview').textContent=s?'Lean candidate: '+compileFormula(s).lean:'';}
  catch(e){$('formulaPreview').textContent=e.message;}
});
$('findRules').onclick=async()=>{
  if(!patchNode||!clean()||patchNode.kind==='witness')return;
  const node=patchNode,snapshotRev=rev,query=$('ruleIntent').value,formulaInput=$('formulaGoal').value;
  const target=$('ruleResults');target.replaceChildren();
  $('findRules').disabled=true;$('ruleStatus').textContent='Searching in the selected Lean context…';
  try{
    const intent=parseRuleIntent(query);
    const formula=formulaInput.trim()?compileFormula(formulaInput).lean:'';
    const r=await api('search',{source:lean.value,path:node.path,...intent,formula});
    if(snapshotRev!==rev||patchNode!==node||$('ruleIntent').value!==query||$('formulaGoal').value!==formulaInput)return;
    const candidates=r.candidates||[];
    $('ruleStatus').textContent=candidates.length?candidates.length+' locally closed candidate(s) · select one, then check replacement.':'No closed candidate found in the bounded search. This is not a proof of impossibility.';
    for(const c of candidates){
      const row=element('div',undefined,'ruleResult');row.append(element('strong',c.rule),element('code',c.term));
      const use=element('button','Use this proof');use.onclick=()=>{$('patchTerm').value=c.term;$('patchTerm').dispatchEvent(new Event('input'));};row.append(use);target.append(row);
    }
  }catch(e){if(snapshotRev===rev&&patchNode===node)$('ruleStatus').textContent=e.message;}
  finally{$('findRules').disabled=false;}
};
$('wordingInput').oninput=()=>{if(!patchNode||!typedRoot||!clean())return;try{wording=putWording(wording,typedRoot,patchNode,$('wordingInput').value);showTypedNarrative();persist();$('wordingStatus').textContent='Author wording recorded; Lean unchanged.';}catch(e){$('wordingStatus').textContent=e.message;}};
$('saveInterpretDraft').onclick=()=>{if($('interpretText').value.trim())newObject({label:'Interpretation draft',expression:$('interpretText').value,comment:'Unverified alternatives'});};
function drawInterpretations(plan,checked=null){
  const target=$('interpretResults');target.replaceChildren();
  for(const a of plan.unresolved){const row=element('div',undefined,'ruleResult');row.append(element('strong','Unresolved · retained'),element('code',a.raw),element('small',a.reason));target.append(row);}
  if(!checked){for(const a of plan.alternatives){const row=element('div',undefined,'ruleResult');row.append(element('strong',a.origin+' · not checked'),element('code',a.term||[a.formula,a.rule,...a.required].filter(Boolean).join(' · ')));target.append(row);}return;}
  for(const row of checked.interpretations||[]){if(row.status==='locally-checked')continue;const a=plan.alternatives[row.index];const d=element('div',undefined,'ruleResult');d.append(element('strong',row.status+' · retained'),element('code',a.raw));target.append(d);}
  for(const c of rankInterpretations(plan,checked)){
    const row=element('div',undefined,'ruleResult');row.append(element('strong',c.rule+' · locally checked'),element('code',c.term),element('small','From: '+c.interpretation.raw));
    if(c.interpretation.modifiers.length)row.append(element('small','Discourse: '+c.interpretation.modifiers.join(' ')));
    const use=element('button','Use candidate');use.onclick=()=>{$('patchTerm').value=c.term;$('patchTerm').dispatchEvent(new Event('input'));};row.append(use);target.append(row);
  }
}
function planInterpretation(){const scope=(patchNode?.scope||[]).map(d=>d.name);const facts=factsFromScope(patchNode?.scope);const primary=interpretations($('interpretText').value,scope,facts);return $('includeAiInterpret').checked?mergeInterpretations(primary,interpretations($('aiInterpretText').value,scope,facts)):primary;}
async function checkInterpretations(){
  if(!patchNode||!clean()||!local||patchNode.kind==='witness'||interpretBusy)return;
  const node=patchNode,revision=rev,version=interpretVersion,raw=$('interpretText').value;
  const plan=planInterpretation();drawInterpretations(plan);
  if(!plan.alternatives.length){$('interpretStatus').textContent='No supported interpretation yet. Your text is retained.';return;}
  interpretBusy=true;$('interpretRun').disabled=true;$('interpretStatus').textContent='Checking bounded alternatives in Lean…';
  try{
    const r=await api('interpret',{source:lean.value,path:node.path,alternatives:plan.alternatives});
    if(revision!==rev||version!==interpretVersion||node!==patchNode)return;
    drawInterpretations(plan,r);$('interpretStatus').textContent=rankInterpretations(plan,r).length+' locally checked candidate(s). Select, then check the rebuilt proof.';
  }catch(e){if(revision===rev&&version===interpretVersion&&node===patchNode)$('interpretStatus').textContent=e.message;}
  finally{interpretBusy=false;$('interpretRun').disabled=false;if(version!==interpretVersion&&patchNode&&clean()&&$('liveInterpret').checked)scheduleInterpretation();}
}
function scheduleInterpretation(){clearTimeout(interpretTimer);if($('liveInterpret').checked&&local)interpretTimer=setTimeout(checkInterpretations,750);}
$('interpretText').oninput=()=>{interpretVersion++;$('includeAiInterpret').checked=false;if($('aiInterpretText').value)$('aiInterpretStatus').textContent='Original wording changed; suggestions are retained but no longer included.';try{drawInterpretations(planInterpretation());$('interpretStatus').textContent='Draft interpretations · not yet checked';scheduleInterpretation();}catch(e){$('interpretStatus').textContent=e.message;}};
$('liveInterpret').onchange=scheduleInterpretation;
$('aiInterpretText').oninput=()=>{interpretVersion++;$('includeAiInterpret').checked=false;$('aiInterpretStatus').textContent='Review the modified alternatives before including them.';drawInterpretations(planInterpretation());};
$('includeAiInterpret').onchange=()=>{interpretVersion++;drawInterpretations(planInterpretation());scheduleInterpretation();};
$('interpretRun').onclick=checkInterpretations;
$('suggestInterpretations').onclick=async()=>{
  if(!local||!patchNode||!clean()||!$('interpretText').value.trim())return;
  if(!confirm('Send this mathematical wording, current Lean proof and selected context to your configured AI provider?'))return;
  const node=patchNode,revision=rev,version=interpretVersion,raw=$('interpretText').value;
  $('suggestInterpretations').disabled=true;$('aiInterpretStatus').textContent='Requesting unverified alternatives…';
  try{
    const r=await api('interpretations',{source:lean.value,prose:JSON.stringify({wording:raw,goal:node.type,scope:(node.scope||[]).map(x=>({name:x.name,type:x.type}))})});
    if(revision!==rev||node!==patchNode||version!==interpretVersion)return;
    if(!Array.isArray(r.lines))throw Error('Provider did not return alternatives.');
    $('aiInterpretText').value=r.lines.join('\n');$('includeAiInterpret').checked=false;
    $('aiInterpretStatus').textContent='Review or edit these unverified suggestions. Include them explicitly to check.';
    interpretVersion++;drawInterpretations(planInterpretation());
  }catch(e){if(revision===rev&&node===patchNode&&version===interpretVersion)$('aiInterpretStatus').textContent=e.message;}
  finally{$('suggestInterpretations').disabled=false;}
};
function parseChainInput(text,scope){const mode=$('chainFormat').value;return mode==='formula'?compileFormulaSequence(text,scope):mode==='natural'?draftSession.compile(text,scope,factsFromScope(patchNode?.scope),{choices:draftChoices,goal:patchNode?.type}):compileChain(text,scope);}
$('chainFormat').onchange=()=>{$('chainText').placeholder=$('chainFormat').value==='formula'?'$Q$\n$R$':$('chainFormat').value==='natural'?'建立 hq : $Q$，由 f，使用 p\n因此 $R$，由 g，使用 hq\n\n分情况讨论 h，建立 hR : $R$\n  左支 hp\n    $R$ | f hp\n  右支 hq\n    $R$ | g hq\n$R$ | hR':'Establish hq | f using p\nConclude | g using hq';$('chainText').dispatchEvent(new Event('input'));};
$('chainText').addEventListener('input',()=>{draftChoiceVersion++;if($('chainFormat').value!=='natural')clearDraftChoices();$('chainBindings').replaceChildren();$('patchTerm').value='';$('patchTerm').dispatchEvent(new Event('input'));$('chainStatus').textContent='Narrative changed. Stage the new candidate.';previewDraft({edited:true});});
function previewDraft({edited=false,choices=draftChoices}={}){
 const target=$('draftTranslation');target.replaceChildren();
 if($('chainFormat').value!=='natural'||!patchNode)return;
 try{
   const input=$('chainText').value,scope=(patchNode.scope||[]).map(d=>d.name),facts=factsFromScope(patchNode.scope);
    if(edited&&choices.size){
     // Earlier restored choices can reveal later candidate domains. Replay
     // until the choice map stabilizes; abandon migration on nonconvergence.
     const original=new Map(choices);let migrated=new Map(),stable=false;
     for(let pass=0;pass<=original.size+1;pass++){
      const probe=draftSession.evaluate(input,scope,facts,{goal:patchNode.type,choices:migrated});
      const correspondence=reconcileDraftIdentity(draftIdentity,probe.graph);
      const next=migrateDraftChoices(draftIdentity,correspondence,original);
      if(JSON.stringify([...next])===JSON.stringify([...migrated])){stable=true;break;}
      migrated=next;
     }
     choices.clear();if(stable)for(const [line,term] of migrated)choices.set(line,term);
    }
    const r=draftSession.evaluate(input,scope,facts,{choices,goal:patchNode.type});
    draftIdentity=reconcileDraftIdentity(draftIdentity,r.graph);
   const shownGroups=new Set();
   function refreshChoice(line=null,key=null){draftChoiceVersion++;$('chainBindings').replaceChildren();$('patchTerm').value='';$('patchTerm').dispatchEvent(new Event('input'));if(line!==null){if(key===null)draftChoices.delete(line);else draftChoices.set(line,key);} $('chainStatus').textContent='Candidate choice changed. Stage and check again.';previewDraft({choices:new Map(draftChoices)});}
   for(const x of r.rows){
     const d=element('div',undefined,'ruleResult');
     d.dataset.objectId=draftIdentity.ids.get(x.graphId||'line:'+x.line)||'';
     d.append(element('small','Line '+x.line+' · '+x.status+(x.proofStatus?' · '+x.proofStatus:'')),element('span',x.raw));
     appendResolutionStatus(d,x);
     if(x.step)d.append(element('code',['introduce','assume'].includes(x.step.kind)?'intro '+x.step.name:x.step.kind==='obtain'?'obtain ⟨'+x.step.name+', '+x.step.evidenceName+'⟩ from '+x.step.source+' : '+x.step.type+'; '+x.step.evidenceType:x.step.kind==='define'?'let '+x.step.name+' : '+x.step.type+' := '+x.step.value:x.step.kind==='establish'?'have '+x.step.name+' : '+x.step.type+' := '+x.step.application:x.step.kind==='local-lemma'?'have '+x.step.name+' : '+x.step.type+' by a scoped subproof':x.step.kind==='cases'?'cases '+x.step.source+' into '+x.step.branches.map(b=>b.constructor+' '+b.name+': '+b.type).join(' / ')+'; establish '+x.step.name+' : '+x.step.type:x.step.kind==='and-intro'?'split conjunction into '+x.step.subgoals.map(g=>g.id+': '+g.goal).join(' and '):x.step.kind==='iff-intro'?'prove both directions of '+x.type:x.step.kind==='exists-intro'?'construct witness '+x.step.witness+' for '+x.type:'show '+x.step.type+'; '+x.step.application));
     if((x.step?.kind==='cases'||x.kind==='cases')&&x.branches?.length){
      const branches=element('details');branches.append(element('summary','Branch-local assumptions · common result '+(x.step?.name||x.name)+' : '+x.type));
      for(const branch of x.branches)branches.append(element('small',branch.constructor+' '+branch.name+' : '+branch.type+' ⊢ '+(branch.goal||x.type)+' · '+(branch.status||'open')));
      d.append(branches);
     }
     if((['and-intro','iff-intro','exists-intro','local-lemma'].includes(x.step?.kind)||['and-intro','iff-intro','exists-intro','local-lemma'].includes(x.kind))&&x.subgoals?.length){
      const subgoals=element('details');subgoals.append(element('summary','Child goals · '+x.type));
      for(const subgoal of x.subgoals)subgoals.append(element('small',subgoal.id+' · '+subgoal.goal+' · '+(subgoal.status||'open')));
      d.append(subgoals);
     }
     if(x.reason)d.append(element('small',x.reason));
     if(x.rejectedCandidates?.length){
      const rejected=element('details');rejected.append(element('summary','Other operation readings ruled out by the explicit goal'));
      for(const candidate of x.rejectedCandidates){
       const line=candidate.rejectedBy?.line;
       rejected.append(element('small',candidate.term+' · '+candidate.schema+(line?' · conflicts with line '+line+' goal '+candidate.rejectedBy.goal:'')));
      }
      d.append(rejected);
     }
     if(x.constraints?.length)d.append(element('small','Later structural constraints: '+x.constraints.map(c=>'line '+c.line+' ('+c.status+')').join(', ')));
     if(x.constraintGroup?.variables.length>1){
      const group=x.constraintGroup;
      if(!shownGroups.has(group.id)){
       shownGroups.add(group.id);
       const details=element('details');
       details.append(element('summary','Joint constraints · '+group.variables.map(v=>v.name).join(', ')+' · '+(group.status==='overflow'?'search incomplete':group.assignments.length+' compatible assignments')));
       for(const assignment of group.assignments.slice(0,8)){
        const item=element('div',undefined,'ruleResult');
        item.append(element('code',assignment.map((key,i)=>{const v=group.variables[i],candidate=v.domain?.find(c=>c.key===key);return v.name+' : '+(candidate?.type||'?')+' := '+(candidate?.term||key);}).join(' · ')));
        const use=element('button','Use this assignment');use.type='button';
        use.onclick=()=>{if(!patchNode||!clean())return;group.variables.forEach((v,i)=>draftChoices.set(v.line,assignment[i]));refreshChoice();};
        item.append(use);details.append(item);
       }
       if(group.assignments.length>8)details.append(element('small','Showing the first 8 assignments. Individual candidate choices can narrow the remaining possibilities.'));
       if(group.variables.some(v=>draftChoices.has(v.line))){
        const clear=element('button','Clear joint choices');clear.type='button';
        clear.onclick=()=>{if(!patchNode||!clean())return;group.variables.forEach(v=>draftChoices.delete(v.line));refreshChoice();};
        details.append(clear);
       }
       d.append(details);
      }
     }
     if(x.dependencies?.length)d.append(element('small','Depends on open obligations: '+x.dependencies.join(', ')));
     for(const c of x.candidates||[]){
      d.append(element('code',(c.type?c.type+' ← ':'')+c.term+' · '+c.schema));
      if(c.requiredCondition)d.append(element('small','After introduction, establish '+c.requiredCondition));
      if(c.evidenceType)d.append(element('small',c.evidenceName+' : '+c.evidenceType));
      if(c.constraints?.length)d.append(element('small','Compatible with the remaining goal at line '+c.constraints.at(-1).line));
      if(c.premiseFacts?.length)d.append(element('small',c.premiseFacts.map(p=>p.type+' ['+p.name+']').join(' · ')));
      const key=c.choice??c.term,selected=choices.get(x.line)===key;
      const b=element('button',selected?'Clear choice':'Use this candidate');b.type='button';
      b.onclick=()=>{
       if(!patchNode||!clean())return;
       refreshChoice(x.line,selected?null:key);
      };
      d.append(b);
     }
     target.append(d);
   }
   if(r.term)target.append(element('pre',r.term));
 }catch(e){target.append(element('p',e.message));}
}
$('compileChain').onclick=()=>{
  if(!patchNode||!clean()||patchNode.kind==='witness')return;
  try{
    const r=parseChainInput($('chainText').value,(patchNode.scope||[]).map(d=>d.name));
    $('patchTerm').value=r.term;$('patchTerm').dispatchEvent(new Event('input'));
    $('chainStatus').textContent=r.steps.length+' steps compiled to a candidate. Check replacement to validate with Lean.';
  }catch(e){$('chainStatus').textContent=e.message;}
};
$('inferChain').onclick=async()=>{
  if(!patchNode||!clean()||patchNode.kind==='witness')return;
  const node=patchNode,revision=rev,query=$('chainText').value,format=$('chainFormat').value,choiceVersion=draftChoiceVersion;
  $('chainBindings').replaceChildren();$('inferChain').disabled=true;
  $('patchTerm').value='';$('patchTerm').dispatchEvent(new Event('input'));
  $('chainStatus').textContent='Inferring intermediate propositions in Lean…';
  try{
    const {steps}=parseChainInput(query,(node.scope||[]).map(d=>d.name));
    const r=await api('chain',{source:lean.value,path:node.path,steps});
    if(revision!==rev||node!==patchNode||query!==$('chainText').value||format!==$('chainFormat').value||choiceVersion!==draftChoiceVersion)return;
    if(r.status!=='inferred')throw Error('Lean did not confirm inference.');
    $('patchTerm').value=r.term;$('patchTerm').dispatchEvent(new Event('input'));
    for(const b of r.bindings){const row=element('div',undefined,'scopeRow');row.append(element('strong',b.name),element('code',b.type));$('chainBindings').append(row);}
    const goal=element('div',undefined,'scopeRow');goal.append(element('strong','Conclusion'),element('code',r.goal));$('chainBindings').append(goal);
    $('chainStatus').textContent='Intermediate propositions inferred by Lean. Check replacement before applying.';
  }catch(e){if(revision===rev&&node===patchNode&&query===$('chainText').value&&format===$('chainFormat').value&&choiceVersion===draftChoiceVersion)$('chainStatus').textContent=e.message;}
  finally{$('inferChain').disabled=false;}
};
function stageWitness(){
  if(!patchNode||$('witnessPair').hidden)return;
  try{
    $('patchTerm').value=witnessTerm($('witnessValue').value,$('witnessEvidence').value);
    $('patchTerm').dispatchEvent(new Event('input'));
    $('patchStatus').textContent='Witness and evidence staged together. Check the entire replacement.';
  }catch(e){
    $('patchTerm').value='';$('patchTerm').dispatchEvent(new Event('input'));$('patchStatus').textContent=e.message;
  }
}
$('buildWitness').onclick=stageWitness;
for(const id of ['witnessValue','witnessEvidence'])$(id).addEventListener('input',stageWitness);
$('cancelPatch').onclick=()=>{patchNode=null;patchCandidate=null;$('typedPatch').hidden=true;};
$('patchTerm').addEventListener('input',()=>{patchCandidate=null;$('applyPatch').disabled=true;$('patchPreview').textContent='';$('patchStatus').textContent='Replacement changed. Check it again.';});
$('checkPatch').onclick=async()=>{
  if(!patchNode||!clean())return;
  const snapshotRev=rev,node=patchNode,term=$('patchTerm').value;
  patchCandidate=null;$('applyPatch').disabled=true;$('checkPatch').disabled=true;$('patchStatus').textContent='Checking local term, rebuilt proof and exported declaration…';
  try{const r=await api('patch',{source:lean.value,path:node.path,replacement:term});
    if(snapshotRev!==rev||patchNode!==node||$('patchTerm').value!==term)return;
    if(r.status!=='checked'||!r.statementDefEq||!r.proofShapePreserved)throw Error('The server did not confirm type preservation.');
    if(r.unchanged){$('patchStatus').textContent='No structural change · original source preserved exactly.';return;}
    patchCandidate=parseLean(r.source);$('patchPreview').textContent=r.source;
    $('patchStatus').textContent='Checked by Lean · same statement type · proof structure preserved after re-elaboration.';
    $('applyPatch').disabled=false;
  }catch(e){if(snapshotRev===rev&&patchNode===node)$('patchStatus').textContent=e.message;}
  finally{$('checkPatch').disabled=false;}
};
$('applyPatch').onclick=()=>{
  if(!patchCandidate||!clean())return;
  if(!confirm('Replace the current source with the checked term-style theorem? Export the original workspace first if you want to retain the tactic layout.'))return;
  install(patchCandidate);setView('reading');notice('Checked typed export applied. The local checker can recheck this revision.');
};
function scheduleTypedReading(){clearTimeout(liveTimer);if($('liveNarrative').checked)liveTimer=setTimeout(()=>{if(local&&clean())typedRequest('structure','reading');},400);}
$('liveNarrative').onchange=scheduleTypedReading;
async function typedRequest(mode,profile='full'){
  if(typedBusy)return;
  if(!clean()){notice('Synchronize first.',true);return;}
  const snapshotRev=rev;typedBusy=true;
  $('extractTerm').disabled=$('informath').disabled=true;
  $('typedStatus').textContent=mode==='structure'?'Elaborating trusted proof locally…':'Running separately installed Informath…';
  try{const source=lean.value;
    const reusable=mode==='structure'&&profile==='reading'&&source===lastTypedSource&&lastTypedTree;
    const r=reusable?{tree:lastTypedTree}:await api(mode,{source,profile});if(snapshotRev!==rev)return;
    if(mode==='structure'){$('typedTree').replaceChildren();patchNode=null;patchCandidate=null;$('typedPatch').hidden=true;$('applyPatch').disabled=true;foldedPaths.clear();typedRoot=r.tree;proofIndex=indexProof(typedRoot);if(!reusable){lastTypedSource=source;lastTypedProfile=profile;lastTypedTree=r.tree;}$('typedNarrative').classList.remove('staleReading');$('typedTree').classList.remove('staleReading');showTypedNarrative();renderTyped(r.tree,$('typedTree'));$('typedStatus').textContent='Extracted from Lean elaboration. Tree is depth-limited; inspect the original proof separately.'+(profile==='reading'?' Live reading: alternative search deferred.':'');}
    else{$('informathOutput').textContent=r.narrative;$('typedStatus').textContent='Informath output · alignment not certified.';}
  }catch(e){if(snapshotRev===rev)$('typedStatus').textContent=e.message;}
  finally{typedBusy=false;$('extractTerm').disabled=$('informath').disabled=false;if(snapshotRev!==rev&&$('liveNarrative').checked)scheduleTypedReading();}
}
$('extractTerm').onclick=()=>typedRequest('structure');$('informath').onclick=()=>typedRequest('informath');
async function ai(mode){if(!clean()){notice('Synchronize first.',true);return;}if(mode==='propose'&&!notes.value.trim()){notice('Enter a mathematical argument first.',true);return;}if(!confirm('Send the current Lean proof and notes to your configured AI provider?'))return;const snapshotRev=rev,snapshotNotes=notesRev;candidate=null;narrative=null;$('accept').disabled=$('useNarrative').disabled=true;$('propose').disabled=$('explain').disabled=true;$('proposal').textContent='Requesting unverified output…';try{const r=await api(mode,{source:lean.value,prose:notes.value});if(snapshotRev!==rev||snapshotNotes!==notesRev)return;if(mode==='explain'){narrative=r.narrative;$('proposal').textContent=narrative;$('useNarrative').disabled=false;notice('AI explanation · unverified.');return;}const next=parseLean(r.source);if(!sameStatement(ir,next))throw Error('Theorem header or environment changed.');candidate=next;$('proposal').textContent=r.source;$('accept').disabled=false;notice('Unverified proposal · review before applying and checking.');}catch(e){if(snapshotRev===rev&&snapshotNotes===notesRev){$('proposal').textContent=e.message;notice('AI unavailable or rejected.',true);}}finally{$('propose').disabled=$('explain').disabled=false;}}
$('propose').onclick=()=>ai('propose');$('explain').onclick=()=>ai('explain');$('accept').onclick=()=>{if(candidate&&clean()&&confirm('Apply the proposed Lean source? Review before running Lean.'))install(candidate);};
$('useNarrative').onclick=()=>{if(narrative)appendNotes('### AI explanation — unverified\n\n'+narrative);};
function theme(t){document.documentElement.dataset.theme=t;$('theme').textContent=t==='dark'?'Light mode':'Dark mode';try{localStorage.setItem(THEME,t);}catch{}}
$('theme').onclick=()=>theme(document.documentElement.dataset.theme==='dark'?'light':'dark');
try{theme(localStorage.getItem(THEME)||'light');}catch{theme('light');}
try{const saved=localStorage.getItem(KEY);if(saved)loadWorkspace(JSON.parse(saved));else{name=EXAMPLES[0].name;install(parseLean(EXAMPLES[0].source));}}catch(e){name=EXAMPLES[0].name;install(parseLean(EXAMPLES[0].source),{save:false});notice('Saved workspace could not be restored: '+e.message+'. Original storage retained until the next edit.',true);}

$('envState').textContent=local?'Local workspace':'Static demo · checker and AI require local server';
ui.refresh();
if(!local){$('collapseProof').disabled=true;$('expandProof').disabled=true;$('narrativeStyle').disabled=true;showStaticNarrative();$('liveNarrative').disabled=true;$('liveInterpret').disabled=true;for(const id of ['check','propose','explain','extractTerm','informath','inferChain','findRules','checkPatch','completeLean']){$(id).disabled=true;$(id).title='Start the local Python server to use this feature.';}$('output').textContent='Browser-only demo. To verify in Lean or use AI, clone the repository and run python server.py.';state('verifyState','Local server required');}
// Same-origin data generated by the Pages build. No user source is sent to a server.
if(!local)fetch(new URL('./demo-proof-trees.json',import.meta.url)).then(async response=>{
  if(!response.ok)return;
  const data=await response.json();
  if(data.schema!==1||!Array.isArray(data.entries)||typeof data.toolchain!=='string')return;
  staticToolchain=data.toolchain;
  for(const entry of data.entries)if(EXAMPLES.some(e=>e.source===entry.source)&&entry.tree&&typeof entry.tree.kind==='string')staticProofs.set(entry.source,entry.tree);
  showStaticNarrative();
}).catch(()=>{/* Authored, explicitly uncertified fallback remains available. */});
document.addEventListener('keydown',e=>{if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='s'){e.preventDefault();persist();notice('Workspace saved locally. Export for a portable backup.');}});
