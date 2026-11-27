Warning: truncated output (original token count: 17091)
Total output lines: 727

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
notes.addEventListener('input',()=>{notesRev++;candidate=null;narrative=null;$('accept').disabled=true;$('useNarrative').disabled=true;$('proposal').te…11091 tokens truncated…key,i)=>{const v=group.variables[i],candidate=v.domain?.find(c=>c.key===key);return v.name+' : '+(candidate?.type||'?')+' := '+(candidate?.term||key);}).join(' · ')));
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
      if(c.premiseFacts?.length)d.append(element('small',c.premiseFacts.map(p=>p.type+' ['+p.name+']').join(' · ')));
      const key=c.choice??c.term,selected=draftChoices.get(x.line)===key;
      const b=element('button',selected?'Clear choice':'Use this candidate');b.type='button';
      b.onclick=()=>{
       if(!patchNode||!clean())return;
       if(selected)draftChoices.delete(x.line);else draftChoices.set(x.line,key);
       refreshChoice();
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
