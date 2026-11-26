import {parseLean,renderLean,renderProse,planSync,sameStatement,EXAMPLES} from './core.mjs';
const $=id=>document.getElementById(id),lean=$('lean'),prose=$('prose');
let ir,base,rev=0,candidate=null,timer;
const clean=()=>lean.value===base.lean&&prose.value===base.prose;
function notice(s,error=false){$('notice').textContent=s;$('notice').classList.toggle('error',error);}
function invalidate(){rev++;candidate=null;$('accept').disabled=true;$('proposal').textContent='No proposal yet.';$('output').textContent='No check for current revision.';}
function dirty(){lean.classList.toggle('dirty',lean.value!==base.lean);prose.classList.toggle('dirty',prose.value!==base.prose);}
function math(target,s){
  if(window.katex&&/^[\p{L}\p{N}_\s=→∧∨¬↔∀∃()+*\-]+$/u.test(s)){
    const tex=s.replace(/_/g,'\\_').replace(/→/g,'\\to ').replace(/∧/g,'\\land ').replace(/∨/g,'\\lor ').replace(/¬/g,'\\neg ').replace(/↔/g,'\\leftrightarrow ').replace(/∀/g,'\\forall ').replace(/∃/g,'\\exists ');
    try{window.katex.render(tex,target,{trust:false,throwOnError:true});return;}catch{}
  }target.textContent=s;
}
function reading(){
 const box=$('reading');box.replaceChildren();const h=document.createElement('div');h.className='statement';h.textContent=ir.header;box.append(h);
 for(const n of ir.nodes){if(n.kind==='blank')continue;const b=document.createElement('button');b.className='step';b.style.paddingLeft=Math.min(n.indent-2,40)*8+'px';b.append(document.createTextNode(n.leanLine+' · '+n.label+' '));if(n.argument!==null){const span=document.createElement('span');math(span,n.argument);b.append(span);}b.onclick=()=>{if(!clean()){notice('Synchronize edits before navigating.',true);return;}const lines=lean.value.split('\n'),start=lines.slice(0,n.leanLine-1).join('\n').length+n.leanLine-1;lean.focus();lean.setSelectionRange(start,start+lines[n.leanLine-1].length);};box.append(b);}
}
function install(next){clearTimeout(timer);ir=next;lean.value=renderLean(ir);prose.value=renderProse(ir);base={lean:lean.value,prose:prose.value};invalidate();dirty();reading();notice('Synchronized · syntax only, not verified.');}
function sync(side){clearTimeout(timer);try{install(planSync(base,lean.value,prose.value,side).ir);}catch(e){notice(e.message,true);}}
for(const [el,side] of [[lean,'lean'],[prose,'prose']])el.addEventListener('input',()=>{clearTimeout(timer);invalidate();dirty();notice('Unsynchronized edits.');if($('auto').checked)timer=setTimeout(()=>sync(side),400);});
$('fromLean').onclick=()=>sync('lean');$('fromProse').onclick=()=>sync('prose');
for(const [id,el,key] of [['revertLean',lean,'lean'],['revertProse',prose,'prose']])$(id).onclick=()=>{clearTimeout(timer);if(el.value!==base[key]&&!confirm('Discard edits on this side?'))return;el.value=base[key];invalidate();dirty();notice('Reverted this side to the last synchronized version.');};
EXAMPLES.forEach((e,i)=>$('example').add(new Option(e.name,i)));
$('example').onchange=()=>{if(!clean()&&!confirm('Discard unsynchronized edits?'))return;install(parseLean(EXAMPLES[+$('example').value].source));};
$('open').onclick=()=>$('file').click();
$('file').onchange=async()=>{try{const f=$('file').files[0];if(!f)return;if(!clean()&&!confirm('Discard unsynchronized edits?'))return;if(f.size>128*1024)throw Error('File exceeds 128 KiB.');install(parseLean((await f.text()).replace(/\r\n/g,'\n')));}catch(e){notice(e.message,true);}finally{$('file').value='';}};
async function api(path,payload){const r=await fetch(path,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});const d=await r.json();if(!r.ok)throw Error(d.error||'Request failed');return d;}
$('check').onclick=async()=>{if(!clean()){notice('Synchronize first.',true);return;}const snapshot=rev;$('check').disabled=true;$('output').textContent='Running Lean…';try{const r=await api('/api/check',{source:lean.value});if(snapshot!==rev)return;$('output').textContent=r.output;notice('Lean check: '+r.status,r.status!=='passed');}catch(e){if(snapshot===rev)notice('Checker unavailable: '+e.message,true);}finally{$('check').disabled=false;}};
$('download').onclick=()=>{const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([lean.value],{type:'text/plain'}));a.download='proof.lean';a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);};
async function ai(mode){if(!clean()){notice('Synchronize first.',true);return;}if(mode==='propose'&&!$('prompt').value.trim()){notice('Enter a free-form proof.',true);return;}if(!confirm('Send current proof to the configured AI endpoint?'))return;const snapshot=rev;candidate=null;$('accept').disabled=true;$('propose').disabled=$('explain').disabled=true;$('proposal').textContent='Requesting unverified AI output…';try{const r=await api('/api/'+mode,{source:lean.value,prose:$('prompt').value});if(snapshot!==rev)return;if(mode==='explain'){$('proposal').textContent=r.narrative;notice('AI explanation · unverified, not synchronized.');return;}const next=parseLean(r.source);if(!sameStatement(ir,next))throw Error('Theorem header or environment changed.');candidate=next;$('proposal').textContent=r.source;$('accept').disabled=false;notice('Unverified proposal · review before applying and checking.');}catch(e){if(snapshot===rev){$('proposal').textContent=e.message;notice('AI unavailable or rejected.',true);}}finally{$('propose').disabled=$('explain').disabled=false;}}
$('propose').onclick=()=>ai('propose');$('explain').onclick=()=>ai('explain');$('accept').onclick=()=>{if(candidate&&clean())install(candidate);};
window.addEventListener('load',reading);install(parseLean(EXAMPLES[0].source));
