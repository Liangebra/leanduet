"""Real browser regression checks. Run after installing playwright + Chromium."""
import os
import subprocess
import sys
import time
import urllib.request
from pathlib import Path
from playwright.sync_api import sync_playwright, expect

ROOT=Path(__file__).resolve().parents[1]
port=18765
url=f"http://127.0.0.1:{port}"
with subprocess.Popen([sys.executable,"server.py","--port",str(port)],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL) as server:
    try:
        for _ in range(100):
            try:
                urllib.request.urlopen(url,timeout=.5).close()
                break
            except OSError:
                time.sleep(.1)
        else:
            raise RuntimeError("Local server did not start")
        with sync_playwright() as p:
            browser=p.chromium.launch()
            page=browser.new_page(viewport={"width":1440,"height":900})
            errors=[]
            page.on("pageerror",lambda error:errors.append(str(error)))
            page.goto(url)
            expect(page.locator("#theoremName")).to_have_text("compose imp")
            expect(page.locator("#narrativeStatus")).to_contain_text("Authored example")
            expect(page.locator("#statement math")).to_have_count(3)
            page.locator("#reading .step").last.click()
            expect(page.locator("#inspectCode")).to_have_text("exact hqr hq")
            page.locator("#editStep").click()
            page.locator("#stepInput").fill("Conclude using hqr (hpq hp)")
            page.locator("#applyStep").click()
            expect(page.locator("#lean")).to_have_value(__import__("re").compile(r"exact hqr \(hpq hp\)"))
            expect(page.locator("#narrativeStatus")).to_contain_text("Structural view")
            page.reload()
            expect(page.locator("#lean")).to_have_value(__import__("re").compile(r"exact hqr \(hpq hp\)"))
            page.locator("#focusMode").click()
            expect(page.locator(".codepane")).to_be_hidden()
            page.locator("#focusMode").click()
            expect(page.locator(".codepane")).to_be_visible()
            page.locator("#check").click()
            expect(page.locator("#verifyState")).to_have_text("Lean passed",timeout=60000)
            page.locator('[data-view="typed"]').click()
            page.locator("#extractTerm").click()
            expect(page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            expect(page.locator("#typedNarrative")).to_contain_text("Apply hqr")
            page.locator("#collapseProof").click()
            expect(page.locator("#typedNarrative")).to_contain_text("hidden steps")
            expect(page.locator("#typedNarrative")).not_to_contain_text("Apply hpq")
            page.locator("#expandProof").click()
            expect(page.locator("#typedNarrative")).to_contain_text("Apply hpq")
            page.locator("#typedLanguage").select_option("zh")
            expect(page.locator("#typedNarrative")).to_contain_text("应用")
            page.locator('[data-view="reading"]').click()
            page.locator("#lean").fill(page.locator("#lean").input_value()+"  rfl\n")
            page.locator('[data-view="prose"]').click()
            page.locator("#prose").fill(page.locator("#prose").input_value()+"draft")
            page.locator("#fromProse").click()
            expect(page.locator("#notice")).to_contain_text("Both sides changed")
            page.reload()
            expect(page.locator("#leanDirty")).to_have_text("Edited")
            expect(page.locator("#proseDirty")).to_have_text("Edited")
            page.locator("#theme").click()
            expect(page.locator("html")).to_have_attribute("data-theme","dark")
            page.reload()
            expect(page.locator("html")).to_have_attribute("data-theme","dark")
            page.set_viewport_size({"width":390,"height":844})
            assert page.evaluate("document.documentElement.scrollWidth <= window.innerWidth + 1"), page.evaluate("Array.from(document.querySelectorAll(\'body *\')).filter(x=>x.getBoundingClientRect().right>innerWidth+1&&x.getBoundingClientRect().width>0).map(x=>[x.tagName,x.id,x.className?.toString(),Math.round(x.getBoundingClientRect().right)]).slice(0,20)")
            page.screenshot(path=str(ROOT/"browser-smoke.png"),full_page=True)
            patch_page=browser.new_page(viewport={"width":1440,"height":900})
            patch_page.on("pageerror",lambda error:errors.append(str(error)))
            patch_page.goto(url)
            source="""theorem patch_example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hq : Q) : P → R := by
  intro hp
  exact hqr (hpq hp)
"""
            patch_page.locator("#lean").fill(source)
            patch_page.once("dialog",lambda d:d.accept())
            patch_page.locator("#adopt").click()
            patch_page.locator('[data-view="typed"]').click()
            patch_page.locator("#extractTerm").click()
            expect(patch_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            # Open all nested proof nodes to reach the hpq application.
            patch_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            patch_page.locator(".typedNode").filter(has=patch_page.locator("summary").filter(has_text=__import__("re").compile("^Apply hpq$"))).last.locator(":scope > .typedEdit").click()
            expect(patch_page.locator("#patchScope")).to_contain_text("hq")
            patch_page.get_by_role("button",name="Use hypothesis hq").click()
            expect(patch_page.locator("#patchTerm")).to_have_value("hq")
            patch_page.locator("#checkPatch").click()
            expect(patch_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            expect(patch_page.locator("#patchPreview")).to_contain_text("hqr hq")
            patch_page.once("dialog",lambda d:d.accept())
            patch_page.locator("#applyPatch").click()
            expect(patch_page.locator("#lean")).to_have_value(__import__("re").compile(r"hqr hq"))
            patch_page.locator("#check").click()
            expect(patch_page.locator("#verifyState")).to_have_text("Lean passed",timeout=60000)
            pair_source="""theorem witness_pair : ∃ n : Nat, n = n := by
  exact ⟨0, rfl⟩
"""
            patch_page.locator("#lean").fill(pair_source)
            patch_page.once("dialog",lambda d:d.accept())
            patch_page.locator("#adopt").click()
            patch_page.locator('[data-view="typed"]').click()
            patch_page.locator("#extractTerm").click()
            expect(patch_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            patch_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            patch_page.locator(".typedNode").filter(has=patch_page.locator("summary").filter(has_text=__import__("re").compile("^Apply Exists.intro$"))).last.locator(":scope > .typedEdit").click()
            expect(patch_page.locator("#witnessPair")).to_be_visible()
            patch_page.locator("#witnessValue").fill("1")
            patch_page.locator("#witnessEvidence").fill("rfl")
            expect(patch_page.locator("#patchTerm")).to_have_value("Exists.intro (1) (rfl)")
            patch_page.locator("#checkPatch").click()
            expect(patch_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            patch_page.once("dialog",lambda d:d.accept())
            patch_page.locator("#applyPatch").click()
            patch_page.locator("#check").click()
            expect(patch_page.locator("#verifyState")).to_have_text("Lean passed",timeout=60000)
            rule_source="""theorem reversed (a b : Nat) (h : a = b) : b = a := by
  exact Eq.symm h
"""
            patch_page.locator("#lean").fill(rule_source)
            patch_page.once("dialog",lambda d:d.accept())
            patch_page.locator("#adopt").click()
            patch_page.locator('[data-view="typed"]').click()
            patch_page.locator("#extractTerm").click()
            expect(patch_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            patch_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            patch_page.locator(".typedNode").filter(has=patch_page.locator("summary").filter(has_text=__import__("re").compile("^Apply Eq.symm$"))).last.locator(":scope > .typedEdit").click()
            patch_page.locator("#ruleIntent").fill("由等式对称性，使用 h")
            patch_page.locator("#findRules").click()
            expect(patch_page.locator("#ruleResults")).to_contain_text("Eq.symm",timeout=60000)
            patch_page.locator("#ruleResults").get_by_role("button",name="Use this proof").first.click()
            patch_page.locator("#checkPatch").click()
            expect(patch_page.locator("#patchStatus")).to_contain_text("No structural change",timeout=120000)
            chain_source="""theorem chain_demo (P Q R : Prop) (f : P → Q) (g : Q → R) (p : P) : R := by
  exact g (f p)
"""
            patch_page.locator("#lean").fill(chain_source)
            patch_page.once("dialog",lambda d:d.accept())
            patch_page.locator("#adopt").click()
            patch_page.locator('[data-view="typed"]').click()
            patch_page.locator("#extractTerm").click()
            expect(patch_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            patch_page.locator("#typedLanguage").select_option("ja")
            expect(patch_page.locator("#typedNarrative")).to_contain_text("適用する g")
            patch_page.locator("#typedNarrative .derivedStep").filter(has_text="適用する g").get_by_role("button",name="この推論を編集").click()
            patch_page.locator("#chainEditor summary").click()
            patch_page.locator("#chainFormat").select_option("natural")
            patch_page.locator("#chainText").fill("建立 hq : $Q$，由 f，使用 p\n因此 $R$，由 g，使用 hq")
            expect(patch_page.locator("#draftTranslation")).to_contain_text("have hq : Q := f p")
            expect(patch_page.locator("#draftTranslation")).to_contain_text("exact g hq")
            patch_page.locator("#compileChain").click()
            expect(patch_page.locator("#patchTerm")).to_have_value("by\n  have hq : Q := f p\n  show R\n  exact g hq")
            original_draft="建立 hq : $Q$\n$R$"
            patch_page.locator("#chainText").fill(original_draft)
            rows=patch_page.locator("#draftTranslation .ruleResult")
            rows.nth(0).get_by_role("button",name="Use this candidate").first.click()
            rows.nth(1).get_by_role("button",name="Use this candidate").first.click()
            expect(patch_page.locator("#chainText")).to_have_value(original_draft)
            assert rows.nth(0).get_attribute("data-resolution-status")=="candidate-unverified"
            expect(rows.nth(0)).to_contain_text("Candidate generated · Lean not checke…34073 tokens truncated…=='structure'&&profile==='reading'&&source===lastTypedSource&&lastTypedTree;
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