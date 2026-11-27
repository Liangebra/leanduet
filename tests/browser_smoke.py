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

def select_typed_edit(page, *, exact_type=None, includes=(), summary=None, term=None):
    page.locator("#typedTree").evaluate("""(root, query) => {
      const rows=[...root.querySelectorAll('.typedNode')].map(node=>({
        node,
        type:node.querySelector(':scope > .typedType code')?.textContent.trim()||'',
        summary:node.querySelector(':scope > summary')?.textContent.trim()||'',
        term:node.querySelector(':scope > details pre')?.textContent.trim()||''
      }));
      let candidates=rows.filter(row=>(query.exactType===null||row.type===query.exactType)
        &&query.includes.every(part=>row.type.includes(part))
        &&(query.summary===null||row.summary===query.summary)
        &&(query.term===null||row.term===query.term)
        &&row.node.querySelector(':scope > .typedEdit'));
      if(!candidates.length) throw new Error('Could not locate the requested typed proof node.');
      const shortest=Math.min(...candidates.map(row=>row.type.length));
      candidates=candidates.filter(row=>row.type.length===shortest);
      if(candidates.length!==1) throw new Error('The requested typed proof node is ambiguous.');
      const target=candidates[0].node;
      for(let current=target;current&&current!==root;current=current.parentElement)
        if(current.tagName==='DETAILS') current.open=true;
      target.querySelector(':scope > .typedEdit').click();
    }""", {"exactType":exact_type,"includes":list(includes),"summary":summary,"term":term})

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
            expect(rows.nth(0)).to_contain_text("Candidate generated · Lean not checked")
            patch_page.locator("#compileChain").click()
            expect(patch_page.locator("#patchTerm")).to_have_value("by\n  have hq : Q := f p\n  show R\n  exact g hq")
            patch_page.locator("#chainText").fill(original_draft+"\n")
            expect(patch_page.locator("#patchTerm")).to_have_value("")
            expect(patch_page.locator("#draftTranslation")).to_contain_text("Clear choice")
            patch_page.locator("#chainText").fill("建立 hq : $Q$\n$P$")
            expect(patch_page.locator("#draftTranslation .ruleResult").nth(1)).not_to_contain_text("Clear choice")
            patch_page.locator("#chainFormat").select_option("controlled")
            patch_page.locator("#chainText").fill("建立 hq | f using p\n结论 | g using hq")
            patch_page.locator("#inferChain").click()
            expect(patch_page.locator("#chainBindings")).to_contain_text("Q",timeout=60000)
            expect(patch_page.locator("#patchTerm")).to_have_value("by\n  have hq := f p\n  exact g hq")
            patch_page.locator("#checkPatch").click()
            expect(patch_page.locator("#patchStatus")).to_contain_text(__import__("re").compile("Checked by Lean|No structural change"),timeout=120000)
            case_page=browser.new_page(viewport={"width":1440,"height":900})
            case_page.on("pageerror",lambda error:errors.append(str(error)))
            case_page.goto(url)
            case_source="""theorem interleaved_demo (h : True ∨ True) (j : True ∨ True) (p : True)
    (f g k l m : True → True) : True := by
  exact Or.elim h (fun hp => g hp) (fun hq => k hq)
"""
            case_page.locator("#lean").fill(case_source)
            case_page.once("dialog",lambda d:d.accept())
            case_page.locator("#adopt").click()
            case_page.locator('[data-view="typed"]').click()
            case_page.locator("#extractTerm").click()
            expect(case_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            case_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            case_node=case_page.locator("#typedTree summary").filter(has_text=__import__("re").compile("^Apply Or\\.elim$")).last.locator("xpath=..")
            case_node.locator(":scope > button.typedEdit").click()
            case_page.locator("#chainEditor summary").click()
            case_page.locator("#chainFormat").select_option("natural")
            case_text="establish hr : $True$ | f p\n分情况讨论 h，建立 hT : $True$\n  左支 hp\n    $True$ | g hp\n  右支 hq\n    $True$ | k hq\nestablish ht : $True$ | hT\ncases j, establish jT : $True$\n  left case hu\n    $True$ | l hu\n  right case hv\n    $True$ | m hv\n$True$ | jT"
            partial_case_text="分情况讨论 h，建立 hT : $True$\n  左支 hp\n    unsupported ⊛\n  右支 hq\n    $True$ | k hq\nestablish ht : $True$ | hT\ncases j, establish jT : $True$\n  left case hu\n    $True$ | l hu\n  right case hv\n    $True$ | m hv\n$True$ | jT"
            case_page.locator("#chainText").fill(partial_case_text)
            expect(case_page.locator("#draftTranslation")).to_contain_text("inl hp : True ⊢ True · open")
            expect(case_page.locator("#draftTranslation")).to_contain_text("cases j")
            expect(case_page.locator("#draftTranslation")).to_contain_text("Line 6 · translated · depends-on-open")
            assert case_page.locator("#patchTerm").input_value()=="", "an open branch must not stage a Lean candidate"
            case_page.locator("#chainText").fill(case_text)
            expect(case_page.locator("#draftTranslation")).to_contain_text("cases h into inl hp: True / inr hq: True")
            case_page.locator("#inferChain").click()
            expect(case_page.locator("#chainBindings")).to_contain_text("hT",timeout=120000)
            expect(case_page.locator("#chainBindings")).not_to_contain_text("hp")
            expect(case_page.locator("#chainBindings")).not_to_contain_text("hq")
            assert "cases h with" in case_page.locator("#patchTerm").input_value()
            assert "cases j with" in case_page.locator("#patchTerm").input_value()
            case_page.locator("#checkPatch").click()
            expect(case_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            case_page.once("dialog",lambda d:d.accept())
            case_page.locator("#applyPatch").click()
            case_page.locator("#check").click()
            expect(case_page.locator("#verifyState")).to_have_text("Lean passed",timeout=120000)
            # The browser's controlled editor deliberately accepts one theorem
            # plus imports. Keep this UI fixture within that supported source
            # shape; the set-intersection-specific Lean prelude is compiled in
            # tests/interpret_integration.py instead.
            set_source="""theorem predicate_intersection_left {α : Type} (A B : α → Prop) :
    ∀ x : α, A x ∧ B x → A x := by
  intro x
  intro hx
  exact And.left hx
"""
            case_page.locator("#lean").fill(set_source)
            case_page.once("dialog",lambda d:d.accept())
            case_page.locator("#adopt").click()
            case_page.locator('[data-view="typed"]').click()
            case_page.locator("#extractTerm").click()
            expect(case_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            case_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            set_projection=case_page.locator(".typedNode").filter(has=case_page.locator("summary").filter(has_text=__import__("re").compile("^Apply And\\.left$"))).last
            set_projection.locator(":scope > .typedEdit").click()
            case_page.locator("#chainEditor summary").click()
            case_page.locator("#chainFormat").select_option("natural")
            case_page.locator("#chainText").fill("因此 $A(x)$，由 And.left，使用 hx")
            case_page.locator("#inferChain").click()
            expect(case_page.locator("#draftTranslation")).to_contain_text("exact And.left hx")
            case_page.locator("#compileChain").click()
            expect(case_page.locator("#patchTerm")).to_have_value(__import__("re").compile(r"exact And\.left hx"))
            case_page.locator("#checkPatch").click()
            expect(case_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            case_page.close()
            operation_page=browser.new_page(viewport={"width":1440,"height":900})
            operation_page.on("pageerror",lambda error:errors.append(str(error)))
            operation_page.goto(url)
            operation_source="""theorem operation_choice_demo (P : Nat → Prop) (hall : ∀ x : Nat, P x)
    (he : ∃ y : Nat, P y) (h : True ∨ True) : ∀ x : Nat, P x := by
  exact hall
"""
            operation_page.locator("#lean").fill(operation_source)
            operation_page.once("dialog",lambda d:d.accept())
            operation_page.locator("#adopt").click()
            operation_page.locator('[data-view="typed"]').click()
            operation_page.locator("#extractTerm").click()
            expect(operation_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            select_typed_edit(operation_page,includes=("∀","P x"),summary="Use hypothesis",term="hall")
            expect(operation_page.locator("#patchTarget")).to_contain_text("∀")
            operation_page.locator("#chainEditor summary").click()
            operation_page.locator("#chainFormat").select_option("natural")
            operation_text="""take an element x : $Nat$ satisfying $P(x)$"""
            operation_page.locator("#chainText").fill(operation_text)
            operation_row=operation_page.locator("#draftTranslation .ruleResult").first
            expect(operation_row).to_contain_text("universal-variable introduction")
            expect(operation_row).to_contain_text("existential witness extraction")
            operation_row.get_by_role("button",name="Use this candidate").first.click()
            expect(operation_row).to_contain_text("Clear choice")
            operation_text += """
cases h, establish hp : $P(x)$
  left case hleft
    $P(x)$ | hall x
  right case hright
    $P(x)$ | hall x
$P(x)$ | hp"""
            operation_page.locator("#chainText").fill(operation_text)
            operation_row=operation_page.locator("#draftTranslation .ruleResult").first
            expect(operation_row).to_contain_text("universal-variable introduction")
            expect(operation_row).to_contain_text("Clear choice")
            operation_page.locator("#compileChain").click()
            expect(operation_page.locator("#patchTerm")).to_have_value(__import__("re").compile(r"intro x[\s\S]*cases h with[\s\S]*exact hall x[\s\S]*exact hp"))
            operation_page.locator("#checkPatch").click()
            expect(operation_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            operation_page.once("dialog",lambda d:d.accept())
            operation_page.locator("#applyPatch").click()
            operation_page.locator("#check").click()
            expect(operation_page.locator("#verifyState")).to_have_text("Lean passed",timeout=120000)
            operation_page.close()
            lemma_page=browser.new_page(viewport={"width":1440,"height":900})
            lemma_page.on("pageerror",lambda error:errors.append(str(error)))
            lemma_page.goto(url)
            lemma_page.locator("#lean").fill("""theorem local_lemma_demo (Q R : Prop) (hq : Q) (gr : Q → R) : R := by
  have localQ : Q := hq
  exact gr localQ
""")
            lemma_page.once("dialog",lambda d:d.accept())
            lemma_page.locator("#adopt").click()
            lemma_page.locator('[data-view="typed"]').click()
            lemma_page.locator("#extractTerm").click()
            expect(lemma_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            select_typed_edit(lemma_page,exact_type="R",summary="Establish local binding localQ")
            expect(lemma_page.locator("#patchTarget")).to_contain_text("R")
            lemma_page.locator("#chainEditor summary").click()
            lemma_page.locator("#chainFormat").select_option("natural")
            lemma_text="""local lemma localQ : $Q$
  proof
    $Q$ | hq
$R$ | gr localQ"""
            lemma_page.locator("#chainText").fill(lemma_text)
            lemma_row=lemma_page.locator("#draftTranslation .ruleResult").first
            expect(lemma_row).to_contain_text("local lemma")
            lemma_page.locator("#inferChain").click()
            expect(lemma_page.locator("#chainStatus")).to_contain_text("Intermediate propositions inferred by Lean",timeout=120000)
            expect(lemma_page.locator("#patchTerm")).to_have_value(__import__("re").compile(r"have localQ : Q := by[\s\S]*exact hq[\s\S]*exact gr localQ"))
            lemma_page.locator("#checkPatch").click()
            expect(lemma_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            lemma_page.once("dialog",lambda d:d.accept())
            lemma_page.locator("#applyPatch").click()
            lemma_page.locator("#check").click()
            expect(lemma_page.locator("#verifyState")).to_have_text("Lean passed",timeout=120000)
            lemma_page.close()
            restricted_page=browser.new_page(viewport={"width":1440,"height":900})
            restricted_page.on("pageerror",lambda error:errors.append(str(error)))
            restricted_page.goto(url)
            restricted_page.locator("#lean").fill("""theorem restricted_forall_demo (A : List Nat) (P : Nat → Prop)
    (hall : ∀ x : Nat, x ∈ A → P x) : ∀ x ∈ A, P x := by
  exact fun x hx => hall x hx
""")
            restricted_page.once("dialog",lambda d:d.accept())
            restricted_page.locator("#adopt").click()
            restricted_page.locator('[data-view="typed"]').click()
            restricted_page.locator("#extractTerm").click()
            expect(restricted_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            select_typed_edit(restricted_page,includes=("∀","x ∈ A","P x"),summary="Introduce x")
            expect(restricted_page.locator("#patchTarget")).to_contain_text("∀")
            if not restricted_page.locator("#chainEditor").evaluate("(editor) => editor.open"):
                restricted_page.locator("#chainEditor summary").click()
            restricted_page.locator("#chainFormat").select_option("natural")
            restricted_page.locator("#chainText").fill("take an arbitrary element x : $Nat$ in A satisfying $P(x)$\nassume hx : $x ∈ A$\n$P(x)$ | hall x hx")
            bounded_row=restricted_page.locator("#draftTranslation .ruleResult").first
            expect(bounded_row).to_contain_text("arbitrary element introduction under a set restriction")
            expect(bounded_row).to_contain_text("After introduction, establish (x ∈ A)")
            restricted_page.locator("#compileChain").click()
            expect(restricted_page.locator("#patchTerm")).to_have_value(__import__("re").compile(r"intro x[\s\S]*intro hx[\s\S]*exact hall x hx"))
            restricted_page.locator("#checkPatch").click()
            expect(restricted_page.locator("#applyPatch")).to_be_enabled(timeout=120000)

            restricted_page.locator("#lean").fill("""theorem restricted_exists_demo (A : List Nat) (P : Nat → Prop)
    (h : ∃ x ∈ A, P x) (hq : True) : True := by
  exact hq
""")
            restricted_page.once("dialog",lambda d:d.accept())
            restricted_page.locator("#adopt").click()
            restricted_page.locator('[data-view="typed"]').click()
            restricted_page.locator("#extractTerm").click()
            expect(restricted_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            select_typed_edit(restricted_page,exact_type="True",summary="Use hypothesis",term="hq")
            expect(restricted_page.locator("#patchTarget")).to_contain_text("True")
            if not restricted_page.locator("#chainEditor").evaluate("(editor) => editor.open"):
                restricted_page.locator("#chainEditor summary").click()
            restricted_page.locator("#chainFormat").select_option("natural")
            restricted_page.locator("#chainText").fill("take an element x : $Nat$ in A satisfying $P(x)$ from h\n$True$ | hq")
            bounded_witness=restricted_page.locator("#draftTranslation .ruleResult").first
            expect(bounded_witness).to_contain_text("restricted existential witness extraction")
            expect(bounded_witness).to_contain_text("h_x : ((x ∈ A) ∧ (P x))")
            restricted_page.locator("#compileChain").click()
            expect(restricted_page.locator("#patchTerm")).to_have_value(__import__("re").compile(r"rcases duet_exists_x with ⟨x, h_x⟩[\s\S]*exact hq"))
            restricted_page.locator("#checkPatch").click()
            expect(restricted_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            restricted_page.close()
            exploration_source=patch_page.locator("#lean").input_value()
            patch_page.locator("#noteGoal").click()
            assert "Goal snapshot" in patch_page.locator("#prompt").input_value()
            patch_page.locator("#prompt").fill("A trial: $R$")
            patch_page.locator("#prompt").evaluate("(e)=>{e.focus();e.setSelectionRange(9,12);e.dispatchEvent(new Event('select'));}")
            patch_page.locator("#stageFormula").click()
            expect(patch_page.locator("#formulaGoal")).to_have_value("$R$")
            expect(patch_page.locator("#lean")).to_have_value(exploration_source)
            patch_page.locator("#irInspector summary").click()
            patch_page.locator("#inspectIR").click()
            expect(patch_page.locator("#irStatus")).to_contain_text("formula matches goal",timeout=60000)
            expect(patch_page.locator("#irOutput")).to_contain_text("leanduet.kernel-judgment")
            expect(patch_page.locator("#irStatus")).to_contain_text("Lean round trip checked")
            patch_page.locator("#formulaGoal").fill("$P$")
            patch_page.locator("#inspectIR").click()
            expect(patch_page.locator("#irStatus")).to_contain_text("formula does not match goal",timeout=60000)
            patch_page.locator("#irInspector summary").click()
            patch_page.locator("#abstractPanel summary").click()
            patch_page.locator("#abstractProof").click()
            expect(patch_page.locator("#abstractStatus")).to_contain_text("Standalone theorem compiled",timeout=120000)
            expect(patch_page.locator("#abstractOutput")).to_contain_text("theorem LeanDuetExtractedLemma")
            expect(patch_page.locator("#lean")).to_have_value(chain_source)
            patch_page.locator("#abstractPanel summary").click()
            patch_page.locator("#chainFormat").select_option("formula")
            patch_page.locator("#chainText").fill("$Q$\n$R$")
            patch_page.locator("#inferChain").click()
            expect(patch_page.locator("#chainBindings")).to_contain_text("duet_h1",timeout=60000)
            expect(patch_page.locator("#patchTerm")).to_have_value("by\n  have duet_h1 : Q := by exact?\n  show R\n  exact?")
            patch_page.locator("#chainFormat").select_option("controlled")
            patch_page.locator("#chainText").fill("结论 | g using missing")
            expect(patch_page.locator("#applyPatch")).to_be_disabled()
            patch_page.locator("#compileChain").click()
            expect(patch_page.locator("#chainStatus")).to_contain_text("unknown, ambiguous or forward reference")
            patch_page.close()
            live_page=browser.new_page(viewport={"width":1440,"height":900})
            live_page.on("pageerror",lambda error:errors.append(str(error)))
            live_page.goto(url)
            live_source="""theorem live_duet (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
            live_page.locator("#lean").fill(live_source)
            live_page.once("dialog",lambda d:d.accept())
            live_page.locator("#adopt").click()
            live_page.locator('[data-view="typed"]').click()
            live_page.locator("#typedLanguage").select_option("en")
            live_page.locator("#liveNarrative").check()
            expect(live_page.locator("#typedNarrative")).to_contain_text("Use h1",timeout=60000)
            live_page.locator("#typedNarrative .derivedStep").filter(has_text="Use h1").get_by_role("button",name="Edit this inference").click()
            live_page.locator("#wordingInput").fill("From our original observation,")
            expect(live_page.locator("#typedNarrative")).to_contain_text("From our original observation,")
            live_page.locator("#interpretPanel > summary").click()
            live_page.locator("#interpretText").fill("Therefore, $P$ | h2\n$False$ | h1\nunsupported ⊛")
            expect(live_page.locator("#interpretResults")).to_contain_text("Unresolved")
            live_page.locator("#interpretRun").click()
            expect(live_page.locator("#interpretStatus")).to_contain_text("1 locally checked candidate",timeout=60000)
            expect(live_page.locator("#interpretResults")).to_contain_text("rejected")
            live_page.locator("#interpretResults").get_by_role("button",name="Use candidate").click()
            expect(live_page.locator("#patchTerm")).to_have_value("h2")
            expect(live_page.locator("#lean")).to_have_value(live_source)
            live_page.locator("#auto").check()
            live_page.locator("#lean").fill(live_source.replace("exact h1","exact h2"))
            expect(live_page.locator("#typedNarrative")).to_contain_text("Use h2",timeout=60000)
            expect(live_page.locator("#typedNarrative")).to_contain_text("1 detached author annotation")
            expect(live_page.locator("#typedNarrative .authorWording")).to_have_count(0)
            live_page.close()
            about=browser.new_page(viewport={"width":390,"height":844})
            about.on("pageerror",lambda error:errors.append(str(error)))
            about.goto(url+"/about.html#zh")
            expect(about.locator("html")).to_have_attribute("lang","zh-CN")
            expect(about.locator("article#zh")).to_be_visible()
            expect(about.locator("article#en")).to_be_hidden()
            about.get_by_role("link",name="日本語").click()
            expect(about.locator("html")).to_have_attribute("lang","ja")
            expect(about.locator("article#ja")).to_be_visible()
            expect(about.locator("article#zh")).to_be_hidden()
            assert about.evaluate("document.documentElement.scrollWidth <= window.innerWidth + 1"),"about mobile overflow"
            about.close()
            subgoal_page=browser.new_page(viewport={"width":1440,"height":900})
            subgoal_page.on("pageerror",lambda error:errors.append(str(error)))
            subgoal_page.goto(url)
            pair_source="""theorem conjunction_demo (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact And.intro hp hq
"""
            subgoal_page.locator("#lean").fill(pair_source)
            subgoal_page.once("dialog",lambda d:d.accept())
            subgoal_page.locator("#adopt").click()
            subgoal_page.locator('[data-view="typed"]').click()
            subgoal_page.locator("#extractTerm").click()
            expect(subgoal_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            subgoal_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            pair_node=subgoal_page.locator(".typedNode").filter(has=subgoal_page.locator("summary").filter(has_text=__import__("re").compile("^Apply And\\.intro$"))).last
            pair_node.locator(":scope > button.typedEdit").click()
            subgoal_page.locator("#chainEditor summary").click()
            subgoal_page.locator("#chainFormat").select_option("natural")
            subgoal_page.locator("#chainText").fill("split conjunction\n  first goal\n    $P$ | hp\n  second goal\n    $Q$ | hq")
            expect(subgoal_page.locator("#draftTranslation")).to_contain_text("split conjunction into first: P and second: Q")
            expect(subgoal_page.locator("#draftTranslation")).to_contain_text("first · P · complete")
            expect(subgoal_page.locator("#draftTranslation")).to_contain_text("second · Q · complete")
            subgoal_page.locator("#compileChain").click()
            expect(subgoal_page.locator("#patchTerm")).to_have_value("by\n  constructor\n  ·\n    show P\n    exact hp\n  ·\n    show Q\n    exact hq")
            subgoal_page.locator("#checkPatch").click()
            expect(subgoal_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            subgoal_page.once("dialog",lambda d:d.accept())
            subgoal_page.locator("#applyPatch").click()
            subgoal_page.locator("#check").click()
            expect(subgoal_page.locator("#verifyState")).to_have_text("Lean passed",timeout=120000)
            subgoal_page.close()
            goalop_page=browser.new_page(viewport={"width":1440,"height":900})
            goalop_page.on("pageerror",lambda error:errors.append(str(error)))
            goalop_page.goto(url)
            iff_source="""theorem equivalence_demo (P Q : Prop) (forward : P → Q) (backward : Q → P) : P ↔ Q := by
  exact Iff.intro forward backward
"""
            goalop_page.locator("#lean").fill(iff_source)
            goalop_page.once("dialog",lambda d:d.accept())
            goalop_page.locator("#adopt").click()
            goalop_page.locator('[data-view="typed"]').click()
            goalop_page.locator("#extractTerm").click()
            expect(goalop_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            goalop_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            iff_node=goalop_page.locator(".typedNode").filter(has=goalop_page.locator("summary").filter(has_text=__import__("re").compile("^Apply Iff\\.intro$"))).last
            iff_node.locator(":scope > button.typedEdit").click()
            goalop_page.locator("#chainEditor summary").click()
            goalop_page.locator("#chainFormat").select_option("natural")
            goalop_page.locator("#chainText").fill("prove equivalence\n  forward direction\n    assume hp : $P$\n    $Q$ | forward hp\n  reverse direction\n    assume hq : $Q$\n    $P$ | backward hq")
            expect(goalop_page.locator("#draftTranslation")).to_contain_text("prove both directions")
            goalop_page.locator("#compileChain").click()
            expect(goalop_page.locator("#patchTerm")).to_have_value(__import__("re").compile("constructor"))
            goalop_page.locator("#checkPatch").click()
            expect(goalop_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            goalop_page.once("dialog",lambda d:d.accept())
            goalop_page.locator("#applyPatch").click()
            goalop_page.locator("#check").click()
            expect(goalop_page.locator("#verifyState")).to_have_text("Lean passed",timeout=120000)
            goalop_page.locator("#lean").fill("theorem explicit_witness_demo (P : Nat → Prop) (a : Nat) (ha : P a) : ∃ x : Nat, P x := by\n  exact ⟨a, ha⟩\n")
            goalop_page.once("dialog",lambda d:d.accept())
            goalop_page.locator("#adopt").click()
            goalop_page.locator('[data-view="typed"]').click()
            goalop_page.locator("#extractTerm").click()
            expect(goalop_page.locator("#typedStatus")).to_contain_text("Extracted from Lean elaboration",timeout=60000)
            goalop_page.locator("#typedTree").evaluate("(root) => root.querySelectorAll('details.typedNode').forEach(x=>x.open=true)")
            exists_node=goalop_page.locator(".typedNode").filter(has=goalop_page.locator("summary").filter(has_text=__import__("re").compile("^Apply Exists\\.intro$"))).last
            exists_node.locator(":scope > button.typedEdit").click()
            if not goalop_page.locator("#chainEditor").evaluate("(editor) => editor.open"):
                goalop_page.locator("#chainEditor summary").click()
            goalop_page.locator("#chainText").fill("construct witness a\n  witness property\n    $P(a)$ | ha")
            expect(goalop_page.locator("#draftTranslation")).to_contain_text("construct witness a")
            goalop_page.locator("#compileChain").click()
            expect(goalop_page.locator("#patchTerm")).to_have_value(__import__("re").compile(r"refine ⟨a, \?_⟩"))
            goalop_page.locator("#checkPatch").click()
            expect(goalop_page.locator("#applyPatch")).to_be_enabled(timeout=120000)
            goalop_page.once("dialog",lambda d:d.accept())
            goalop_page.locator("#applyPatch").click()
            goalop_page.locator("#check").click()
            expect(goalop_page.locator("#verifyState")).to_have_text("Lean passed",timeout=120000)
            goalop_page.close()
            assert not errors, errors
            browser.close()
        print("Browser smoke test passed")
    finally:
        server.terminate()
