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
            assert page.evaluate("document.documentElement.scrollWidth <= window.innerWidth + 1"),"mobile overflow"
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
            patch_page.close()
            assert not errors, errors
            browser.close()
        print("Browser smoke test passed")
    finally:
        server.terminate()
