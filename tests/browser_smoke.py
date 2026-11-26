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
            assert not errors, errors
            browser.close()
        print("Browser smoke test passed")
    finally:
        server.terminate()
