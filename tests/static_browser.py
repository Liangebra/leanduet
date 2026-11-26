"""Smoke-test the exact static site at its GitHub Pages subpath."""
import functools
import http.server
from pathlib import Path
import shutil
import tempfile
import threading
from playwright.sync_api import sync_playwright, expect

ROOT=Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory() as tmp:
    shutil.copytree(ROOT/"web",Path(tmp)/"leanduet")
    handler=functools.partial(http.server.SimpleHTTPRequestHandler,directory=tmp)
    with http.server.ThreadingHTTPServer(("127.0.0.1",0),handler) as server:
        threading.Thread(target=server.serve_forever,daemon=True).start()
        url=f"http://127.0.0.1:{server.server_port}/leanduet/"
        try:
            with sync_playwright() as p:
                browser=p.chromium.launch()
                page=browser.new_page(viewport={"width":1440,"height":900})
                errors=[]
                page.on("pageerror",lambda e:errors.append(str(e)))
                page.goto(url+"?demo=1")
                expect(page.locator("#theoremName")).to_have_text("compose imp")
                expect(page.locator("#check")).to_be_disabled()
                expect(page.locator("#highlight .tok-keyword").first).to_be_visible()
                assert page.locator("#highlight").inner_text().rstrip()==page.locator("#lean").input_value().rstrip()
                expect(page.locator(".pane").first).to_have_css("border-radius","0px")
                page.screenshot(path=str(ROOT/"workbench-preview.png"))
                page.locator("#splitter").focus()
                page.keyboard.press("ArrowRight")
                expect(page.locator("#splitter")).to_have_attribute("aria-valuenow","55")
                page.locator("#toggleLayout").click()
                expect(page.locator("body")).to_have_class("notebook-layout")
                expect(page.locator("#splitter")).to_be_hidden()
                page.locator("#toggleLayout").click()
                page.locator("#toggleExplorer").click()
                expect(page.locator(".rail")).to_be_hidden()
                page.locator("#toggleExplorer").click()
                page.get_by_role("link",name="About",exact=True).click()
                expect(page.locator("article#en")).to_be_visible()
                page.get_by_role("link",name="简体中文",exact=True).click()
                expect(page.locator("html")).to_have_attribute("lang","zh-CN")
                page.get_by_role("link",name="日本語",exact=True).click()
                expect(page.locator("article#ja")).to_be_visible()
                page.set_viewport_size({"width":390,"height":844})
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+1")
                page.goto(url+"community.html#zh")
                expect(page.locator("article#zh")).to_be_visible()
                expect(page.locator("html")).to_have_attribute("lang","zh-CN")
                expect(page.locator('article#zh a[href$="/issues/8"]')).to_be_visible()
                page.get_by_role("link",name="日本語",exact=True).click()
                expect(page.locator("article#ja")).to_be_visible()
                page.get_by_role("link",name="English",exact=True).click()
                expect(page.locator("article#en")).to_be_visible()
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+1"), "community mobile overflow"
                page.goto(url+"?demo=1")
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+1")
                expect(page.get_by_role("link",name="About",exact=True)).to_be_visible()
                page.locator("#theme").click()
                original=page.locator("#lean").input_value()
                page.locator('[data-view="notes"]').click()
                free="Maybe compactness is the wrong assumption?\n自定义符号 ⊛; $Q$; prove or find a counterexample."
                page.locator("#prompt").fill(free)
                expect(page.locator("#stageFormula")).to_be_disabled()
                expect(page.locator("#lean")).to_have_value(original)
                page.locator("#addObject").click()
                page.get_by_label("#1 Name or notation",exact=True).fill("x ⊛")
                page.get_by_label("#1 Expression / provisional definition",exact=True).fill("undefined x / 0 = ???")
                page.get_by_label("#1 Research status",exact=True).select_option("doubtful")
                page.get_by_role("button",name="Try an alternative",exact=True).click()
                page.get_by_label("#2 Expression / provisional definition",exact=True).fill("some other x")
                expect(page.locator("#exploreObjects")).to_contain_text("#1")
                expect(page.locator("#lean")).to_have_value(original)
                page.reload()
                page.locator('[data-view="notes"]').click()
                expect(page.locator("#exploreObjects")).to_contain_text("#1 x ⊛ · doubtful")
                expect(page.locator("#exploreObjects")).to_contain_text("#2 x ⊛ · idea")
                page.locator("#exploreObjects summary").first.click()
                expect(page.get_by_label("#1 Expression / provisional definition",exact=True)).to_have_value("undefined x / 0 = ???")
                expect(page.locator("#prompt")).to_have_value(free)
                expect(page.locator("#lean")).to_have_value(original)
                page.locator('[data-view="prose"]').click()
                page.locator("#prose").fill(page.locator("#prose").input_value()+"draft")
                page.locator("#lean").fill(page.locator("#lean").input_value()+"  rfl\n")
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+1"), "dirty dark mobile workspace overflow"
                assert not errors, errors
                browser.close()
            print("Static Pages workbench, layout controls and three-language introduction passed")
        finally:
            server.shutdown()
