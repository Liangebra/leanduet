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
                page.goto(url+"?demo=1")
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+1")
                expect(page.get_by_role("link",name="About",exact=True)).to_be_visible()
                page.locator("#theme").click()
                page.locator('[data-view="prose"]').click()
                page.locator("#prose").fill(page.locator("#prose").input_value()+"draft")
                page.locator("#lean").fill(page.locator("#lean").input_value()+"  rfl\n")
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+1"), "dirty dark mobile workspace overflow"
                assert not errors, errors
                browser.close()
            print("Static Pages workbench, layout controls and three-language introduction passed")
        finally:
            server.shutdown()
