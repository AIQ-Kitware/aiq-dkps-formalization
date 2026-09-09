#!/usr/bin/env python3
import pathlib
import shutil
import subprocess

from playwright.sync_api import sync_playwright


repo = pathlib.Path(
    subprocess.check_output(
        ['git', 'rev-parse', '--show-toplevel'],
        text=True,
    ).strip()
)

src = repo / 'build/semantic-alignment/review.html'
out_dpath = repo / 'papers/formalization_process_4page/figures'
out_dpath.mkdir(parents=True, exist_ok=True)

if not src.exists():
    raise FileNotFoundError(
        f'Semantic-alignment page does not exist: {src}\n'
        'Run ./semantic-alignment-page.sh --statements --no-open first.'
    )

browser_exe = (
    shutil.which('google-chrome')
    or shutil.which('google-chrome-stable')
    or shutil.which('chromium')
    or shutil.which('chromium-browser')
)
if browser_exe is None:
    raise RuntimeError('Could not find Chrome or Chromium')

url = src.resolve().as_uri() + '#3-S2-sin-theta'
with sync_playwright() as p:
    browser = p.chromium.launch(headless=True, executable_path=browser_exe)
    context = browser.new_context(
        viewport={'width': 2600, 'height': 1500},
        device_scale_factor=2,
    )
    page = context.new_page()
    page.goto(url, wait_until='networkidle')
    page.evaluate(
        '''
        async () => {
            if (document.fonts && document.fonts.ready) {
                await document.fonts.ready;
            }
        }
        '''
    )
    row = page.locator('[id="3-S2-sin-theta"]')
    row.wait_for(state='visible')
    page.wait_for_timeout(1000)

    # The viewport image is the appendix screenshot. A row-only capture is also
    # useful for diagnostics and future figure variants.
    page.screenshot(
        path=str(out_dpath / 'semantic-alignment-dashboard.png'),
        full_page=False,
    )
    row.screenshot(path=str(out_dpath / 'semantic-alignment-sine-theta-row.png'))
    browser.close()

print(f'Wrote screenshots to: {out_dpath}')
