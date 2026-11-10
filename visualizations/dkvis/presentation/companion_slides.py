"""Standalone, source-controlled Manim slide decks linked to course-graph nodes.

Slides are authored in JSON, but every build renders the slide visuals with
Manim and wraps the resulting images in a standalone HTML viewer. Building them
never invokes TTS, shell commands from the network, or user-provided URLs.
"""
from __future__ import annotations

import base64
import hashlib
import html
import json
import os
import re
from pathlib import Path
from tempfile import NamedTemporaryFile

from dkvis.presentation.paths import ROOT
from dkvis.presentation.companion_geometry import companion_figure_kind

SOURCE_DIR = ROOT / 'companion-slides'
CACHE_DIR = ROOT / 'companion-slide-cache'
RENDERER_VERSION = '12-native-manim-diagrams'
DECK_ID = re.compile(r'^[a-z][a-z0-9-]{1,63}$')


def esc(value):
    return html.escape(str(value), quote=True)


def render_slide_png(deck, slide, index, count, *, cache_dir=None):
    """Compatibility wrapper around the Manim slide-image renderer."""
    from dkvis.presentation.companion_manim import render_slide_png as _render

    return _render(deck, slide, index, count, cache_dir=cache_dir)


STYLE = """
:root{color-scheme:dark;--bg:#0b1520;--panel:#132231;--rule:#38556a;--ink:#f5f1e7;--muted:#aec1cb;--aqua:#8ee1f2}
*{box-sizing:border-box}html{scroll-behavior:auto}body{margin:0;background:var(--bg);color:var(--ink);font:17px/1.5 system-ui,Arial,sans-serif}
button,select{font:inherit;background:#172d3e;border:1px solid #426176;border-radius:4px;padding:8px 13px;color:var(--ink);cursor:pointer}button:focus-visible,select:focus-visible{outline:2px solid var(--aqua)}button:hover{border-color:var(--aqua)}a{color:var(--aqua)}
header{display:flex;align-items:center;gap:13px;flex-wrap:wrap;padding:11px 22px;border-bottom:1px solid var(--rule);background:#101f2c}header strong{margin-right:auto;font-size:20px;font-weight:600}header .muted{font-size:.82rem;color:var(--muted)}select{max-width:380px}main{max-width:1700px;margin:0 auto;padding:16px}
.slide{background:var(--panel);border:1px solid var(--rule);padding:14px;border-radius:8px}.slide[hidden]{display:none}.slide-image{display:block;width:100%;height:auto;background:#0b1520}.slide-source{position:absolute;left:-99999px;top:auto;width:1px;height:1px;overflow:hidden}
.viewer-frame{position:relative}.foot{display:flex;justify-content:flex-end;margin-top:8px;font-size:12px;letter-spacing:.05em;color:var(--muted)}
body.embed header{position:sticky;top:0;z-index:10;display:flex;gap:6px;padding:6px 10px}body.embed header strong,body.embed header .muted{display:none}body.embed header button{padding:5px 9px}body.embed header select{flex:1;min-width:110px;max-width:none;padding:5px 6px}body.embed header #current{font-size:12px}body.embed main{padding:0}body.embed .slide{border-radius:0;border-left:0;border-right:0;padding:0}
@media print{body{background:#0b1520}header{display:none}main{max-width:none;padding:0}.slide,.slide[hidden]{display:block!important;page-break-after:always;break-after:page;border:0;border-radius:0;padding:0;background:#0b1520}.foot{display:none}@page{size:landscape;margin:0}}
"""
SCRIPT = """
'use strict';
if(new URLSearchParams(location.search).has('embed')) document.body.classList.add('embed');
const pages=[...document.querySelectorAll('.slide')];
const picker=document.getElementById('jump');
const current=document.getElementById('current');
const prev=document.getElementById('prev');
const next=document.getElementById('next');
let at=0;
function show(index){
 at=Math.max(0,Math.min(pages.length-1,index));
 pages.forEach((page,i)=>page.hidden=i!==at);
 picker.value=String(at);current.textContent=`${at+1} / ${pages.length}`;
 prev.disabled=at===0;next.disabled=at===pages.length-1;
 try{history.replaceState(null,'',`#slide=${at+1}`)}catch{}
 window.scrollTo({top:0,behavior:'instant'});
}
prev.onclick=()=>show(at-1);next.onclick=()=>show(at+1);
picker.onchange=()=>show(Number(picker.value));
document.addEventListener('keydown',event=>{
 if(['INPUT','SELECT','TEXTAREA'].includes(document.activeElement?.tagName))return;
 if(event.key==='ArrowRight'||event.key==='PageDown'){event.preventDefault();show(at+1)}
 if(event.key==='ArrowLeft'||event.key==='PageUp'){event.preventDefault();show(at-1)}
});
show(Math.max(0,(Number(location.hash.match(/slide=(\\d+)/)?.[1]||1)||1)-1));
"""


class CompanionSlideLibrary:
    def __init__(self, source=SOURCE_DIR, cache=CACHE_DIR):
        self.source = Path(source).resolve()
        self.cache = Path(cache).resolve()

    def _manifest(self):
        data = json.loads((self.source / 'manifest.json').read_text(encoding='utf8'))
        if data.get('schema_version') != 1 or not isinstance(data.get('decks'), list):
            raise ValueError('Invalid companion slide manifest')
        result = {}
        for entry in data['decks']:
            key = entry['id']
            if not DECK_ID.fullmatch(key) or key in result:
                raise ValueError('Invalid or duplicate slide deck ID')
            if entry.get('source') != f'{key}.json':
                raise ValueError('Slide source filenames must match stable deck IDs')
            if not isinstance(entry.get('lecture_nodes'), list):
                raise ValueError('Slide deck requires lecture-node associations')
            result[key] = entry
        return result

    def _read(self, key):
        entry = self._manifest().get(key)
        if not entry:
            raise KeyError(key)
        raw = (self.source / entry['source']).read_bytes()
        data = json.loads(raw)
        if data.get('schema_version') != 1 or data.get('id') != key:
            raise ValueError(f'Invalid source for {key}')
        if data.get('lecture_nodes') != entry['lecture_nodes']:
            raise ValueError(f'Mismatched lecture links for {key}')
        slides = data.get('slides')
        if not isinstance(slides, list) or not (1 <= len(slides) <= 100):
            raise ValueError(f'Invalid slide count for {key}')
        ids = set()
        for page in slides:
            if not isinstance(page, dict) or not isinstance(page.get('title'), str) or not isinstance(page.get('lead'), str):
                raise ValueError(f'Invalid slide entry in {key}')
            if page.get('id') in ids or not isinstance(page.get('id'), str):
                raise ValueError(f'Duplicate or invalid page ID in {key}')
            ids.add(page['id'])
            if not isinstance(page.get('body', []), list) or not all(isinstance(v, str) for v in page['body']):
                raise ValueError('Slide paragraphs must be a list of strings')
            if not isinstance(page.get('bullets', []), list) or not all(isinstance(v, str) for v in page.get('bullets', [])):
                raise ValueError('Slide bullets must be a list of strings')
            if 'mathtex' in page and (not isinstance(page['mathtex'], str) or len(page['mathtex']) > 4000):
                raise ValueError('Invalid MathTex equation')
            if len(json.dumps(page)) > 12000:
                raise ValueError('Slide content exceeds maximum length')
        digest = hashlib.sha256(RENDERER_VERSION.encode() + raw)
        digest.update(os.environ.get('DKVIS_THEME', 'dark').encode())
        for name in ('companion_manim.py', 'companion_geometry.py'):
            digest.update(Path(__file__).with_name(name).read_bytes())
        for name in ('palette.py', 'slide_style.py'):
            digest.update(Path(__file__).resolve().parents[1].joinpath(name).read_bytes())
        for diagram in sorted({slide.get('diagram') for slide in slides if slide.get('diagram')}):
            if not DECK_ID.fullmatch(diagram):
                raise ValueError('Invalid diagram identifier')
            companion_figure_kind(diagram)  # A missing diagram must fail before rendering.
        stamp = digest.hexdigest()[:20]
        return data, stamp

    def _path(self, key, stamp):
        return self.cache / f'{key}-{stamp}.html'

    def status(self, key):
        data, stamp = self._read(key)
        stage = self._manifest()[key].get('editorial_stage', 'baseline')
        return dict(
            editorial_stage=stage,
            needs_expansion=(stage == 'baseline'),
            id=key,
            title=data['title'],
            subtitle=data['subtitle'],
            slide_count=len(data['slides']),
            lecture_nodes=data['lecture_nodes'],
            built=self._path(key, stamp).is_file(),
            url=f'/slide-decks/{key}',
            download_url=f'/api/slide-decks/{key}/download',
        )

    def list_for_lecture(self, node_id):
        return [self.status(key) for key, row in self._manifest().items() if node_id in row['lecture_nodes']]

    def catalog(self):
        return [self.status(key) for key in self._manifest()]

    def rendered(self, key):
        _, stamp = self._read(key)
        path = self._path(key, stamp)
        if not path.is_file():
            raise FileNotFoundError(key)
        return path

    def build(self, key):
        data, stamp = self._read(key)
        target = self._path(key, stamp)
        if target.is_file():
            return self.status(key)
        content = render_html(data, cache_dir=self.cache / 'frames' / stamp).encode('utf8')
        self.cache.mkdir(parents=True, exist_ok=True)
        with NamedTemporaryFile('wb', dir=self.cache, prefix='.building-', delete=False) as f:
            temp = Path(f.name)
            f.write(content)
            f.flush()
            os.fsync(f.fileno())
        try:
            temp.replace(target)
        finally:
            temp.unlink(missing_ok=True)
        return self.status(key)


def _data_uri(raw: bytes, mime: str = 'image/png') -> str:
    return f'data:{mime};base64,' + base64.b64encode(raw).decode('ascii')


def _slide_source_text(slide):
    chunks = [slide['title'], slide['lead']]
    chunks.extend(slide.get('body', []))
    chunks.extend(slide.get('bullets', []))
    if slide.get('takeaway'):
        chunks.append(slide['takeaway'])
    return ' '.join(part.strip() for part in chunks if part and part.strip())


# ``math_svg`` remains accepted as a compatibility placeholder for old tests and
# callers.  The rendered visual source is now the Manim slide image.
def render_html(deck, *, render_slide_png_fn=None, math_svg=None, cache_dir=None):
    del math_svg
    render_slide_png_fn = render_slide_png if render_slide_png_fn is None else render_slide_png_fn
    cache_dir = Path(cache_dir or CACHE_DIR)
    parts = []
    for index, slide in enumerate(deck['slides']):
        raw = render_slide_png_fn(deck, slide, index, len(deck['slides']), cache_dir=cache_dir)
        src = _data_uri(raw)
        source_text = _slide_source_text(slide)
        parts.append(
            f'''<section class="slide slide--image" id="slide-{index+1}" {'hidden' if index else ''}>
<div class="viewer-frame"><img class="slide-image" alt="{esc(source_text)}" src="{src}"></div>
<div class="slide-source">{esc(source_text)}</div>
<div class="foot">{esc(deck['title'])} · {index+1} / {len(deck['slides'])}</div></section>'''
        )
    options = ''.join(
        f'<option value="{i}">{i+1}. {esc(slide["title"])}</option>' for i, slide in enumerate(deck['slides'])
    )
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(deck['title'])} · DKPS companion slides</title><style>{STYLE}</style></head>
<body><header><strong>{esc(deck['title'])}</strong><span class="muted">Manim-rendered slide deck · arrow keys navigate</span>
<button id="prev" aria-label="Previous slide">◀</button><select id="jump" aria-label="Select slide">{options}</select>
<span id="current" aria-live="polite">1 / {len(deck['slides'])}</span><button id="next" aria-label="Next slide">▶</button>
<button onclick="window.print()" aria-label="Print or save as PDF">Print / PDF</button></header>
<main>{''.join(parts)}</main><script>{SCRIPT}</script></body></html>'''


def main(argv=None):
    import argparse

    parser = argparse.ArgumentParser(description='Build standalone Manim companion-slide decks')
    parser.add_argument('deck', nargs='?', default=None, help='deck ID, or all decks if omitted')
    parser.add_argument('--source', type=Path, default=SOURCE_DIR)
    parser.add_argument('--cache', type=Path, default=CACHE_DIR)
    args = parser.parse_args(argv)
    library = CompanionSlideLibrary(args.source, args.cache)
    for key in [args.deck] if args.deck else [row['id'] for row in library.catalog()]:
        print(library.build(key))


if __name__ == '__main__':
    main()
