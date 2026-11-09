"""Standalone, source-controlled HTML slide decks linked to course-graph nodes.

Slides are authored in JSON; building them does not invoke TTS, shell commands,
or user-provided URLs. Browser HTML is self-contained and kept in a local cache.
"""
from __future__ import annotations

import hashlib
import html
import json
import os
import re
from pathlib import Path
from tempfile import NamedTemporaryFile

from dkvis.presentation.paths import ROOT
from dkvis.presentation.slide_math import MathSvgRenderer, MATH_RENDERER_VERSION

SOURCE_DIR = ROOT / 'companion-slides'
CACHE_DIR = ROOT / 'companion-slide-cache'
RENDERER_VERSION = '12-coverage-stage-'+MATH_RENDERER_VERSION
FIGURE_DIR = SOURCE_DIR / 'figures'
DECK_ID = re.compile(r'^[a-z][a-z0-9-]{1,63}$')


def esc(value):
    return html.escape(str(value), quote=True)


def diagram_svg(kind):
    """Inline locally authored SVG figures; no asset URL or external request.

    Figures are SVG redrawings of geometry in the existing Manim lesson
    scenes (see companion-slides/figures/README.md). The original pilot
    diagrams are preserved as the fallback for the first two decks.
    """
    if DECK_ID.fullmatch(kind):
        figure = FIGURE_DIR / (kind + '.svg')
        if figure.is_file():
            return figure.read_text(encoding='utf8')
    """Simple explanatory figures. Labels are duplicated in the deck prose."""
    pre = ('<svg viewBox="0 0 560 270" role="img" aria-label="'
           + esc(kind.replace('_', ' ')) + ' diagram" xmlns="http://www.w3.org/2000/svg">'
           '<defs><marker id="arrow" markerWidth="7" markerHeight="7" refX="5" refY="3" orient="auto">'
           '<path d="M0,0 L6,3 L0,6" fill="none" stroke="#9cd6ef" stroke-width="1.5"/></marker></defs>')
    s = ''
    line = lambda x1,y1,x2,y2,color='#9cd6ef',width=3: (f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{color}" stroke-width="{width}" stroke-linecap="round"/>')
    txt = lambda x,y,t,size=17,color='#e8f1f7': (f'<text x="{x}" y="{y}" font-family="system-ui,sans-serif" font-size="{size}" fill="{color}">{esc(t)}</text>')
    rect = lambda x,y,w,h,c='#203849': f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="12" fill="{c}" stroke="#55768a"/>'
    if kind == 'orthogonal':
        s = line(78,212,485,212,'#607b8e',2)+line(106,240,106,32,'#607b8e',2)
        s += line(106,212,426,212,'#9cd6ef',5)+line(106,212,106,61,'#f1bf76',5)
        s += '<path d="M106 190 L128 190 L128 212" fill="none" stroke="#f1bf76" stroke-width="2.5"/>'
        s += txt(435,212,'v',22)+txt(118,54,'v⊥',21,'#f1bf76')
        s += txt(150,112,'90°',21,'#f1bf76')+txt(145,250,'invariant orthogonal decomposition',16,'#adbfcc')
    elif kind in {'angle','rotation'}:
        s = line(86,215,460,215,'#607b8e',2)+line(110,238,110,32,'#607b8e',2)
        s += line(110,215,390,215,'#9cd6ef',5)+line(110,215,348,88,'#f1bf76',5)
        s += '<path d="M175 215 A65 65 0 0 0 168 184" fill="none" stroke="#f1bf76" stroke-width="3"/>'
        s += txt(193,185,'θ',23,'#f1bf76')+txt(367,211,'original direction',15)+txt(310,77,'rotated direction',15,'#f1bf76')
        if kind=='rotation':
            s += txt(110,29,'off-diagonal coupling t',16)+txt(145,251,'two modes, one acute angle',15,'#adbfcc')
        else:
            s += txt(140,48,'principal angle between directions',16)
    elif kind in {'spectrum','clusters'}:
        s = line(64,158,512,158,'#607b8e',3)
        s += '<g fill="#9cd6ef"><circle cx="126" cy="158" r="10"/><circle cx="178" cy="158" r="10"/></g>'
        s += '<g fill="#f1bf76"><circle cx="377" cy="158" r="10"/><circle cx="415" cy="158" r="10"/></g>'
        s += line(190,118,363,118,'#f1bf76',2)+line(190,110,190,126,'#f1bf76',2)+line(363,110,363,126,'#f1bf76',2)
        s += txt(255,103,'gap δ',19,'#f1bf76')+txt(88,194,'selected',17)+txt(352,194,'other modes',17)
        s += txt(78,53,'spectral selection',20)+txt(81,245,'separation protects a selected cluster',16,'#adbfcc')
    elif kind in {'projection','induction'}:
        left, right = ('span{v}', 'v⊥') if kind == 'induction' else ('Eλ', 'Eλ⊥')
        s = rect(48,80,182,112)+rect(328,80,182,112)
        s += txt(69,124,left,29,'#9cd6ef')+txt(350,124,right,30,'#f1bf76')
        s += txt(69,158,'eigendirection' if kind=='induction' else 'eigenspace',16)
        s += txt(345,158,'complement',16)
        s += line(250,135,305,135,'#9cd6ef',3)
        s += txt(45,40,f'H = {left} ⊕ {right}',22)
        s += txt(66,238,'both pieces are invariant under A',16,'#adbfcc')
    elif kind=='residual':
        s = rect(28,86,138,102)+rect(216,86,138,102)+rect(406,86,125,102)
        s += txt(66,130,'U',30)+txt(246,130,'AU',27)+txt(433,130,'UB',25)
        s += txt(48,161,'trial frame',15)+txt(229,161,'actual action',15)+txt(410,161,'model action',15)
        s += line(165,136,214,136)+line(354,136,401,136)
        s += txt(186,44,'R = AU − UB',24,'#f1bf76')
        s += txt(151,232,'R = 0 means exact invariance',17,'#adbfcc')
    elif kind=='sylvester':
        s = rect(22,84,160,95)+rect(208,84,145,95)+rect(381,84,156,95)
        s += txt(54,127,'residual',22)+txt(241,127,'X',31,'#f1bf76')+txt(414,127,'sin θ',25)
        s += txt(51,154,'C',24)+txt(229,155,'Sylvester',16)+txt(408,154,'angle',16)
        s += line(185,130,204,130)+line(354,130,377,130)
        s += txt(137,45,'separation δ controls inversion',19)
        s += txt(120,222,'A⊥X − XB = C',23,'#f1bf76')
    elif kind=='families':
        for (x,y,label) in [(25,31,'sin θ'),(302,31,'tan θ'),(25,152,'sin(2θ)'),(302,152,'tan(2θ)')]:
            s += rect(x,y,232,87)+txt(x+33,y+38,label,24)+txt(x+22,y+64,'geometry + hypotheses',14,'#adbfcc')
    elif kind=='matching':
        s = ''.join(f'<circle cx="{x}" cy="{y}" r="17" fill="#203849" stroke="#9cd6ef" stroke-width="3"/>' for x,y in [(90,95),(225,95),(360,95),(490,95)])
        s += line(95,95,220,95,'#f1bf76',5)+line(360,95,490,95,'#f1bf76',5)
        s += txt(66,153,'θ₁',22)+txt(203,153,'θ₂',22)+txt(340,153,'θ₃',22)+txt(469,153,'θ₄',22)
        s += txt(70,216,'singletons or disjoint pairs',21)
    else:  # roadmap and any future diagram kinds
        names=['spectral data','residual & gap','angles','transport']
        for i,name in enumerate(names):
            x=12+i*140
            s+=rect(x,76,124,90)+txt(x+10,113,name.split(' ')[0],17)+txt(x+10,137,' '.join(name.split(' ')[1:]),15)
            if i<3:s+=line(x+125,121,x+138,121)
        s+=txt(88,229,'Four linked proof stages',20,'#f1bf76')
    return pre+s+'</svg>'


STYLE = """
:root{color-scheme:dark;--bg:#0b1520;--panel:#142536;--ink:#f5f1e7;--muted:#b7c9d3;--rule:#426176;--aqua:#8ee1f2;--gold:#f1c88c;--body:#dde6e9}
*{box-sizing:border-box}html{scroll-behavior:auto}body{margin:0;background:var(--bg);color:var(--ink);font:17px/1.5 system-ui,Arial,sans-serif}
button,select{font:inherit;background:#172d3e;border:1px solid #426176;border-radius:4px;padding:8px 13px;color:var(--ink);cursor:pointer}button:focus-visible,select:focus-visible{outline:2px solid var(--aqua)}button:hover{border-color:var(--aqua)}a{color:var(--aqua)}
header{display:flex;align-items:center;gap:13px;flex-wrap:wrap;padding:11px 22px;border-bottom:1px solid var(--rule);background:#101f2c}header strong{margin-right:auto;font-family:Georgia,serif;font-size:20px;font-weight:500}header .muted{font-size:.82rem;color:var(--muted)}select{max-width:350px}main{max-width:1640px;margin:0 auto;padding:16px}
.slide{background:radial-gradient(ellipse at 100% 4%,#183348 0%,transparent 46%),linear-gradient(130deg,#132737,#0e1c29 70%);border:1px solid #3b5970;aspect-ratio:16/9;min-height:610px;max-height:calc(100vh - 100px);overflow:auto;position:relative;padding:clamp(25px,2.8vw,52px) clamp(31px,3.4vw,62px) 48px;border-top:4px solid #7fcde3}.slide[hidden]{display:none}
.slide-meta{display:flex;justify-content:space-between;align-items:center;gap:20px;margin-bottom:9px}.kicker{font-size:12px;color:var(--aqua);font-weight:680;letter-spacing:.115em;text-transform:uppercase}.slide-id{font:12px/1.3 system-ui,sans-serif;letter-spacing:.11em;color:#8aafc4}
.slide h1{font-family:'EB Garamond',Georgia,'Times New Roman',serif;font-size:clamp(32px,3.65vw,57px);font-weight:500;line-height:1.08;max-width:1260px;margin:0 0 12px;letter-spacing:-.021em;color:var(--ink)}.lead{font-size:clamp(17px,1.42vw,23px);line-height:1.38;color:#bfe3ef;max-width:1100px;margin:0 0 20px;font-weight:420}
.slide-stage{display:grid;grid-template-columns:minmax(0,1fr) minmax(300px,1fr);gap:clamp(20px,3.4vw,60px);align-items:center}.slide-stage:not(:has(.figure)){grid-template-columns:1fr}.slide--reading .slide-stage{max-width:1220px;min-height:330px;margin-left:auto;margin-right:auto;align-items:center}.slide--reading .narrative{columns:2;column-gap:5vw;column-fill:balance}.slide--reading .narrative p{break-inside:avoid}.slide--reading .argument-beat{font-size:clamp(18px,1.33vw,23px);font-weight:400;line-height:1.56;margin:0 0 23px;padding-left:15px;border-left:2px solid #4d788b}.slide--reading.slide--long .argument-beat{font-size:clamp(16px,1.15vw,20px)}.slide--opening .slide-stage{grid-template-columns:1fr 1.05fr}.slide--opening .slide-stage:not(:has(.figure)){grid-template-columns:minmax(0,1fr);max-width:1130px;align-items:start;min-height:0;margin-top:24px}.slide--opening .slide-stage:not(:has(.figure)) .narrative p{max-width:88ch;font-size:clamp(18px,1.26vw,22px);line-height:1.6}.slide--opening h1{font-size:clamp(40px,4.3vw,70px)}
.narrative{min-width:0}.narrative p{margin:0 0 13px;font-size:clamp(15px,1.07vw,18px);line-height:1.53;color:var(--body);max-width:72ch}.narrative p:first-child::first-letter{font-feature-settings:'kern'}.narrative ul{list-style:none;padding:0;margin:9px 0}.narrative li{padding:7px 0 8px 21px;position:relative;color:var(--body);font-size:clamp(15px,1.05vw,18px);line-height:1.45}.narrative li:before{content:'•';position:absolute;left:0;color:var(--gold)}
.figure{margin:0;min-width:0;max-width:none;background:linear-gradient(145deg,#172e40,#122332);border:1px solid #345369;border-radius:5px;padding:clamp(14px,1.6vw,27px);display:grid;align-items:center;justify-items:center;min-height:220px}.figure svg{display:block;width:100%;height:auto;max-height:325px;overflow:visible}.slide--opening .figure svg{max-height:370px}
.math-stage{color:var(--gold);width:100%;margin:8px auto 20px;display:flex;align-items:center;justify-content:center;height:112px;min-height:112px;overflow:hidden}.math-stage svg{display:block;width:100%;height:100%;color:var(--gold);fill:currentColor}.math-stage--multi{height:154px;min-height:154px}.math-stage svg path:not([style*="fill:none"]),.math-stage svg use{fill:currentColor!important}.slide--math .math-stage{margin-top:9px;margin-bottom:18px}.slide--math.slide--reading .math-stage{max-width:1120px}
.idea{font-family:'EB Garamond',Georgia,serif;font-size:clamp(21px,2.15vw,34px);font-weight:500;color:var(--gold);border-left:3px solid var(--gold);padding:8px 20px;margin:6px 0 19px;max-width:1000px;line-height:1.2}.takeaway{color:#ebd0a7;border-top:1px solid #45667a;margin-top:18px;padding-top:12px;font-size:clamp(15px,1.09vw,18px);line-height:1.4;max-width:1150px}.takeaway::before{content:'KEY POINT  ';color:var(--aqua);font-size:11px;letter-spacing:.11em;font-weight:700;margin-right:7px}
.foot{position:absolute;bottom:12px;right:27px;font-size:11px;letter-spacing:.055em;color:#a1bdcd}.slide--figure .figure{align-self:center}
@media(min-width:1100px){
.slide--track-g2.slide--reading .slide-stage{min-height:455px}
.slide--track-g2.slide--opening .slide-stage,.slide--track-g2.slide--figure .slide-stage{min-height:440px}
.slide--track-g2.slide--opening .figure,.slide--track-g2.slide--figure .figure{min-height:315px}
.slide--track-g2.slide--equation .slide-stage{min-height:255px}
.slide--track-g2.slide--equation .narrative{columns:2;column-gap:4.5vw;max-width:none;column-fill:balance}
.slide--track-g2.slide--equation .narrative p{break-inside:avoid;font-size:clamp(17px,1.24vw,20px);line-height:1.55}
.slide--track-g2.slide--math .math-stage{min-height:132px;height:132px;margin-top:18px;margin-bottom:22px}
}
@media(max-width:1050px){.slide{aspect-ratio:auto;min-height:calc(100vh - 110px);max-height:none;padding:26px 26px 48px}.slide-stage,.slide--opening .slide-stage{grid-template-columns:1fr}.slide--reading .narrative{columns:1}.figure{max-width:680px;min-height:170px;justify-self:center}.figure svg{max-height:340px}.slide h1{font-size:clamp(31px,5.7vw,49px)}.math-stage{max-height:none}.math-stage svg{height:100%}}
body.embed header{position:sticky;top:0;z-index:10;display:flex;gap:6px;padding:6px 10px}body.embed header strong,body.embed header .muted{display:none}body.embed header button{padding:5px 9px}body.embed header select{flex:1;min-width:110px;max-width:none;padding:5px 6px}body.embed header #current{font-size:12px}body.embed main{padding:0}body.embed .slide{aspect-ratio:auto;min-height:0;max-height:none;overflow:visible;border:0;border-top:4px solid var(--aqua);border-radius:0;padding:25px 30px 48px}body.embed .slide-stage{grid-template-columns:minmax(0,1fr) minmax(240px,1fr)}body.embed .slide--reading .narrative{columns:2}body.embed .slide h1{font-size:clamp(30px,3.1vw,48px)}body.embed .lead{font-size:clamp(17px,1.45vw,22px)}body.embed .figure svg{max-height:290px}
@media(max-width:850px){body.embed .slide-stage,body.embed .slide--opening .slide-stage{grid-template-columns:1fr}body.embed .slide--reading .narrative{columns:1}body.embed .slide{padding:20px 18px 42px}}
@media print{body{background:#0b1520}header{display:none}main{max-width:none;padding:0}.slide,.slide[hidden]{display:block!important;aspect-ratio:16/9;width:100%;min-height:0;max-height:none;page-break-after:always;break-after:page;border:0;border-top:4px solid var(--aqua);overflow:hidden}.slide h1{font-size:38px}.narrative p{font-size:15px}.foot{bottom:9px}@page{size:landscape;margin:0}}
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
        self.math = MathSvgRenderer(self.cache / 'math-svg')

    def _manifest(self):
        data = json.loads((self.source/'manifest.json').read_text(encoding='utf8'))
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
            if entry.get('editorial_stage') not in {'expanded', 'baseline'}:
                raise ValueError(f'Missing editorial stage for deck {key}')
            result[key] = entry
        return result

    def _read(self, key):
        entry = self._manifest().get(key)
        if not entry:
            raise KeyError(key)
        raw = (self.source/entry['source']).read_bytes()
        data = json.loads(raw)
        if data.get('schema_version') != 1 or data.get('id') != key:
            raise ValueError(f'Invalid source for {key}')
        if data.get('editorial_stage', entry['editorial_stage']) != entry['editorial_stage']:
            raise ValueError(f'Editorial stage mismatch for {key}')
        data['editorial_stage'] = entry['editorial_stage']
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
            if not isinstance(page.get('body', []), list) or not all(isinstance(v,str) for v in page['body']):
                raise ValueError('Slide paragraphs must be a list of strings')
            if not isinstance(page.get('bullets', []), list) or not all(isinstance(v,str) for v in page.get('bullets', [])):
                raise ValueError('Slide bullets must be a list of strings')
            if 'mathtex' in page and (not isinstance(page['mathtex'], str) or len(page['mathtex']) > 4000):
                raise ValueError('Invalid MathTex equation')
            if len(json.dumps(page)) > 12000:
                raise ValueError('Slide content exceeds maximum length')
        digest = hashlib.sha256(RENDERER_VERSION.encode() + entry['editorial_stage'].encode() + raw)
        for diagram in sorted({slide.get('diagram') for slide in slides if slide.get('diagram')}):
            if not DECK_ID.fullmatch(diagram):
                raise ValueError('Invalid diagram identifier')
            figure = FIGURE_DIR / (diagram + '.svg')
            if figure.is_file():
                digest.update(figure.read_bytes())
        stamp = digest.hexdigest()[:20]
        return data, stamp

    def _path(self, key, stamp):
        return self.cache / f'{key}-{stamp}.html'

    def status(self, key):
        data, stamp = self._read(key)
        return dict(id=key, title=data['title'], subtitle=data['subtitle'],
                    editorial_stage=data['editorial_stage'], needs_expansion=data['editorial_stage']=='baseline',
                    slide_count=len(data['slides']), lecture_nodes=data['lecture_nodes'],
                    built=self._path(key, stamp).is_file(),
                    url=f'/slide-decks/{key}',
                    download_url=f'/api/slide-decks/{key}/download')

    def list_for_lecture(self, node_id):
        result=[]
        for key, row in self._manifest().items():
            if node_id in row['lecture_nodes']:
                result.append(self.status(key))
        return result

    def catalog(self):
        return [self.status(key) for key in self._manifest()]

    def rendered(self, key):
        _, stamp=self._read(key)
        path=self._path(key,stamp)
        if not path.is_file():
            raise FileNotFoundError(key)
        return path

    def build(self, key):
        data,stamp=self._read(key)
        target=self._path(key,stamp)
        if target.is_file():
            return self.status(key)
        content=render_html(data, math_svg=self.math.svg).encode('utf8')
        self.cache.mkdir(parents=True,exist_ok=True)
        # Atomic publish; safe when multiple browsers request the same build.
        with NamedTemporaryFile('wb',dir=self.cache,prefix='.building-',delete=False) as f:
            temp=Path(f.name)
            try:
                f.write(content)
                f.flush();os.fsync(f.fileno())
            finally:
                pass
        try:
            temp.replace(target)
        finally:
            temp.unlink(missing_ok=True)
        return self.status(key)


def render_html(deck, *, math_svg=None):
    # Compose accessible reading slides with typeset vector mathematics.
    if math_svg is None:
        import tempfile
        math_svg = MathSvgRenderer(Path(tempfile.gettempdir()) / 'dkps-slide-math-svg').svg
    parts=[]
    tracks = {node.split(':', 1)[0].upper() for node in deck.get('lecture_nodes', [])}
    track_label = ' / '.join(sorted(tracks)) if tracks else 'DKPS'
    baseline = deck.get('editorial_stage') == 'baseline'
    stage_label = 'BASELINE · NEEDS EXPANSION' if baseline else ''
    for index,slide in enumerate(deck['slides']):
        layout=slide.get('layout') or ('figure' if slide.get('diagram') else 'reading')
        body=slide.get('body', [])
        if layout == 'reading' and not slide.get('mathtex') and not slide.get('diagram'):
            # Presentation prose is independent of the audio. Preserve every
            # sentence while composing short readable argument beats.
            sentences=[]
            for paragraph in body:
                sentences.extend(re.split(r'(?<=[.!?])\s+(?=[A-Z])', paragraph))
            beats=[]
            for sentence in sentences:
                if beats and len(beats[-1]) + len(sentence) < 185:
                    beats[-1] += ' ' + sentence
                else:
                    beats.append(sentence)
            paragraphs=''.join(f'<p class="argument-beat">{esc(b)}</p>' for b in beats)
        else:
            paragraphs=''.join(f'<p>{esc(p)}</p>' for p in body)
        bullets=slide.get('bullets') or []
        if bullets:
            paragraphs+='<ul>'+''.join(f'<li>{esc(b)}</li>' for b in bullets)+'</ul>'
        tex=slide.get('mathtex')
        math=(f'<div class="math-stage{" math-stage--multi" if ("\\begin{aligned}" in tex or "\\begin{bmatrix}" in tex) else ""}">{math_svg(tex)}</div>' if tex else '')
        # A formula field without MathTex denotes an editorial proposition,
        # never a mathematical formula to be impersonated by Unicode text.
        idea=(f'<div class="idea">{esc(slide["formula"])}</div>'
              if slide.get('formula') and not tex else '')
        figure=(f'<figure class="figure">{diagram_svg(slide["diagram"])}</figure>'
                if slide.get('diagram') else '')
        takeaway=(f'<div class="takeaway">{esc(slide["takeaway"])}</div>'
                  if slide.get('takeaway') else '')
        layout=slide.get('layout') or ('figure' if figure else 'reading')
        if layout not in ('figure','reading','opening','equation'):
            raise ValueError(f'Unsupported slide layout {layout}')
        total_chars=sum(map(len,body))
        classes=('slide slide--'+layout+(' slide--track-g2' if 'G2' in tracks else '')+(' slide--math' if math else '')
                 +(' slide--brief' if total_chars<400 else ' slide--long'))
        stage=f'<div class="slide-stage"><div class="narrative">{paragraphs}</div>{figure}</div>'
        parts.append(f'''<section class="{classes}" id="slide-{index+1}" {'hidden' if index else ''}>
<div class="slide-meta"><div class="kicker">{esc(slide.get('eyebrow') or deck['title'])}</div><div class="slide-id">{esc(stage_label + ' · ' if baseline else '')}{esc(track_label)} · {index+1:02d} / {len(deck['slides']):02d}</div></div>
<h1>{esc(slide['title'])}</h1><p class="lead">{esc(slide['lead'])}</p>
{math}{idea}{stage}{takeaway}
<div class="foot">{esc(deck['title'])} · {index+1} / {len(deck['slides'])}</div></section>''')
    options=''.join(f'<option value="{i}">{i+1}. {esc(slide["title"])}</option>' for i,slide in enumerate(deck['slides']))
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(deck['title'])} · DKPS companion slides</title><style>{STYLE}</style></head>
<body><header><strong>{esc(deck['title'])}</strong><span class="muted">{esc('Baseline outline · needs expansion' if baseline else 'Standalone mathematics')} · arrow keys navigate</span>
<button id="prev" aria-label="Previous slide">◀</button><select id="jump" aria-label="Select slide">{options}</select>
<span id="current" aria-live="polite">1 / {len(deck['slides'])}</span><button id="next" aria-label="Next slide">▶</button>
<button onclick="window.print()" aria-label="Print or save as PDF">Print / PDF</button></header>
<main>{''.join(parts)}</main><script>{SCRIPT}</script></body></html>'''


def main(argv=None):
    import argparse
    parser=argparse.ArgumentParser(description='Build self-contained HTML companion slides')
    parser.add_argument('deck', nargs='?', default=None, help='deck ID, or all decks if omitted')
    parser.add_argument('--source',type=Path,default=SOURCE_DIR)
    parser.add_argument('--cache',type=Path,default=CACHE_DIR)
    args=parser.parse_args(argv)
    library=CompanionSlideLibrary(args.source,args.cache)
    for key in [args.deck] if args.deck else [row['id'] for row in library.catalog()]:
        print(library.build(key))


if __name__=='__main__':
    main()
