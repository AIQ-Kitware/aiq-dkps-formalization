"""Regression tests for the expanded G2 062000--069000 Sylvester companion decks."""
from __future__ import annotations

import json
import math
import shutil
import subprocess
import sys
from pathlib import Path

from dkvis.presentation.companion_geometry import companion_figure_kind
from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR
from tools import promote_g2_062000_069000 as promotion

G2_SYLVESTER_NODES = tuple(f'g2:{i:03d}000' for i in range(62,70))


def test_g2_sylvester_decks_have_complete_math_and_local_figures():
    catalog={node:row for row in CompanionSlideLibrary().catalog() for node in row['lecture_nodes']}
    math_count=0
    figures=set()
    for node in G2_SYLVESTER_NODES:
        meta=catalog[node]
        assert meta['editorial_stage']=='expanded'
        assert not meta['needs_expansion']
        deck=json.loads((SOURCE_DIR/(meta['id']+'.json')).read_text(encoding='utf8'))
        lecture=(SOURCE_DIR.parent/deck['source_lecture']).read_text(encoding='utf8')
        assert '<!-- BEGIN SPOKEN LECTURE -->' in lecture
        assert '<!-- END SPOKEN LECTURE -->' in lecture
        assert len(deck['slides']) == 10
        assert len({row['id'] for row in deck['slides']})==10
        assert sum(bool(row.get('mathtex')) for row in deck['slides'])>=8
        for slide in deck['slides']:
            assert slide['title'] and slide['lead'] and slide['takeaway']
            assert len(' '.join([slide['lead'],*slide['body']]).split()) >= 35
            assert all(text.strip().endswith(('.', '!', '?', '”')) for text in slide['body'])
            assert 'first-pass outline' not in slide['eyebrow']
            if name:=slide.get('diagram'):
                figures.add(name)
                assert companion_figure_kind(name),(node,name)
        math_count+=sum(bool(row.get('mathtex')) for row in deck['slides'])
    assert math_count >=70
    assert len(figures)==15


def test_g2_sylvester_slides_are_standalone_and_render_locally(tmp_path,monkeypatch):
    from dkvis.presentation import companion_slides as renderer
    monkeypatch.setattr(renderer, 'render_slide_png', lambda deck, slide, index, count, cache_dir=None: b'PNG')
    lib=CompanionSlideLibrary(SOURCE_DIR,tmp_path/'rendered')
    for node in G2_SYLVESTER_NODES:
        key=next(x['id'] for x in lib.catalog() if node in x['lecture_nodes'])
        record=lib.build(key)
        html=lib.rendered(key).read_text(encoding='utf8')
        assert record['slide_count']==10 and record['built']
        assert html.count('<section class="slide slide--')==10
        assert 'BASELINE · NEEDS EXPANSION' not in html
        assert '<script src=' not in html
        assert 'data:image/png;base64,' in html
        deck=json.loads((SOURCE_DIR/(key+'.json')).read_text(encoding='utf8'))
        prose=' '.join(' '.join([s['lead'],*s['body']]) for s in deck['slides']).lower()
        for dangling in ['in the previous lecture','later lecture', 'we met spectral projections earlier',
                         'we will prove its mechanism after']:
            assert dangling not in prose


def test_g2_sylvester_promotion_preserves_unrelated_manifest_entries(tmp_path,monkeypatch):
    temporary=tmp_path/'companion-slides'
    temporary.mkdir()
    manifest=json.loads((SOURCE_DIR/'manifest.json').read_text(encoding='utf8'))
    unrelated=manifest['decks'][0]
    unrelated['external_agent_marker']='preserved'
    for node in G2_SYLVESTER_NODES:
        row=next(x for x in manifest['decks'] if x['lecture_nodes']==[node])
        row['editorial_stage']='baseline'
        shutil.copy2(SOURCE_DIR/row['source'], temporary/row['source'])
    (temporary/'manifest.json').write_text(json.dumps(manifest),encoding='utf8')
    monkeypatch.setattr(promotion,'G2_SYLVESTER_DECK_DIRECTORY',temporary)
    pending=promotion.promote_g2_sylvester_decks(write=False)
    assert len(pending)==8
    assert len(promotion.promote_g2_sylvester_decks(write=True))==8
    assert promotion.promote_g2_sylvester_decks(write=True)==[]
    after=json.loads((temporary/'manifest.json').read_text(encoding='utf8'))
    assert after['decks'][0]['external_agent_marker']=='preserved'
    assert all(next(row for row in after['decks'] if row['lecture_nodes']==[node])['editorial_stage']=='expanded'
               for node in G2_SYLVESTER_NODES)


def test_g2_sylvester_exact_numerical_examples():
    # Both sides of AX-XB=C for the entrywise lecture 063000.
    a=[1,4]; b=[0,3]
    x=[[2,-3],[2,10]]
    c=[[2,6],[8,10]]
    assert [[(a[i]-b[j])*x[i][j] for j in range(2)] for i in range(2)]==c
    # The pairwise-gap counterexample from 069000.
    a=[1,-1];b=[0,2];x=[[3,-3],[-3,1]]
    c=[[(a[i]-b[j])*x[i][j] for j in range(2)] for i in range(2)]
    assert c==[[3,3],[3,-3]]
    assert math.isclose(2+math.sqrt(10),5.162277660168379)
    assert 2+math.sqrt(10)>3*math.sqrt(2)
    # One-dimensional ordered gap saturation.
    delta=2;c_scalar=1
    assert (delta-0)*(c_scalar/delta)==c_scalar


def test_g2_sylvester_promotion_cli_direct_command():
    script=Path(__file__).resolve().parents[1]/'tools/promote_g2_062000_069000.py'
    result=subprocess.run([sys.executable,str(script),'--check'],capture_output=True,text=True)
    assert result.returncode==0,result.stdout+result.stderr
