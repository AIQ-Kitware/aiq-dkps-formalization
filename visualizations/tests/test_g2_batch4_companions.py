"""The G2 054000-061000 companion expansion is source-grounded and renderable."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from dkvis.presentation.companion_geometry import companion_figure_kind
from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR

G2_BATCH4_NODES = tuple(f'g2:{n:03d}000' for n in range(54,62))


def test_g2_batch4_decks_have_authored_proofs_math_and_figures():
    catalog={node:row for row in CompanionSlideLibrary().catalog() for node in row['lecture_nodes']}
    total_math=0
    all_figures=set()
    for node in G2_BATCH4_NODES:
        entry=catalog[node]
        assert entry['editorial_stage']=='expanded' and not entry['needs_expansion']
        deck=json.loads((SOURCE_DIR/(entry['id']+'.json')).read_text(encoding='utf8'))
        assert deck['editorial_stage']=='expanded'
        lecture=(SOURCE_DIR.parent/deck['source_lecture']).read_text(encoding='utf8')
        assert '<!-- BEGIN SPOKEN LECTURE -->' in lecture
        assert '<!-- END SPOKEN LECTURE -->' in lecture
        assert len(deck['slides']) == 10
        assert len({s['id'] for s in deck['slides']})==10
        assert sum(bool(s.get('mathtex')) for s in deck['slides'])>=5
        assert sum(bool(s.get('diagram')) for s in deck['slides'])>=7
        for slide in deck['slides']:
            assert 'first-pass outline' not in slide['eyebrow']
            assert slide['takeaway'] and slide['title'] and slide['lead']
            assert len(slide['body'])>=2
            assert len(' '.join([slide['lead'], *slide['body']]).split())>=43
            if figname:=slide.get('diagram'):
                all_figures.add(figname)
                assert companion_figure_kind(figname),(node,figname)
        total_math+=sum('mathtex' in slide for slide in deck['slides'])
    assert total_math>=50
    assert len(all_figures)>=12


def test_g2_batch4_decks_render_without_external_web_assets(tmp_path,monkeypatch):
    from dkvis.presentation import companion_slides as renderer
    monkeypatch.setattr(renderer, 'render_slide_png', lambda deck, slide, index, count, cache_dir=None: b'PNG')
    library=CompanionSlideLibrary(SOURCE_DIR,tmp_path/'rendered')
    for node in G2_BATCH4_NODES:
        deck=next(row['id'] for row in library.catalog() if node in row['lecture_nodes'])
        result=library.build(deck)
        html=library.rendered(deck).read_text(encoding='utf8')
        assert result['built'] and result['slide_count']==10
        assert html.count('<section class="slide slide--')==10
        assert 'BASELINE · NEEDS EXPANSION' not in html
        assert 'data:image/png;base64,' in html
        assert '<script src=' not in html


def test_g2_batch4_promotion_script_is_idempotent():
    root=Path(__file__).resolve().parents[1]
    proc=subprocess.run([sys.executable,str(root/'tools/promote_g2_054000_061000.py'),'--check'],
                        cwd=root,capture_output=True,text=True)
    assert proc.returncode==0,proc.stdout+proc.stderr


def test_g2_batch4_central_mathematical_distinctions():
    def full_text(n):
        deck=next(SOURCE_DIR.glob(f'g2-{n:03d}000-*.json'))
        document=json.loads(deck.read_text(encoding='utf8'))
        return ' '.join(' '.join([s['title'],s['lead'],*s['body'],s.get('takeaway','')])
                        for s in document['slides'])
    assert 'componentwise' in full_text(54) and 'Ky Fan' in full_text(54)
    assert 'prefix' in full_text(55) and 'weak' in full_text(55)
    assert 'sign symmetry' in full_text(56) and 'convexity' in full_text(56)
    assert 'Gram' in full_text(57) and 'trace' in full_text(57)
    assert 'fixed' in full_text(58) and 'ideal' in full_text(58)
    assert 'padding' in full_text(59) and 'compression' in full_text(59)
    assert 'reflection' in full_text(60) and 'concatenate' in full_text(60)
    assert 'squaring' in full_text(61) and 'Courant' in full_text(61)
