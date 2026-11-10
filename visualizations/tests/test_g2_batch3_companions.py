"""Source, rendering, and manifest invariants for G2 046000–053000."""
import json
from pathlib import Path
import subprocess
import sys

from dkvis.presentation.companion_geometry import companion_figure_kind
from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR

BATCH3_NODES=tuple(f'g2:{n:03d}000' for n in range(46,54))


def test_g2_batch3_curated_mathematics_and_provenance():
    catalog={row['lecture_nodes'][0]:row for row in CompanionSlideLibrary().catalog()
             if len(row['lecture_nodes'])==1}
    for node in BATCH3_NODES:
        entry=catalog[node]
        assert entry['editorial_stage']=='expanded' and not entry['needs_expansion']
        deck=json.loads((SOURCE_DIR/(entry['id']+'.json')).read_text(encoding='utf8'))
        assert deck['editorial_stage']=='expanded'
        lecture=SOURCE_DIR.parent/deck['source_lecture']
        assert '<!-- BEGIN SPOKEN LECTURE -->' in lecture.read_text(encoding='utf8')
        assert 9<=len(deck['slides'])<=20
        assert len({slide['id'] for slide in deck['slides']})==len(deck['slides'])
        assert sum(bool(s.get('mathtex')) for s in deck['slides'])>=4
        assert sum(bool(s.get('diagram')) for s in deck['slides'])>=4
        for slide in deck['slides']:
            assert slide['title'] and slide['lead'] and len(slide['body'])>=2
            assert len(' '.join([slide['lead'],*slide['body']]).split())>=38
            assert 'first-pass outline' not in slide['eyebrow']
            if kind:=slide.get('diagram'):
                assert companion_figure_kind(kind),(node,kind)


def test_g2_batch3_self_contained_render(tmp_path,monkeypatch):
    from dkvis.presentation import companion_slides as renderer
    monkeypatch.setattr(renderer, 'render_slide_png', lambda deck, slide, index, count, cache_dir=None: b'PNG')
    lib=CompanionSlideLibrary(SOURCE_DIR,tmp_path/'rendered')
    for node in BATCH3_NODES:
        entry=next(e for e in lib.catalog() if node in e['lecture_nodes'])
        result=lib.build(entry['id'])
        html=lib.rendered(entry['id']).read_text(encoding='utf8')
        assert html.count('<section class="slide slide--')==result['slide_count']
        assert 'BASELINE · NEEDS EXPANSION' not in html
        assert 'data:image/png;base64,' in html
        assert '<script src=' not in html


def test_g2_batch3_manifest_promotion_is_idempotent():
    root=Path(__file__).resolve().parents[1]
    proc=subprocess.run([sys.executable,str(root/'tools/promote_g2_046000_053000.py'),'--check'],
                        cwd=root,capture_output=True,text=True)
    assert proc.returncode==0,proc.stderr+proc.stdout


def test_g2_batch3_scope_and_angle_distinctions():
    def slide_text(node):
        deck=next(SOURCE_DIR.glob(f'g2-{node}-*.json'))
        doc=json.loads(deck.read_text(encoding='utf8'))
        return ' '.join(' '.join([s['title'],s['lead'],*s['body']]) for s in doc['slides'])
    acute=slide_text('047000')
    assert 'crossed' in acute and 'right-angle' in acute
    assert 'uniform' in acute and 'infinite' in acute
    matching=slide_text('050000')
    assert 'source defect' in matching and 'target defect' in matching
    cls=slide_text('051000')
    assert 'compact' in cls and 'continuous' in cls
    sv=slide_text('052000')
    assert 'Courant–Fischer' in sv and 'Gram operator' in sv
