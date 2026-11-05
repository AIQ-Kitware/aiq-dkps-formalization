"""Source-preserving code rendering and one-card-per-fact lecture structure."""
from html.parser import HTMLParser
import importlib

import pytest

pytest.importorskip('manim')
from dkvis.components.lean_code import lean_markup
from dkvis.decks import get_deck
from dkvis.lectures import lecture_decks
from dkvis.slide_style import GAP, RESID


class PlainText(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts = []

    def handle_data(self, data):
        self.parts.append(data)


@pytest.mark.parametrize('source', [
    'example (x : E) : P x = x :=\n  projection_fact x',
    'variable (p : ℝ≥0∞)\n-- <tag> & comments\n#check (fun x ↦ x)',
    '⨆ V : Submodule ℝ E, ⨅ x ∈ V, ‖x‖ ≤ 1\n',
])
def test_syntax_colors_preserve_the_actual_lean_source(source):
    reader = PlainText()
    reader.feed(lean_markup(source))
    assert ''.join(reader.parts) == source


def test_keyword_and_library_proof_highlights_are_distinct():
    assert f'foreground="{GAP}"' in lean_markup('example : True := by trivial')
    assert f'foreground="{RESID}"' in lean_markup('  library_fact x', proof=True)


def test_each_lean_fact_has_its_own_card():
    for name in lecture_decks():
        cards = [s for s in get_deck(name).slides if 'Lean' in s.scene]
        if not cards:
            continue
        classes = [getattr(importlib.import_module(s.module), s.scene) for s in cards]
        assert [c.fact_index for c in classes] == list(range(len(classes)))
        assert len(classes) == len(classes[0].symbolic_facts)


def test_cover_credit_preserves_recorded_models_and_unknown_variants(monkeypatch):
    from dkvis.components import llm_credit
    data={'slides':{'initial_source_attribution':[{'models':['Model A (variant high)']}]},
          'transcript':{'initial_source_attribution':[{'models':['Model B (exact configuration unknown)']}]}}
    monkeypatch.setattr(llm_credit,'source_provenance',lambda deck:data)
    label,uncertain=llm_credit.credit_text('example')
    assert 'Model A (variant high)' in label and 'Model B' in label and uncertain
    data['transcript']={'initial_source_attribution':[{'models':['Model C']}],
                        'revisions':[{'models':['Model C']}]}
    label,uncertain=llm_credit.credit_text('example')
    assert label.count('Model C')==1 and not uncertain
