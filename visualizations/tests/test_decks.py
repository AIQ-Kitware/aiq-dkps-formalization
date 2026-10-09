"""Deck structure and source existence, not brittle assertions about slide copy."""

import ast
from pathlib import Path

from dkvis.decks import DECKS, get_deck
from dkvis.decks.reference import MODULE_OF, PART_SCENES


EXPECTED_SHORT = [
    "S00TitleShort", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03NoGap", "S03cUnstable", "S04Angle", "S05Residual",
    "S06Gap", "S07Theorem", "S08Why", "S11Payoff", "D01Planes", "S12Lean",
    "P01Claim", "P02Counterexample", "S14Summary",
]

# Freeze the 21-scene presentation's ordering; its content remains free to edit.
COMPLETED_TALK_ORDER = [
    "S00TitleShort", "W00Overview", "W01Workflow", "S01Ellipse", "S02Perturb",
    "S03NoGap", "S03cUnstable", "S04Angle", "S05Residual", "S06Gap",
    "S07Theorem", "S11Payoff", "S12Lean", "P01Claim", "P02Counterexample",
    "P04LeanRefutation", "W02TwoChecks", "W04Reversals", "W06Claims",
    "S14Summary", "V01VTKFinale",
]


def test_reference_short_order_is_preserved():
    assert get_deck("sine-theta-short").scene_names == EXPECTED_SHORT


def test_reference_full_is_exact_part_concatenation():
    expected = [scene for scenes in PART_SCENES.values() for scene in scenes]
    assert get_deck("sine-theta-full").scene_names == expected
    assert list(get_deck("sine-theta-full").composite_parts) == list(PART_SCENES)


def test_decks_have_unique_scene_names_and_real_source_modules():
    root = Path(__file__).resolve().parents[1]
    for deck in DECKS.values():
        assert len(deck.scene_names) == len(set(deck.scene_names))
        for slide in deck.slides:
            source = root / (slide.module.replace(".", "/") + ".py")
            assert source.is_file(), (deck.name, slide.scene, source)
            classes = {node.name for node in ast.parse(source.read_text()).body if isinstance(node, ast.ClassDef)}
            assert slide.scene in classes, (deck.name, slide.scene, source)


def test_completed_talk_is_preserved_under_a_stable_name():
    talk = get_deck("kitware-talk")
    assert talk.scene_names == COMPLETED_TALK_ORDER
    assert all(slide.depth == "" for slide in talk.slides)
    assert "friday" not in DECKS


def test_comprehensive_covers_every_distinct_reference_scene():
    complete = get_deck("comprehensive")
    used = set(complete.scene_names)
    # Original title variants repeat the same art; the long deck has its own
    # broader cover. All distinct mathematical and evidence scenes are present.
    chapters = {
        "C00LongTitle", "C01Foundations", "C02ThreeDimensions",
        "C03TheoremFamily", "C04Proposition", "C05Evidence", "C06Notation",
    }
    assert used == (set(MODULE_OF) - {"S00Title", "S00TitleShort"}) | chapters
    assert len(complete.scene_names) == len(used)
    assert all(slide.depth == "" for slide in complete.slides)


def test_comprehensive_has_a_coherent_topic_progression():
    names = get_deck("comprehensive").scene_names
    chapters = [
        "C01Foundations", "C02ThreeDimensions", "C03TheoremFamily",
        "C04Proposition", "C05Evidence", "C06Notation",
    ]
    assert names[0:2] == ["C00LongTitle", "W00Overview"]
    positions = [names.index(scene) for scene in chapters]
    assert positions == sorted(positions)
    assert names.index("S07Theorem") < names.index("S12Lean") < names.index("D01Planes")
    assert names.index("D04Perturb") < names.index("F01Setup") < names.index("S13Family")
    assert names.index("P02Counterexample") < names.index("P04LeanRefutation") < names.index("W02TwoChecks")
    assert names.index("W06Claims") < names.index("G01Matrices") < names.index("S14Summary")
    assert names[-2:] == ["S14Summary", "V01VTKFinale"]
    assert "V00Manim3DFinale" not in names


def test_deck_depth_is_presentation_specific():
    assert get_deck("part5-process").slide("W01Workflow").depth == "*"
    assert get_deck("kitware-talk").slide("W01Workflow").depth == ""
    assert get_deck("study").slide("P04Details").depth == "**"
    assert get_deck("study").slide("G01Matrices").depth == "**"


def test_study_and_reference_decks_remain_independent():
    study = get_deck("study").scene_names
    assert "P03Why" in study
    assert "F04TanTwoTheta" in study
    assert "V01VTKFinale" not in study
    assert "V01VTKFinale" not in get_deck("sine-theta-short").scene_names
    assert len(study) > len(get_deck("kitware-talk").scene_names)
