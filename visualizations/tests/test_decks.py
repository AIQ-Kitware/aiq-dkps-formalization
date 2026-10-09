import ast
from pathlib import Path

from dkvis.decks import DECKS, get_deck
from dkvis.decks.reference import PART_SCENES
from dkvis.notation import SYMBOLS


EXPECTED_SHORT = [
    "S00TitleShort", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03NoGap", "S03cUnstable", "S04Angle", "S05Residual",
    "S06Gap", "S07Theorem", "S08Why", "S11Payoff", "D01Planes", "S12Lean",
    "P01Claim", "P02Counterexample", "S14Summary",
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


def test_depth_is_presentation_specific():
    # Same reusable component: optional in the preserved process part, core in
    # the Friday story where the workflow is part of the main argument.
    assert get_deck("part5-process").slide("W01Workflow").depth == "*"
    assert get_deck("friday").slide("W01Workflow").depth == ""

    # Raw matrices and glossary remain backup material in the learning deck.
    assert get_deck("study").slide("P04Details").depth == "**"
    assert get_deck("study").slide("G01Matrices").depth == "**"


def test_working_decks_have_distinct_purposes():
    friday = get_deck("friday").scene_names
    study = get_deck("study").scene_names
    assert friday[:3] == ["S00TitleShort", "W00Overview", "W01Workflow"]
    assert "W02TwoChecks" in friday
    assert friday[-2:] == ["S14Summary", "V01VTKFinale"]
    assert "V01VTKFinale" not in study
    assert "V01VTKFinale" not in get_deck("sine-theta-short").scene_names
    assert "P02Counterexample" in friday
    assert "F04TanTwoTheta" not in friday
    assert "F04TanTwoTheta" in study
    # Friday states the general theorem and reconnects it to A + H, then
    # presents Proposition 4.4 before the source-audit retrospective.
    assert friday.index("S07Theorem") < friday.index("S11Payoff") < friday.index("S12Lean")
    assert "S08Why" not in friday
    assert "P03Why" not in friday
    assert "P03Why" in study
    assert friday.index("P02Counterexample") < friday.index("P04LeanRefutation") < friday.index("W02TwoChecks")
    assert friday.index("W02TwoChecks") < friday.index("W04Reversals") < friday.index("W06Claims")
    assert len(study) > len(friday)


def test_sine_theta_notation_contract():
    root = Path(__file__).resolve().parents[1]
    source = (root / "dkvis/slides_sine_theta.py").read_text()

    assert SYMBOLS["Ahat"][0] == r"\widehat A"
    assert r"\sym{At}" not in source
    # The core sine-theta exposition operates on frames directly.  U/V remain
    # available for genuinely local statements such as Proposition 4.4.
    assert r"\sym{U}" not in source
    assert r"\sym{V}" not in source

    friday = get_deck("friday").scene_names
    assert friday.index("S07Theorem") < friday.index("S11Payoff")
