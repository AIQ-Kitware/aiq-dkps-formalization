"""Guard the small presentation-specific contracts agreed for the Friday deck."""

from pathlib import Path
import xml.etree.ElementTree as ET

from dkvis.decks import get_deck


ROOT = Path(__file__).resolve().parents[1]


def source(name):
    return (ROOT / 'dkvis' / name).read_text()


def test_friday_order_and_new_refutation_statement():
    names = get_deck('friday').scene_names
    assert 'S08Why' not in names
    assert names.index('P01Claim') < names.index('P02Counterexample')
    assert 'P03Why' not in names  # Keep the chord-curve explanation for study only.
    assert 'P03Why' in get_deck('study').scene_names
    assert names.index('P02Counterexample') < names.index('P04LeanRefutation')
    assert names.index('P04LeanRefutation') < names.index('W02TwoChecks')
    assert names.index('W02TwoChecks') < names.index('W04Reversals')
    assert names.index('W04Reversals') < names.index('W06Claims')


def test_robot_is_svg_and_disclosure_is_title_only():
    icon = ROOT / 'dkvis/assets/robot.svg'
    assert ET.parse(icon).getroot().tag == '{http://www.w3.org/2000/svg}svg'
    sine = source('slides_sine_theta.py')
    process = source('slides_process.py')
    prop44 = source('slides_prop44.py')
    assert 'SVGMobject(' in sine
    assert 'Slides prepared with LLM assistance.' in sine
    assert 'Slides prepared with LLM assistance.' not in process
    assert 'Slides prepared with LLM assistance.' not in prop44
    assert '🤖' not in sine  # Tex must never receive the Unicode emoji.


def test_theorem_is_anchored_to_real_lean_declarations():
    prop44 = source('slides_prop44.py')
    lean = (ROOT.parent / 'DavisKahan/FiniteDimensional/DirectRotation/'
            'ShortRotationCounterexample.lean').read_text()
    for declaration in ('shortRotation_fullDisplacement_refuted',
                        'not_davisKahanProposition4_4_Finite'):
        assert declaration in prop44
        assert f'theorem {declaration}' in lean
    assert 'kyFanSum 4 (LinearMap.id - W.toLinearMap) <' in prop44
    assert '¬ DavisKahanProposition4_4_Finite.{0}' in prop44


def test_slides_avoid_old_clutter_and_note_telemetry_limits():
    sine = source('slides_sine_theta.py')
    process = source('slides_process.py')
    assert 'one column here' not in sine
    assert 'not an error rate' not in process
    assert 'measured error rate' not in process
    assert 'many commits retain token telemetry' in process
    assert 'telemetry is absent from many commits' in process
    assert 'self.play(FadeIn(moral))' not in process.split('class W06Claims(DeckSlide):')[1]
    assert 'https://mathoverflow.net/a/513567' in process


def test_prop44_counterexample_explains_and_compares_displacement_norms():
    source_text = source('slides_prop44.py')
    counterexample = source_text.split('class P02Counterexample(P4Slide):')[1].split('class P03Why(P4Slide):')[0]
    claim = source_text.split('class P01Claim(P4Slide):')[1].split('class P02Counterexample(P4Slide):')[0]
    assert r'A \emph{norm} turns $I-W$' in claim
    assert r'\norm{I-\mathcal R}' in counterexample
    assert r'\norm{I-W}' in counterexample
    assert 'Norm choice matters: the trace norm refutes the claim' in counterexample
    assert 'standard axioms only' not in counterexample
    assert 'less motion' not in counterexample
    assert 'failure_outline' in counterexample
