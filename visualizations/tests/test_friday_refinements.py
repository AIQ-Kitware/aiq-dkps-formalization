"""Guard the small presentation-specific contracts agreed for the Friday deck."""

from pathlib import Path
import ast
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
    assert names[-2:] == ['S14Summary', 'V01VTKFinale']


def test_friday_overview_is_source_oriented_and_unique_to_friday():
    friday = get_deck('friday').scene_names
    assert friday[:3] == ['S00TitleShort', 'W00Overview', 'W01Workflow']
    assert 'W00Overview' not in get_deck('study').scene_names
    assert 'W00Overview' not in get_deck('sine-theta-short').scene_names
    overview = source('slides_process.py').split('class W00Overview(DeckSlide):')[1].split('class W01Workflow(DeckSlide):')[0]
    for phrase in ('Davis', '1970', 'DARPA AIQ', 'July--August', 'Semantic alignment:',
                   'Palomar formalization', 'TauCetiRoadmap', 'Hilbert-space operator-theory',
                   'self.add(', 'self.say('):
        assert phrase in overview
    assert r'\sym{delta}' in overview
    assert r'\sym{sinTheta0}' in overview
    assert 'FadeIn(' not in overview  # Overview is fully visible, without staged decoration.
    assert 'CHALLENGES' in overview
    assert 'DEVELOPMENTS: CLASSICAL OPERATOR THEORY' in overview
    assert 'Six prerequisite theory areas' in overview
    assert 'WHAT THE FOUNDATIONS ENABLE' in overview
    assert 'Mathematical research in functional analysis' in overview
    assert 'Jan--Feb:' in overview
    assert 'June:' in overview
    assert 'July--August:' in overview
    assert 'Agent orchestration:' in overview


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
    qnorm = (ROOT.parent / 'DavisKahan/FiniteDimensional/DirectRotation/'
             'QNorm.lean').read_text()
    for declaration in ('shortRotation_fullDisplacement_refuted',
                        'not_davisKahanProposition4_4_Finite'):
        assert declaration in prop44
        assert f'theorem {declaration}' in lean
    assert 'theorem directRotation_fullDisplacement_qnorm' in qnorm
    assert 'QNORM_SOURCE' in prop44
    assert '_lean_statement(' in prop44
    assert '(hN : IsQNorm N)' in qnorm
    assert 'literal Lean' in prop44 or 'LITERAL LEAN' in prop44
    # The counterexample displays numbers only; repair discussion belongs on
    # the next Lean slide, rather than repeated in the comparison animation.
    counterexample = prop44.split('class P02Counterexample(P4Slide):')[1].split('class P03Why(P4Slide):')[0]
    assert 'directRotation_fullDisplacement_qnorm' not in counterexample
    assert 'lean = VGroup' not in counterexample


def test_literal_prop44_theorem_headers_are_extractable_from_source():
    """Exercise the exact-source reader without importing optional Manim."""
    module_ast = ast.parse(source('slides_prop44.py'))
    func = next(node for node in module_ast.body
                if isinstance(node, ast.FunctionDef) and node.name == '_lean_statement')
    namespace = {'Path': Path}
    exec(compile(ast.Module(body=[func], type_ignores=[]), '<lean-excerpt>', 'exec'), namespace)
    excerpt = namespace['_lean_statement']
    dk = ROOT.parent / 'DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean'
    qn = ROOT.parent / 'DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean'
    witness = excerpt(dk, 'shortRotation_fullDisplacement_refuted', include_witness=True)
    assert witness[0] == 'theorem shortRotation_fullDisplacement_refuted :'
    assert 'kyFanSum 4 (LinearMap.id - W.toLinearMap) <' in '\n'.join(witness)
    assert 'principalAngles U V 0 ≤ Real.pi / 3' in '\n'.join(witness)
    assert witness[-1].strip().startswith('⟨U4, V4, acute, Wequiv')
    negation = excerpt(dk, 'not_davisKahanProposition4_4_Finite')
    assert negation == ['theorem not_davisKahanProposition4_4_Finite :',
                        '    ¬ DavisKahanProposition4_4_Finite.{0} := by']
    repair = excerpt(qn, 'directRotation_fullDisplacement_qnorm')
    assert repair[0] == 'theorem directRotation_fullDisplacement_qnorm'
    assert any('(hN : IsQNorm N)' in line for line in repair)
    assert repair[-1].rstrip().endswith(':= by')


def test_takeaways_state_count_intuition_and_limited_counterexample_scope():
    section = source('slides_sine_theta.py').split('class S14Summary(DeckSlide):')[1].split('SCENES = [')[0]
    assert r'All \textbf{29}' in section
    assert r'\textbf{28 proved}' in section
    assert 'Hilbert-space functional analysis' in section
    assert 'subspace error is bounded by residual over separation' in section
    assert 'unobserved' in section
    assert 'LLM-assisted review found a counterexample' in section
    assert 'for acute pairs' in section
    assert '$Q$-norms' in section
    assert r"without the source's $60^\circ$ cutoff" in section


def test_vtk_finale_reuses_project_renderer_without_replacing_summary():
    names = get_deck('friday').scene_names
    assert names[-2:] == ['S14Summary', 'V01VTKFinale']
    assert 'V01VTKFinale' not in get_deck('study').scene_names
    assert 'V01VTKFinale' not in get_deck('sine-theta-short').scene_names
    vtk = source('slides_vtk_finale.py')
    assert 'vtk_sine_theta_3d' in vtk
    assert 'vtk3d.write_still' in vtk
    assert 'vtk3d.write_movie' in vtk
    assert 'loop=True' in vtk
    assert 'finale-tilt.mp4' in vtk


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
