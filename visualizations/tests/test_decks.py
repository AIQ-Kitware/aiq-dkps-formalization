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


NOVELTY_TOUR_ORDER = [
    "N00Title",
    "N01ThreeStories",
    "N02OptimizationProblem",
    "N03LowerBound",
    "N04ComplexTrace",
    "N05SmoothedTransport",
    "N06SmoothedStability",
    "N06CriticalFlatness",
    "N07SchattenTransition",
    "N07GlobalSchatten",
    "N07NoMixingProof",
    "N07OptimizerChoices",
    "N07MultiplicityFamilies",
    "N07LocalGlobal",
    "N08ComplexVsReal",
    "N08NuclearMatching",
    "N08MatchingGraph",
    "N08MatchingReduction",
    "N08NuclearParity",
    "N08NuclearCanonical",
    "N08NuclearCorrection",
    "N08CommutingCorrection",
    "N08NumericalCorrection",
    "N09StatusBoard",
]

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


def test_novelty_tour_order_is_preserved():
    assert get_deck("novelty-tour").scene_names == NOVELTY_TOUR_ORDER


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
    matching = {"N08NuclearMatching", "N08MatchingGraph", "N08MatchingReduction"}
    assert used == matching | (set(MODULE_OF) - {"S00Title", "S00TitleShort"}) | chapters
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
    matching_progression = [
        "P04LeanRefutation", "N08NuclearMatching", "N08MatchingGraph",
        "N08MatchingReduction", "C05Evidence",
    ]
    positions = [names.index(scene) for scene in matching_progression]
    assert positions == sorted(positions)
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


def test_indexed_lectures_have_two_answerable_review_scenes_and_thinking_time():
    from dkvis.lectures import lecture_decks
    from dkvis.presentation.narration import read_deck_narration
    from dkvis.quiz import SCENES, questions
    for name in lecture_decks():
        assert get_deck(name).scene_names[-2:] == list(SCENES)
        scripts = read_deck_narration(name)
        for scene, question in zip(SCENES, questions(name)):
            script = scripts[scene]
            assert len(script.beats) == 2
            assert script.pauses == (question['think_seconds'], 0)
            assert 3 <= len(question['choices']) <= 4
            assert 0 <= question['correct'] < len(question['choices'])
            assert question['explanation'].strip()


def test_numbered_public_names_leave_deck_and_cache_names_stable():
    from dkvis.lectures import lecture_decks, lecture_number, lecture_output_name
    from dkvis.presentation.build import output_name
    for name in lecture_decks():
        number = lecture_number(name)
        assert len(number) == 6 and number.isdigit()
        assert lecture_output_name(name) == f'{number}_{name}'
        assert not output_name(name).startswith(number)
    assert lecture_output_name('kitware-talk') == 'kitware-talk'


def test_existing_public_exports_are_numbered_without_moving_caches(tmp_path):
    from dkvis.lectures import lecture_output_name, number_outputs
    deck = 'prereq-projections'
    files = [f'{deck}.kokoro.narrated.mp4', f'{deck}-light.handout.pdf',
             f'999999_{deck}.standalone.html']
    for name in files:
        (tmp_path/name).write_bytes(name.encode())
    cache = tmp_path/f'{deck}-narrated'
    cache.mkdir()
    (cache/'speech.wav').write_bytes(b'cached speech')
    rows = {'projections': {'deck': deck}}
    number_outputs(rows, tmp_path)
    for name in files:
        bare = name.removeprefix('999999_')
        target = tmp_path/(lecture_output_name(deck)+bare[len(deck):])
        assert target.read_bytes() == name.encode()
        assert not (tmp_path/name).exists()
    number_outputs(rows, tmp_path)  # Reapplying preserves outputs and caches.
    assert (cache/'speech.wav').read_bytes() == b'cached speech'


def test_each_indexed_lecture_introduces_local_objects_and_separates_numerics():
    from dkvis.lectures import lecture_decks
    for name in lecture_decks():
        slides = get_deck(name).slides
        setups = [i for i, s in enumerate(slides) if s.module == 'dkvis.learning.orientation']
        assert setups == [1]
        bonus = [i for i, s in enumerate(slides) if s.scene.endswith('Computation')]
        assert bonus == [len(slides)-3]
        assert slides[bonus[0]].depth == '*'
        assert all(i < bonus[0] for i, s in enumerate(slides) if 'Lean' in s.scene)
