"""A compact proof presentation, independent of the matching study deck."""
from dkvis.quiz import quiz_uses
from dkvis.deck_spec import DeckSpec, SlideUse
from dkvis.lectures import lecture_path

SCENES = [
    'T00Statement', 'T01ProofStrategy', 'T02Stationarity',
    'T03TwoPhases', 'T04CommonBlocks', 'T05BlockAccounting',
    'T06LocalFibers', 'T07PhaseRectangle', 'T08EdgeReduction',
    'T09OtherComponents', 'T10MatchingEquality', 'T11TraceEndpoint',
    'T12Attainment',
]

MATCHING_PROOF_TALK = DeckSpec(
    name='matching-proof-talk',
    description='A compact proof of the unrestricted finite real trace-norm matching formula.',
    footer=r'Real trace-norm transport $\cdot$ matching proof',
    narration=lecture_path('matching_proof'),
    slides=tuple(SlideUse('dkvis.learning.matching.talk', name) for name in SCENES) + quiz_uses(),
)
