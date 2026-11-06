"""Standalone historical overview, without technical prerequisite dependencies."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.lectures import lecture_path
from dkvis.quiz import quiz_uses

HISTORY_OVERVIEW = DeckSpec(
    name='history-overview',
    description='People and publications behind subspace geometry, Davis–Kahan, statistics, and transport.',
    footer='Mathematical history: Davis–Kahan and beyond',
    narration=lecture_path('history_overview'),
    slides=uses('dkvis.learning.history.scenes', [
        'HiTitle', 'HiQuestion', 'HiJordan', 'HiSylvester', 'HiRayleighRitz', 'HiWeyl',
        'HiHotelling', 'HiProjectionPeople', 'HiKatoHalmos', 'HiRosenblum',
        'HiDavisKahan', 'HiBound', 'HiWedinGolub', 'HiYws', 'HiQuench',
        'HiNormPeople', 'HiCorrection', 'HiMatching', 'HiEvidence', 'HiSummary',
    ])+quiz_uses(),
)
