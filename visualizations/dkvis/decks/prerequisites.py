"""Independent short prerequisite lectures; existing talks remain unchanged."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.quiz import quiz_uses
from dkvis.lectures import lecture_path, lecture_decks


PROJECTIONS = DeckSpec(
    name='prereq-projections',
    description='From nearest points to subspace projections, frames, and commuting blocks.',
    footer=r'subspaces and projections',
    narration=lecture_path('projections'),
    slides=uses('dkvis.learning.projections.scenes', [
        'PrTitle',
        'Pr00Question', 'Pr01History', 'Pr02Decomposition', 'Pr03Projector',
        'Pr04Frames', 'Pr05Blocks', 'Pr06Commutation', 'Pr07Transport', 'Pr08Recap',
        'PrComputation', 'PrFacts', 'PrLean',
    ]) + quiz_uses(),
)

SINGULAR_NORMS = DeckSpec(
    name='prereq-singular-norms',
    description='Singular values explain displacement costs, norm choice, and block additivity.',
    footer=r'singular values and displacement cost',
    narration=lecture_path('singular_norms'),
    slides=uses('dkvis.learning.singular_norms.scenes', [
        'SnTitle',
        'Sn00Question', 'Sn01History', 'Sn02Stretching', 'Sn03Norms',
        'Sn04Invariance', 'Sn05Rotation', 'Sn06SmoothCost', 'Sn07BlockCosts',
        'Sn08Restrictions', 'Sn09Recap',
        'SnComputation', 'SnFacts', 'SnLean',
    ]) + quiz_uses(),
)

MATRIX_EXPONENTIAL = DeckSpec(
    name='prereq-matrix-exponential',
    description='From a matrix velocity to its exact flow: series, small steps, examples, and orthogonality.',
    footer=r'the matrix exponential',
    narration=lecture_path('matrix_exponential'),
    slides=uses('dkvis.learning.matrix_exponential.scenes', [
        'ExTitle',
        'Ex00Question', 'Ex01History', 'Ex02Series', 'Ex03SmallSteps',
        'Ex04Dynamics', 'Ex05Diagonal', 'Ex06Shear', 'Ex07Rotation',
        'Ex08Laws', 'Ex09Noncommuting', 'Ex10Orthogonal',
        'Ex11SourcePreservation', 'Ex12Recap',
        'ExComputation', 'ExFacts', 'ExLean',
    ]) + quiz_uses(),
)

VARIATIONS = DeckSpec(
    name='prereq-variations',
    description='Construct constraint-preserving curves and use stationarity to test a minimizer.',
    footer=r'feasible variations and stationarity',
    narration=lecture_path('variations'),
    slides=uses('dkvis.learning.variations.scenes', [
        'VaTitle',
        'Va00Question', 'Va01History', 'Va02Velocity', 'Va03Exponential',
        'Va04SourceMotion', 'Va05Feasible', 'Va06Stationarity',
        'Va07Gradient', 'Va08Test', 'Va09Structure', 'Va10Recap',
        'VaComputation', 'VaFacts', 'VaLean',
    ]) + quiz_uses(),
)

# The YAML prerequisite graph owns course membership and teaching order.
_BY_NAME = {d.name: d for d in (PROJECTIONS, SINGULAR_NORMS, MATRIX_EXPONENTIAL, VARIATIONS)}
PREREQUISITES = tuple(_BY_NAME[name] for name in lecture_decks('prerequisites'))
