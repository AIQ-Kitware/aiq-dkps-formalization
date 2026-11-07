"""Independent lessons: local setup, core facts, optional computation, review."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.quiz import quiz_uses
from dkvis.lectures import lecture_path, lecture_decks


BASICS = DeckSpec(
    name='prereq-basics', description='A short review of the linear algebra, geometry, and calculus assumed by the series.',
    footer='Before the Series: Foundations', narration=lecture_path('basics'),
    slides=uses('dkvis.learning.basics.scenes', ['BaTitle'])
    + uses('dkvis.learning.orientation', ['BaSetup'])
    + uses('dkvis.learning.basics.scenes', [
        'BaNumbers', 'BaMatrices', 'BaSpaces', 'BaInner', 'BaAdjoints',
        'BaTrig', 'BaEigen', 'BaMeasurements', 'BaLimits', 'BaDerivative',
        'BaIntegral', 'BaRecap', 'BaFacts', 'BaLean', 'BaLeanMinimum',
    ])
    + uses('dkvis.learning.basics.scenes', ['BaComputation'], depth='*')
    + quiz_uses(),
)


PROJECTIONS = DeckSpec(
    name='prereq-projections', description='From nearest points to subspace projections, frames, and commuting blocks.',
    footer='subspaces and projections', narration=lecture_path('projections'),
    slides=uses('dkvis.learning.projections.scenes', ['PrTitle'])
    + uses('dkvis.learning.orientation', ['PrSetup'])
    + uses('dkvis.learning.projections.scenes', [
        'Pr00Question', 'Pr01History', 'Pr02Decomposition', 'Pr03Projector',
        'Pr04Frames', 'Pr05Blocks', 'Pr06Commutation', 'Pr07Transport',
        'Pr08Recap', 'PrFacts', 'PrLean', 'PrLeanBlocks',
    ])
    + uses('dkvis.learning.projections.scenes', ['PrComputation'], depth="*")
    + quiz_uses(),
)

COMPLEMENTARY_PROJECTION = DeckSpec(
    name='prereq-complementary-projection',
    description='Read I minus P as a complementary projection, projection error, and restricted sine block.',
    footer='Thinking about I minus P', narration=lecture_path('complementary_projection'),
    slides=uses('dkvis.learning.complementary_projection.scenes', ['CpTitle'])
    + uses('dkvis.learning.orientation', ['CpSetup'])
    + uses('dkvis.learning.complementary_projection.scenes', [
        'CpQuestion', 'CpSplit', 'CpKeep', 'CpAngle', 'CpRestricted',
        'CpSineBlock', 'CpDisplacement', 'CpSummary', 'CpFacts',
        'CpLeanOperator', 'CpLeanError',
    ])
    + uses('dkvis.learning.complementary_projection.scenes', ['CpComputation'], depth='*')
    + quiz_uses(),
)

SINGULAR_NORMS = DeckSpec(
    name='prereq-singular-norms', description='Singular values explain displacement costs, norm choice, and block additivity.',
    footer='singular values and displacement cost', narration=lecture_path('singular_norms'),
    slides=uses('dkvis.learning.singular_norms.scenes', ['SnTitle'])
    + uses('dkvis.learning.orientation', ['SnSetup'])
    + uses('dkvis.learning.singular_norms.scenes', [
        'Sn00Question', 'Sn01History', 'Sn02Stretching', 'Sn03Norms',
        'Sn04Invariance', 'Sn05Rotation', 'Sn06SmoothCost', 'Sn07BlockCosts',
        'Sn08Restrictions', 'Sn09Recap', 'SnFacts', 'SnLean',
        'SnLeanCoordinates',
    ])
    + uses('dkvis.learning.singular_norms.scenes', ['SnComputation'], depth="*")
    + quiz_uses(),
)

MATRIX_EXPONENTIAL = DeckSpec(
    name='prereq-matrix-exponential', description='From a matrix velocity to its exact flow: series, small steps, examples, and orthogonality.',
    footer='the matrix exponential', narration=lecture_path('matrix_exponential'),
    slides=uses('dkvis.learning.matrix_exponential.scenes', ['ExTitle'])
    + uses('dkvis.learning.orientation', ['ExSetup'])
    + uses('dkvis.learning.matrix_exponential.scenes', [
        'Ex00Question', 'Ex01History', 'Ex02Series', 'Ex03SmallSteps',
        'Ex04Dynamics', 'Ex05Diagonal', 'Ex06Shear', 'Ex07Rotation',
        'Ex08Laws', 'Ex09Noncommuting', 'Ex10Orthogonal', 'Ex11SourcePreservation',
        'Ex12Recap', 'ExFacts', 'ExLean', 'ExLeanLengths',
        'ExLeanSplit',
    ])
    + uses('dkvis.learning.matrix_exponential.scenes', ['ExComputation'], depth="*")
    + quiz_uses(),
)

VARIATIONS = DeckSpec(
    name='prereq-variations', description='Construct constraint-preserving curves and use stationarity to test a minimizer.',
    footer='feasible variations and stationarity', narration=lecture_path('variations'),
    slides=uses('dkvis.learning.variations.scenes', ['VaTitle'])
    + uses('dkvis.learning.orientation', ['VaSetup'])
    + uses('dkvis.learning.variations.scenes', [
        'Va00Question', 'Va01History', 'Va02Velocity', 'Va03Exponential',
        'Va04SourceMotion', 'Va05Feasible', 'Va06Stationarity', 'Va07Gradient',
        'Va08Test', 'Va09Structure', 'Va10Recap', 'VaFacts',
        'VaLean', 'VaLeanTrace',
    ])
    + uses('dkvis.learning.variations.scenes', ['VaComputation'], depth="*")
    + quiz_uses(),
)

_BY_NAME = {d.name: d for d in (BASICS, PROJECTIONS, COMPLEMENTARY_PROJECTION, SINGULAR_NORMS, MATRIX_EXPONENTIAL, VARIATIONS)}
PREREQUISITES = tuple(_BY_NAME[name] for name in lecture_decks("prerequisites"))
