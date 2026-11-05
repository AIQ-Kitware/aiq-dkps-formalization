"""Independent lessons: local setup, core facts, optional computation, review."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.quiz import quiz_uses
from dkvis.lectures import lecture_path, lecture_decks


MINMAX = DeckSpec(
    name='operators-minmax', description='Rayleigh quotients, the two min-max inequalities, and Weyl stability.',
    footer='Rayleigh quotients and eigenvalue stability', narration=lecture_path('minmax'),
    slides=uses('dkvis.learning.operators.minmax', ['MmTitle'])
    + uses('dkvis.learning.orientation', ['MmSetup'])
    + uses('dkvis.learning.operators.minmax', [
        'MmQuestion', 'MmRayleigh', 'MmMinMax', 'MmWeyl',
        'MmSummary', 'MmFacts', 'MmLean', 'MmLeanWeyl',
    ])
    + uses('dkvis.learning.operators.minmax', ['MmComputation'], depth="*")
    + quiz_uses(),
)

POLAR = DeckSpec(
    name='operators-polar', description='Separate stretching from motion, including the singular and Hilbert-space cases.',
    footer='Operator absolute value and polar decomposition', narration=lecture_path('polar'),
    slides=uses('dkvis.learning.operators.polar', ['PoTitle'])
    + uses('dkvis.learning.orientation', ['PoSetup'])
    + uses('dkvis.learning.operators.polar', [
        'PoQuestion', 'PoModulus', 'PoKernel', 'PoExample',
        'PoSummary', 'PoFacts', 'PoLean', 'PoLeanSupport',
    ])
    + uses('dkvis.learning.operators.polar', ['PoComputation'], depth="*")
    + quiz_uses(),
)

SYLVESTER = DeckSpec(
    name='operators-sylvester', description='Solve AX-XB=R and understand exactly what a spectral gap controls.',
    footer='Sylvester equations and spectral separation', narration=lecture_path('sylvester'),
    slides=uses('dkvis.learning.operators.sylvester', ['SyTitle'])
    + uses('dkvis.learning.orientation', ['SySetup'])
    + uses('dkvis.learning.operators.sylvester', [
        'SyQuestion', 'SyEntries', 'SyGap', 'SyExample',
        'SySummary', 'SyFacts', 'SyLean', 'SyLeanGap',
    ])
    + uses('dkvis.learning.operators.sylvester', ['SyComputation'], depth="*")
    + quiz_uses(),
)

_BY_NAME = {d.name: d for d in (MINMAX, POLAR, SYLVESTER)}
OPERATORS = tuple(_BY_NAME[name] for name in lecture_decks("operators"))
