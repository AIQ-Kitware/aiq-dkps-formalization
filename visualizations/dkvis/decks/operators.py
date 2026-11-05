"""Operator-roadmap foundations accepted into Tau Ceti."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.lectures import lecture_path
from dkvis.quiz import quiz_uses

MINMAX = DeckSpec(
    name='operators-minmax', description='Rayleigh quotients, the two min-max inequalities, and Weyl stability.',
    footer='Rayleigh quotients and eigenvalue stability', narration=lecture_path('minmax'),
    slides=uses('dkvis.learning.operators.minmax', ['MmTitle', 'MmQuestion', 'MmRayleigh',
        'MmMinMax', 'MmWeyl', 'MmSummary', 'MmComputation', 'MmFacts', 'MmLean']) + quiz_uses())
POLAR = DeckSpec(
    name='operators-polar', description='Separate stretching from motion, including the singular and Hilbert-space cases.',
    footer='Operator absolute value and polar decomposition', narration=lecture_path('polar'),
    slides=uses('dkvis.learning.operators.polar', ['PoTitle', 'PoQuestion', 'PoModulus',
        'PoKernel', 'PoExample', 'PoSummary', 'PoComputation', 'PoFacts', 'PoLean']) + quiz_uses())
SYLVESTER = DeckSpec(
    name='operators-sylvester', description='Solve AX-XB=R and understand exactly what a spectral gap controls.',
    footer='Sylvester equations and spectral separation', narration=lecture_path('sylvester'),
    slides=uses('dkvis.learning.operators.sylvester', ['SyTitle', 'SyQuestion', 'SyEntries',
        'SyGap', 'SyExample', 'SySummary', 'SyComputation', 'SyFacts', 'SyLean']) + quiz_uses())
OPERATORS = (MINMAX, POLAR, SYLVESTER)
