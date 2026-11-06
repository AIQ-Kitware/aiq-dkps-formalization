"""Trial spaces, their small eigenproblem, and the error it leaves outside."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.quiz import quiz_uses
from dkvis.lectures import lecture_path

RAYLEIGH_RITZ = DeckSpec(
    name='operators-rayleigh-ritz',
    description='Choose a trial space, compress, solve, lift, and interpret Ritz residuals.',
    footer='Rayleigh–Ritz: trial spaces and residuals',
    narration=lecture_path('rayleigh_ritz'),
    slides=uses('dkvis.learning.rayleigh_ritz.scenes',['RrTitle'])
    +uses('dkvis.learning.orientation',['RrSetup'])
    +uses('dkvis.learning.rayleigh_ritz.scenes',[
        'RrQuestion','RrSpace','RrFrame','RrCompress','RrQuotient','RrSolve',
        'RrGeometry','RrExample','RrBlock','RrOrthogonality','RrModel','RrQuality',
        'RrMinmax','RrPaper','RrSummary','RrFacts','RrLean','RrLeanOrthogonal','RrLeanSplit'])
    +uses('dkvis.learning.rayleigh_ritz.scenes',['RrComputation'],depth='*')
    +quiz_uses(count=4),
)
