"""A standalone introduction to projection-valued measures."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.quiz import quiz_uses
from dkvis.lectures import lecture_path

PVM=DeckSpec(name='operators-pvm',description='Spectral selection, scalar energy measures, integration, and unbounded domains.',
    footer='Projection-valued measures',narration=lecture_path('pvm'),
    slides=uses('dkvis.learning.pvm.scenes',['PvTitle'])
    + uses('dkvis.learning.outcomes', ['LectureOutcomes'])
    +uses('dkvis.learning.orientation',['PvSetup'])
    +uses('dkvis.learning.pvm.scenes',[
        'PvQuestion','PvWindow','PvMatrix','PvLaws','PvCountable','PvMass','PvIntegral',
        'PvContinuous','PvStrong','PvUnbounded','PvCutoff','PvDk','PvSummary','PvFacts',
        'PvLean','PvLeanComplement','PvLeanMass'])
    +uses('dkvis.learning.pvm.scenes',['PvComputation'],depth='*')+quiz_uses(count=4))
