"""The population-gap proof, frame alignment, and corrected rectangular extension."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.lectures import lecture_path
from dkvis.quiz import quiz_uses

YWS = DeckSpec(
    name='yws-population-gap',
    description='YWS Theorem 2 with a residual proof, population blocks, alignment, and the corrected singular-subspace extension.',
    footer='Yu–Wang–Samworth: population gap, residual, alignment',
    narration=lecture_path('yws'),
    slides=uses('dkvis.learning.yws.scenes',['YsTitle'])
    + uses('dkvis.learning.outcomes', ['LectureOutcomes'])
    + uses('dkvis.learning.orientation',['YsSetup'])
    + uses('dkvis.learning.yws.scenes',[
        'YsMotivation','YsMixedExample','YsGap','YsGeometry','YsTheorem',
        'YsRoadmap','YsResidual','YsOperatorUpper','YsFrobeniusUpper',
        'YsBlocks','YsLowerIdentity','YsEntrywise','YsCombine','YsAlignment',
        'YsAlignmentProof','YsRotationExample','YsRectangular','YsRectangularGap',
        'YsSummary','YsFacts','YsLean','YsLeanAligned',
    ]) + uses('dkvis.learning.yws.scenes',['YsComputation'],depth='*')
    + quiz_uses(count=4),
)
