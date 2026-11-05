"""A separate, detailed walkthrough of the finite real matching theorem."""
from dkvis.quiz import quiz_uses
from dkvis.deck_spec import DeckSpec, SlideUse, uses
from dkvis.lectures import lecture_path

SCENES = [
    "M00Problem", "M00BlockMeaning", "M01PrincipalPlanes", "M02Singleton", "M03PairedBlock",
    "M04Graph", "M05TwoBounds", "M06SmoothCost", "M07Existence",
    "M08FeasibleCurves", "M08ProjectionMeaning", "M08CommutingConstruction", "M08StationaryTests",
    "M09RotationCost", "M10SignAverage", "M11TracePairing",
    "M12Stationarity", "M13TwoDecompositions", "M13InvariantBlocks", "M14GradientLevels",
    "M15ComplexCoordinates", "M16TwoPhases", "M17ProjectionBlocks",
    "M18RealBlocks", "M19ZeroGradient", "M20PairCoordinates",
    "M20PhaseParameters", "M20PhasePolynomial", "M20RectangleBounds",
    "M21PhaseRectangle", "M22PairMinimum", "M23Determinants",
    "M24BlockOptimality", "M25MatchingEquality", "M26ZeroAngles",
    "M27UniformLimit", "M28EndpointWeights", "M29MatchingAlgorithm",
    "M30WorkedExample", "M31Rehearsal",
]

MATCHING_PROOF = DeckSpec(
    name="matching-proof",
    description="Learn why the matching proof works: geometry, legal variations, and invariant blocks.",
    footer=r"Real trace-norm matching $\cdot$ proof study",
    narration=lecture_path('matching_study'),
    slides=uses('dkvis.learning.matching.study', ['MTitle'])
    + uses('dkvis.learning.orientation', ['M00Setup'])
    + tuple(SlideUse("dkvis.learning.matching.study", name) for name in SCENES)
    + uses('dkvis.learning.matching.bonus', ['MatchingComputation'], depth='*') + quiz_uses(),
)
