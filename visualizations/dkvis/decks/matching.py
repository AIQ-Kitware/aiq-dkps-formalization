"""A separate, detailed walkthrough of the finite real matching theorem."""
from dkvis.deck_spec import DeckSpec, SlideUse

SCENES = [
    "M00Problem", "M01PrincipalPlanes", "M02Singleton", "M03PairedBlock",
    "M04Graph", "M05TwoBounds", "M06SmoothCost", "M07Existence",
    "M08FeasibleCurves", "M09RotationCost", "M10SignAverage", "M11TracePairing",
    "M12Stationarity", "M13TwoDecompositions", "M14GradientLevels",
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
    description="Theorem 5, one inference and justification at a time.",
    footer=r"Real trace-norm matching $\cdot$ proof study",
    slides=tuple(SlideUse("dkvis.slides_matching", name) for name in SCENES),
)
