# Principal angles — comparing whole subspaces

## PaTitle: Principal angles between subspaces

Why: Compare whole spaces rather than arbitrary basis arrows.
Recall: Projections, orthonormal frames, and singular values.

Principal angles between subspaces.

## LectureOutcomes: Three ways to read the same geometry

Why: State the destination before the SVD.
Recall: Equal-dimensional subspaces in a finite real inner product space.

Principal angles compare subspaces independently of the bases chosen. The singular values of the frame overlap are the cosines of those angles. The largest sine measures the worst perpendicular error of a unit input. We will begin with lines, then see why a plane needs more than one angle. The matrix calculation will describe that geometry, rather than replace it.

## PaSetup: The spaces, frames, and angle list

Why: Fix the local setting and explain the objects.
Recall: The opening conclusions describe what we will establish.

K and L are real subspaces of the same dimension k. Q and Z are matrices with orthonormal columns spanning those spaces. Multiplying by Q makes an actual vector from k coordinates. Multiplying by Z transpose reads its projection coordinates in L. The geometric principal angles will be ordered from smallest to largest and lie between zero and a right angle. Projection onto L is written P sub L. These names distinguish spaces, coordinates, and measurements of their disagreement.

## PaLines: A line has no preferred arrow direction

Why: Explain the absolute value in the angle.
Recall: Unit vectors u and v span two lines.

Two arrows can span exactly the same line while pointing in opposite directions. Their ordinary vector angle would be a straight angle, but their line angle should be zero. We therefore use the absolute value of their inner product and take an angle between zero and a right angle. Camille Jordan’s nineteenth-century subspace geometry extends this comparison beyond one pair of lines. The next question is what remains of this idea for several dimensions.

<!-- beat -->

The amber arrow now changes sign. The line has not moved. A useful subspace comparison must ignore that sign change, and more generally must ignore rotations of a basis within the same space.

## PaSeveral: Two directions can disagree by different amounts

Why: Motivate an angle list.
Recall: Example: two two-dimensional spaces inside four-dimensional space.

In this example, K is spanned by the first two coordinate vectors. L uses one direction tilted through alpha toward the third coordinate, and another tilted through beta toward the fourth. The left diagram shows the first coordinate plane; the right shows the second. These are two different slices of the same four-dimensional example. There is no single tilt that captures both disagreements.

<!-- beat -->

The first tilt stays at twenty degrees while the second increases. One shared label such as the average angle would hide the changing worst direction. Principal angles retain a list. Common directions contribute zero angles, and perpendicular paired directions contribute right angles.

## PaOverlap: Read agreement in the other frame

Why: Explain why the overlap matrix appears.
Recall: Q and Z have orthonormal columns spanning K and L.

A vector in K has the form Q a. Its coordinates after projecting toward L are Z transpose Q a. So the overlap matrix measures which unit combinations in K align well with L. Its largest singular value gives the strongest alignment. Further singular directions give the remaining perpendicular pairs. Write the overlap as U C V transpose. Then Q V and Z U are new frames in which corresponding directions have inner product c j and cross-pair inner products vanish.

## PaError: The missed component supplies the sine

Why: Derive the distance interpretation.
Recall: The frame coordinates have unit norm.

For a unit input Q a, its projection into L and its perpendicular remainder form a right triangle. In principal coordinates, a single paired direction has projected length cosine theta and missed length sine theta. For a general combination, the squared missed length is the sum of squared coefficients weighted by the squared sines. The largest possible missed length is therefore the largest sine. That is the operator norm of I minus P L composed with Q. Adding all squared sine contributions instead gives the Frobenius sine error used in statistical bounds.

## PaBasis: A new basis changes entries, not angles

Why: Make coordinate invariance explicit.
Recall: Orthogonal matrices C and D change frame coordinates.

Replacing Q by Q C and Z by Z D changes the overlap to D transpose times the old overlap times C. Orthogonal multiplication preserves singular values. Therefore the principal-angle list stays the same, even though the overlap entries and every displayed basis arrow may change. Repeated singular values can leave several equally valid choices of principal vectors. The angles remain meaningful without a unique choice of those vectors.

## PaSummary: What the angle list tells us

Why: Reinforce the three opening claims.
Recall: Classroom angles are ordered from smallest to largest.

Principal angles compare subspaces independently of the bases chosen. The singular values of the frame overlap are the cosines of those angles. The largest sine measures the worst perpendicular error of a unit input. Zero angles describe common directions; right angles describe perpendicular paired directions. For unequal dimensions, one must specify a directed convention rather than assuming this equal-dimensional list controls every comparison. The closing Lean facts use principal cosines, whose symmetry avoids that ambiguity. Their finite-support representation is padded by zeros; the dimensions tell us how many geometric angles to retain.

## PaFacts: Two facts about principal cosines

Why: Pair geometric meanings with the formal API.
Recall: c i denotes an overlap singular value.

Every principal cosine lies between zero and one, making the inverse cosine a legitimate geometric angle on the actual angle indices. Swapping the two subspaces gives the same principal cosines. The latter follows because the two overlap maps are adjoints and have the same singular values. These are the precise facts shown in Lean next. We are not identifying the classroom increasing angle list with every directed-angle convention in the library.

## PaLean: Lean: cosines are in the unit interval

Why: Inspect the bound and its assumptions.
Recall: Finite-dimensional real inner product space; U and V are subspaces.

Principal cosines names the singular values of the cross-projection map. The two inequalities certify that each value is a possible cosine, including the padded zero values. The proof combines the accepted non-negativity and contraction bounds.

## PaLeanSymmetry: Lean: exchange the two spaces

Why: Connect adjoints to symmetry.
Recall: The same U and V occur on both sides.

The equality states that the entire finite-support cosine function is unchanged when the spaces are exchanged. This is a statement about the cosine data. Directed sine lists for unequal dimensions need additional care and are not being equated by this theorem.

## PaComputation: Bonus: compute angles from orthonormal frames

Why: Separate subspace geometry from basis scaling.
Recall: Start with full-rank spanning columns.

First orthonormalize the spanning columns, for example with a QR factorization. Then take the singular values of Z transpose Q. Clamp only tiny roundoff excursions outside the interval zero to one before applying inverse cosine. Near a zero angle, inverse cosine can lose relative accuracy. Computing the singular values of the perpendicular remainder offers sine information instead. Raw non-orthonormal column overlaps do not directly give principal cosines.
