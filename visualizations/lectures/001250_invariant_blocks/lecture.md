# Invariant subspaces — why blocks are allowed

## IbTitle: Invariant subspaces and blocks

Why: See why small pieces can be studied independently.
Recall: Linear maps and orthogonal projection.

Invariant subspaces, and why blocks are allowed.

## LectureOutcomes: The three facts we will explain

Why: Separate notation from a structural claim.
Recall: Finite real Euclidean space.

An invariant subspace keeps its vectors inside itself under a map. One invariant subspace gives a triangular block structure, not necessarily a diagonal one. Two preserved perpendicular parts give block diagonality and commutation with projection. The point is to justify when a large matrix really splits into independent problems. We will track vectors across a proposed boundary before deciding which blocks can be zero.

## IbSetup: The objects in the block test

Why: Fix the local setting and explain the objects.
Recall: The opening conclusions describe what we will establish.

A finite real inner product space is our whole space. T is a linear map and K is a proposed subspace. K perpendicular names the vectors perpendicular to every vector in K. P keeps the component in K and removes the perpendicular part. We want to know which inputs T sends across this division. Invariance means that inputs in one chosen part remain there; it does not require their lengths or individual positions to stay unchanged.

## IbQuestion: A boundary that the map respects

Why: Give invariance a visible meaning.
Recall: K is the horizontal axis.

A subspace is useful for simplifying a map only if the map respects it. Here K is the horizontal line. Apply the displayed matrix to a horizontal input: its output is still horizontal. This is the meaning of invariant. It does not mean the vector stays fixed; here its length doubles. In nineteenth-century matrix theory, eigenvectors supplied the simplest such pieces: a whole line remains a line.

<!-- beat -->

Now test a vertical input. The green output acquires a horizontal component. The horizontal line is invariant, but its perpendicular line is not. One preserved subspace has not split the whole problem into independent parts. The changing upper-right entry records exactly this transfer.

## IbBlocks: Read columns as inputs and rows as outputs

Why: Derive the zero blocks from vector behavior.
Recall: T acts on K plus its perpendicular complement.

The first block column describes inputs from K. Its lower entry measures the output outside K. If K is invariant, that entry is zero. The upper-right block describes a different transfer: inputs from the complement producing output in K. Our example allows that transfer. The result is block triangular, not block diagonal. A block is a map between named spaces, not merely a convenient box drawn around entries.

## IbSymmetry: Self-adjointness supplies the other zero

Why: Explain the often abbreviated symmetry step.
Recall: The inner product detects perpendicularity.

For a self-adjoint map, one invariant subspace is enough to make its perpendicular complement invariant too. Why? Take x in K and y perpendicular to K. The inner product of T y with x equals the inner product of y with T x. Invariance places T x inside K, so that last inner product is zero. Thus T y is perpendicular to every vector in K. This supplies the second zero block. For a general map, the adjoint identity used here is unavailable.

## IbCommute: Projection tests the two-way separation

Why: Turn geometry into a useful equation.
Recall: P keeps K; I minus P keeps its complement.

If T preserves both pieces, projecting before or after applying T gives the same K component. That is P T equals T P. Conversely, suppose these two compositions agree. For x in K, P x equals x, so P T x equals T x and T x lies in K. For y in the complement, P y is zero, so P T y is zero and T y remains in the complement. This proves the equivalence rather than treating commutation as an unexplained requirement.

## IbExample: An invariant line need not be a fixed line

Why: Distinguish preservation from pointwise identity.
Recall: The eigenvalues in this example are two and three.

The diagonal example scales the two axes separately. Every horizontal input stays horizontal and every vertical input stays vertical, but neither axis is fixed point by point. Both one-dimensional restrictions can now be analyzed independently. The two-by-two drawing illustrates a general block rule: in higher dimensions each scalar box can be replaced by an entire linear map on its own subspace.

## IbSummary: What justifies a block reduction?

Why: Return to the opening distinctions.
Recall: One operator, or several operators to be reduced together.

An invariant subspace keeps its vectors inside itself under a map. One invariant subspace gives a triangular block structure, not necessarily a diagonal one. Two preserved perpendicular parts give block diagonality and commutation with projection. For one operator, inspect where vectors from each part go. For several operators, a useful common block must be preserved by each of them. A decomposition for one operator alone does not automatically simplify the others. This is the extra issue that arises in structural proofs involving a motion and two projections.

## IbFacts: Two reusable projection laws

Why: Connect the geometry to exact statements.
Recall: P is orthogonal projection onto K.

The off-diagonal part of T is P T times I minus P, plus I minus P times T P. It vanishes exactly when T commutes with P. Its two terms have perpendicular output ranges, so cancellation cannot conceal a nonzero transfer. Separately, every vector is the sum of its two orthogonal projections. These are the two facts on the next Lean cards.

## IbLean: Lean: off-diagonal transfer vanishes

Why: Read the exact commutation criterion.
Recall: K is a subspace with an orthogonal projection.

Off diagonal block names the sum of the two transfers just discussed. The theorem says its vanishing is equivalent to commutation of the projection and T. Lean uses bounded linear maps; our finite matrices give a familiar specialization. No condition that T fixes K point by point appears.

## IbLeanSplit: Lean: the vector decomposition

Why: Connect the coordinate split to projection maps.
Recall: The complement is written K perpendicular.

The second statement says the two projected vectors add back to the original input. Star projection is the orthogonal projection in this API. This decomposition is what lets the commutation identity control the two parts of every vector.

## IbComputation: Bonus: testing a proposed block numerically

Why: Measure transfer instead of trusting a picture.
Recall: Q and Z are orthonormal frames for perpendicular parts.

For a proposed split, compute Z transpose T Q and Q transpose T Z. These are the two off-diagonal blocks. Their norms measure leakage across the split. Small entries are evidence of approximate preservation, not proof of exact zero. If T is not self-adjoint, test both directions. A change of basis describes the same map; it does not eliminate a real transfer between the proposed spaces.
