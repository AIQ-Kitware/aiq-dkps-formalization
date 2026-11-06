# Projection-valued measures

Authored by GPT-6.1-Sol. Source and Lean correspondence: `sources.md`.
The finite examples are illustrations; infinite-dimensional assertions retain
their topology and domain qualifications.

## PvTitle: Projection-valued measures

Why: Select a spectral region, then integrate its components.
Recall: PVM means projection-valued measure.

Projection-valued measures.

## PvSetup: The setting and the notation

Why: A set of spectral values will select a subspace.
Recall: An orthogonal projection keeps the component lying in a subspace.

Work on a Hilbert space, which may have finitely or infinitely many dimensions. We use complex Hilbert spaces for the formal companions; our real matrix pictures also act on complex coordinates. A is a self-adjoint operator. Capital B denotes a Borel set of real spectral values: intervals and countable combinations of intervals are examples. E of B will be an orthogonal projection onto the part of the space associated with those values. E is the name of the entire projection-valued measure, not the Hilbert space.

## PvQuestion: Why replace an eigenvalue list?

Why: We want to select spectral components without choosing individual eigenvectors.
Recall: A finite self-adjoint matrix has an orthonormal eigenbasis.

For a matrix, one can choose eigenvectors and keep the columns whose eigenvalues lie in a chosen interval. That is a useful picture, but a repeated eigenvalue allows many choices of basis inside the same eigenspace. In infinite dimensions there may not even be an eigenbasis. We need an object that selects the space directly.

<!-- beat -->

A projection-valued measure assigns an orthogonal projection to each measurable spectral set. It packages selection, set operations, and countable decomposition into one object. This viewpoint belongs to the spectral-theorem and functional-analysis tradition associated with Riesz, von Neumann, and others; Kato’s 1966 Perturbation Theory for Linear Operators makes spectral projections central to perturbation theory. Our goal is to understand that object, not to prove the full spectral theorem in one lecture.

## PvWindow: A finite spectral window

Why: Start with the matrix picture before replacing sums by integrals.
Recall: The four eigenvalues are 1, 2, 2, and 4.

Here is an example in spectral coordinates. The matrix has eigenvalues one, two, two, and four. A window around two selects both directions in the two-dimensional eigenspace with eigenvalue two. E of B keeps those coordinates and removes the others. In this eigenbasis its matrix is diagonal with entries zero, one, one, and zero.

<!-- beat -->

Move the window until it also contains four. The selected projection gains that eigendirection. It changes only when the membership of a spectral value changes. A set of values cannot select just one arbitrary direction from a repeated eigenspace: both copies of the value two enter together. This is one reason to organize the definition by spectral sets rather than by a list of chosen eigenvectors.

## PvMatrix: A basis-independent projection

Why: A coordinate formula describes an intrinsic subspace.
Recall: P j denotes the orthogonal projection onto the entire eigenspace for a distinct value.

Group the matrix by its distinct eigenvalues. Let P j project onto the whole eigenspace for lambda j. The P j projections are mutually orthogonal and add to the identity. Then A is the sum of lambda j times P j, and E of B is the sum of P j over the eigenvalues belonging to B. The same eigenspace may have dimension greater than one.

<!-- beat -->

In arbitrary orthonormal coordinates, these operators are conjugated by the same orthogonal or unitary change of basis. The selected subspace itself does not depend on the basis chosen within a repeated eigenspace. This is a finite projection-valued measure: it has finitely many nonzero atoms, where an atom here is a singleton spectral value with a nonzero projection.

## PvLaws: Sets become commuting projections

Why: Intersection means keep only the spectral components common to both sets.
Recall: Composition is multiplication of the two bounded operators.

For any Borel set B, E of B is self-adjoint and idempotent, so it is an orthogonal projection. The empty set gives zero, and the whole real line gives the identity. Most importantly, E of B times E of C equals E of the intersection of B and C. For this one PVM the projections therefore commute.

<!-- beat -->

Complements give the familiar operator I minus E of B. Disjoint spectral sets give orthogonal ranges, so the projection of their union is the sum of the projections. These facts are properties of one compatible family of spectral projections. Two arbitrary orthogonal projections, or projections belonging to different operators, do not have to commute.

## PvCountable: Why this is called a measure

Why: Countable disjoint decomposition is an essential part of the definition.
Recall: Convergence will be measured after applying the operators to a fixed vector.

Finite additivity alone does not explain the word measure. For pairwise disjoint Borel sets B one, B two, and so on, apply the projection of their union to a vector x. The result is the norm-convergent sum of E of B j applied to x. This is strong countable additivity: for every fixed x, the partial sums converge in the Hilbert-space norm.

<!-- beat -->

The components are orthogonal, so their squared lengths add. In particular, the sum of their squared norms is bounded by the squared norm of x. That makes the vector sum well behaved. We are not asserting convergence of the operator partial sums in operator norm. The distinction will matter in the infinite-coordinate example later.

## PvMass: A scalar measure for each vector

Why: The scalar measure records how much of this vector lies in a spectral region.
Recall: x is fixed; B is the measurable set that varies.

Define mu x of B as the squared norm of E of B applied to x. Because E of B is an orthogonal projection, this is also the inner product of x with E of B x. The result is a nonnegative scalar measure, with total mass equal to the squared norm of x. If x is a unit vector, it has total mass one and can be regarded as a probability measure.

<!-- beat -->

In our example the spectral coordinates of x are all one half, so x has unit norm. The masses at the distinct eigenvalues one, two, and four are one quarter, one half, and one quarter. The middle mass adds the energy of both directions at value two. It is not the rank of the projection. A vector orthogonal to a spectral space gives it mass zero even when that projection is nonzero.

## PvIntegral: Spectral integration weights the selected pieces

Why: The integral generalizes a weighted sum of orthogonal spectral pieces.
Recall: An indicator function is one on its set and zero outside.

For a simple function f equal to a sum of coefficients c j times indicators of disjoint measurable sets B j, define its spectral integral as the sum of c j E of B j. Selecting a set is the special case where f is its indicator. A bounded measurable function is handled by extending this construction with an appropriate limiting argument.

<!-- beat -->

For the spectral PVM of A, this operator is called f of A. In the finite example, f of A simply replaces each eigenvalue lambda j by f of lambda j while preserving its spectral projection. Thus squaring the function squares the eigenvalues, and an interval indicator produces a spectral projection. For bounded A, the coordinate function is bounded on its spectrum and recovers A. For an unbounded A, that last step needs a domain, which we will describe shortly.

## PvContinuous: A bounded example with no eigenvectors

Why: An operator can have spectral subspaces without an eigenbasis.
Recall: Functions in L squared are identified when they agree almost everywhere.

Consider the Hilbert space L squared of the interval zero to one with ordinary length measure. A vector is now a square-integrable function. Define A by multiplying a function by its input coordinate t. This is a bounded self-adjoint operator. E of B multiplies a vector by the indicator of the part of B inside zero to one. It keeps the part of the function supported in the chosen spectral window.

<!-- beat -->

This operator has no nonzero eigenvector. An eigenvector with eigenvalue lambda would have to vanish except where t equals lambda, a single point of measure zero. Such a function is zero in L squared. Nevertheless, intervals have nonzero spectral projections. The shaded window shows the support of E of B applied to the constant unit function. Its squared norm is the length of the window. Continuous spectral information is real geometry, even when there are no eigenvectors to draw.

## PvStrong: Strong convergence is not operator-norm convergence

Why: Finite spectral cutoffs converge for each fixed vector, but not uniformly over all unit vectors.
Recall: The full example has infinitely many coordinates; only the first few are drawn.

Take the Hilbert space of square-summable sequences, indexed by the positive integers. Let E of the integers from one through N keep the first N coordinates and discard the tail. For each fixed vector x, the tail’s squared energy tends to zero, so these projections applied to x converge to x. That is strong convergence to the identity.

<!-- beat -->

Yet the operator norm of I minus this projection is one for every finite N. Choose a unit coordinate vector just beyond the cutoff; it is entirely discarded. The offending vector can change with N. This example explains exactly why the countable-additivity statement uses convergence for each fixed x rather than operator-norm convergence. The dots at the right indicate more coordinates, not the end of the space.

## PvUnbounded: Unbounded operator, bounded projections

Why: Spectral integration must specify which vectors have a finite weighted second moment.
Recall: Use the same square-summable sequence space, now with eigenvalue n on coordinate n.

Define A x at coordinate n to be n times x n. The eigenvalues grow without bound. Every E of B is still a bounded orthogonal projection, defined for every square-summable vector. But A is defined only when the sum of n squared times the squared absolute values of x n is finite. This is a restriction on the vector, not on the PVM’s ability to project it.

<!-- beat -->

For instance, x n equal to one over n is square-summable, but A x would be the constant sequence one, which is not square-summable. That x is outside the domain. The general spectral statement is that x belongs to the domain of A exactly when the integral of lambda squared against mu x is finite. On that domain, A is the spectral integral of lambda, and the squared norm of A x equals that integral.

## PvCutoff: Bounded windows make an unbounded operator manageable

Why: A bounded spectral region limits the stretching that A can perform there.
Recall: B is contained in the interval from minus M to M, with M nonnegative.

If the spectral set B lies between minus M and M, all spectral values selected by E of B have absolute value at most M. Therefore E of B sends every vector into the domain of A, and the norm of A E of B x is at most M times the norm of x. The composition A E of B is a bounded, everywhere-defined operator, even though A itself may be unbounded.

<!-- beat -->

General spectral projections also preserve the domain of A and commute with A on that domain. Bounded windows give the stronger fact that every projected vector lies in the domain. This makes truncation useful: work on bounded spectral pieces, then recover the full space through limits. The domain qualifications cannot be dropped just because the projections themselves are bounded.

## PvDk: Where the PVM enters Davis–Kahan

Why: The PVM supplies the spectral spaces that the angle theorem compares.
Recall: A spectral projection selects a reducing subspace of its self-adjoint operator.

Choose a spectral region for the reference self-adjoint operator A and a corresponding region for the perturbed operator A hat. Their spectral PVMs give projections P and Q. The ranges of P and Q are the spaces we want to compare. The projection viewpoint works even when those ranges do not come with a finite eigenvector list.

<!-- beat -->

The PVM does not by itself prove a perturbation bound. Davis–Kahan supplies quantitative control under its spectral separation, residual, norm, and domain hypotheses. Our lecture has explained how to interpret the objects in those assumptions: spectral sets, their projections, and the operator restricted to the selected parts. That is the bridge from finite eigenvector pictures to the Hilbert-space statements.

## PvSummary: Selection, energy, and integration

Why: Keep the three roles separate while remembering how they fit together.
Recall: The measure is projection-valued; a fixed vector produces a scalar measure.

A PVM takes a measurable spectral set and returns an orthogonal projection. Its set operations become compatible operator operations, and disjoint countable unions become vectorwise norm-convergent sums. A fixed vector produces the scalar energy measure mu x. Spectral integration then weights the selected pieces to construct functions of an operator.

<!-- beat -->

An infinite-dimensional PVM need not come from an eigenvector list, and an unbounded spectral integral needs a domain. Bounded spectral windows provide a useful connection between these settings. The next cards record three reusable laws and show their accepted Tau Ceti forms. The optional numerical slide treats finite matrices only, so that a computational procedure is not mistaken for the full spectral theorem.

## PvFacts: Three reusable PVM laws

Why: These identities connect the symbolic notation to the next Lean cards.
Recall: B and C are measurable; x is any vector in the Hilbert space.

Intersection corresponds to multiplication of projections. Complementation corresponds to I minus the projection. The scalar mass of a spectral region is the squared norm of the projected vector. These laws hold for a PVM on a complex Hilbert space, independently of whether it arose from a finite matrix, a bounded multiplication operator, or an unbounded self-adjoint operator.

## PvLean: Lean companion: intersection

Why: The operator product is composition; measurability witnesses are explicit.
Recall: The slide E of B is Lean P dot proj B hB.

The first Lean card uses the accepted projection-valued measure structure in Tau Ceti. P is the whole PVM. Its proj field takes a set B and a proof hB that B is measurable. The multiplication symbol composes the two bounded operators. The statement is exactly the intersection law shown on the mathematical card. The source structure also carries compatible finite scalar measures for every vector; countable additivity is proved from that measure data.

## PvLeanComplement: Lean companion: complement

Why: This is the spectral meaning of I minus P.
Recall: The superscript complement refers to the set complement in the real line.

The complement of B is written with a superscript c. The theorem says that the corresponding projection is the identity bounded operator minus P dot proj B hB. No finite-dimensional instance is needed. The proof applies Tau Ceti’s accepted complement lemma, rather than reproducing the projection algebra in this lecture.

## PvLeanMass: Lean companion: scalar energy

Why: A vector-dependent scalar measure records squared projected length.
Recall: P dot diag x is the scalar measure associated with x.

The final Lean card states that the squared norm of the projected vector is the measure of B under P dot diag x, converted to a real number. Lean’s measure value uses extended nonnegative reals, but the PVM structure guarantees that this scalar measure is finite. The conversion therefore does not silently discard an infinite mass. These accepted PVM foundations have documented ancestry through this project and Spectra; the lecture itself does not claim original authorship of those proofs.

## PvComputation: Computing spectral windows for finite matrices

Why: This is an optional finite-dimensional procedure, not a construction for every PVM.
Recall: A is a symmetric or Hermitian matrix with a computed orthonormal eigenbasis.

For a finite matrix, diagonalize it with an appropriate symmetric or Hermitian eigensolver. Select the columns whose eigenvalues belong to B. Applying the projector to a vector can then be done as Q B times Q B adjoint x, without forming the full dense projector. For f of A, weight each eigenvector coefficient by f of its eigenvalue. Membership near a window boundary can be sensitive to numerical errors; a gap or explicit error analysis matters. This finite procedure does not construct the continuous-spectrum example, and finite truncations do not automatically converge in operator norm.
