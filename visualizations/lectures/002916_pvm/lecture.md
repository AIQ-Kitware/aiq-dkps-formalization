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

For a matrix, we often want to keep the part of a vector associated with a chosen range of eigenvalues. How can we express that selection without depending on a particular eigenvector list? We will build one object through three questions. Which components does a spectral region select? How much of a vector lies there? And what happens when we weight those components instead of merely keeping them? We start with a finite self-adjoint matrix A and then see which parts of this picture survive on an infinite-dimensional Hilbert space.

## PvQuestion: Why replace an eigenvalue list?

Why: We want to select spectral components without choosing individual eigenvectors.
Recall: A finite self-adjoint matrix has an orthonormal eigenbasis.

Begin with the selection question. For a matrix, one can choose eigenvectors and keep the columns whose eigenvalues lie in a chosen interval. That is a useful picture, but a repeated eigenvalue allows many choices of basis inside the same eigenspace. In infinite dimensions there may not even be an eigenbasis. We need an object that selects the space directly.

<!-- beat -->

A projection-valued measure assigns an orthogonal projection to each measurable spectral set. Our spectral regions are Borel sets: they include intervals and are closed under complements and countable unions. It packages selection, set operations, and countable decomposition into one object. This viewpoint belongs to the spectral-theorem and functional-analysis tradition associated with Riesz, von Neumann, and others; Kato’s 1966 Perturbation Theory for Linear Operators makes spectral projections central to perturbation theory. Our goal is to understand that object, not to prove the full spectral theorem in one lecture. Let us first draw that rule for a small matrix, where we can inspect every selected direction.

## PvWindow: A finite spectral window

Why: Start with the matrix picture before replacing sums by integrals.
Recall: The four eigenvalues are 1, 2, 2, and 4.

Keep the same idea of a spectral region; call that region B and its projection E of B. Here is an example in spectral coordinates. The matrix has eigenvalues one, two, two, and four. A window around two selects both directions in the two-dimensional eigenspace with eigenvalue two. E of B keeps those coordinates and removes the others. In this eigenbasis its matrix is diagonal with entries zero, one, one, and zero.

<!-- beat -->

Move the window until it also contains four. The selected projection gains that eigendirection. It changes only when the membership of a spectral value changes. A set of values cannot select just one arbitrary direction from a repeated eigenspace: both copies of the value two enter together. This is one reason to organize the definition by spectral sets rather than by a list of chosen eigenvectors. We can write this selection in a way that no longer depends on the coordinates used to draw it.

## PvMatrix: A basis-independent projection

Why: A coordinate formula describes an intrinsic subspace.
Recall: P j denotes the orthogonal projection onto the entire eigenspace for a distinct value.

The window just selected whole eigenspaces. Package that observation as a formula. Group the matrix by its distinct eigenvalues. Let P j project onto the whole eigenspace for lambda j. The P j projections are mutually orthogonal and add to the identity. Then A is the sum of lambda j times P j, and E of B is the sum of P j over the eigenvalues belonging to B. The same eigenspace may have dimension greater than one.

<!-- beat -->

In arbitrary orthonormal coordinates, these operators are conjugated by the same orthogonal or unitary change of basis. The selected subspace itself does not depend on the basis chosen within a repeated eigenspace. This is a finite projection-valued measure: it has finitely many nonzero atoms, where an atom here is a singleton spectral value with a nonzero projection. Now that one selection is basis independent, we need to check how different selections fit together.

## PvLaws: Sets become commuting projections

Why: Intersection means keep only the spectral components common to both sets.
Recall: Composition is multiplication of the two bounded operators.

We have a projection E of B for every spectral set B. To use this family reliably, its projections must agree about which components they keep. Begin with one set. Keeping its selected components twice changes nothing, so E of B is idempotent. It is an orthogonal projection, hence self-adjoint. Keeping no values gives zero; keeping the whole real line gives the identity.

<!-- beat -->

Now select B and then C. A component survives both operations precisely when its spectral value belongs to the intersection. Thus E of B times E of C equals E of their intersection. Reversing the selections gives the same result. These projections commute because they belong to this same spectral selection rule.

<!-- beat -->

This also explains complements and disjoint unions. Values outside B give I minus E of B. Disjoint sets select orthogonal components, so their projections add. We have described finite selections. Calling this object a measure adds one more requirement: the rule must also handle countably many disjoint pieces.

## PvCountable: Why this is called a measure

Why: Countable disjoint decomposition is an essential part of the definition.
Recall: Convergence will be measured after applying the operators to a fixed vector.

Suppose a spectral region has been split into disjoint sets B one, B two, and so on. For a finite matrix, adding the selected components is just a finite sum. To allow infinitely many pieces, take a fixed vector x and add the first N selected components. What should those partial sums approach?

<!-- beat -->

They approach the projection of x onto the union of all the sets. The displayed limit is in the Hilbert-space norm after applying each partial sum to this fixed x. This is strong countable additivity. It extends the finite selection rule to an infinite decomposition.

<!-- beat -->

The selected vector components are orthogonal, so their squared lengths add, with total at most the squared norm of x. Their energy is what makes the infinite sum manageable. We have not claimed uniform convergence over every unit vector. We will return to that distinction in a coordinate-cutoff example. First, these squared lengths give us a simpler, scalar way to describe what the PVM selects.

## PvMass: A scalar measure for each vector

Why: The scalar measure records how much of this vector lies in a spectral region.
Recall: x is fixed; B is the measurable set that varies.

The PVM tells us which subspace a set selects. A different question concerns a particular input: how much of this vector lies in that subspace? Fix x and define mu x of B to be the squared norm of E of B applied to x. This assigns a nonnegative number to each spectral region.

<!-- beat -->

Disjoint regions give orthogonal components, whose squared lengths add. Thus mu x is an ordinary nonnegative scalar measure. Its total mass is the squared norm of x; for a unit vector it has total mass one. The same quantity is the inner product of x with E of B x.

<!-- beat -->

Return to our four-coordinate example. Give x spectral coordinates all equal to one half. Its unit energy is distributed as one quarter at value one, one half at value two, and one quarter at value four. The middle mass counts this vector’s energy in both directions, rather than the rank of that two-dimensional projection. Selection has now given us an energy distribution. Can we use the same components to build operators that do more than keep or discard them?

## PvIntegral: Spectral integration weights the selected pieces

Why: The integral generalizes a weighted sum of orthogonal spectral pieces.
Recall: An indicator function is one on its set and zero outside.

So far our spectral filter has assigned only zero or one: discard a component or keep it. Let us allow other weights. Describe a simple function f by values c j on disjoint spectral sets B j. The indicator functions in the formula identify which piece receives each weight.

<!-- beat -->

Use the same selection rule, then apply the chosen weight. The resulting operator is the sum of c j times E of B j. This is the spectral integral of the simple function. An indicator gives back a spectral projection. For a bounded measurable function, a limiting construction extends this rule beyond finitely many weights.

<!-- beat -->

For the spectral PVM of A, the result is called f of A. In the finite case, replacing each eigenvalue lambda by its square gives A squared, while retaining the same eigenspaces. Integrating the coordinate function recovers A; an unbounded A will require a domain. Before tackling that issue, we should test the more basic promise: can spectral selection work when there are no eigenvectors to list?

## PvContinuous: A bounded example with no eigenvectors

Why: An operator can have spectral subspaces without an eigenbasis.
Recall: Functions in L squared are identified when they agree almost everywhere.

We have described selection and weighting using a finite matrix. To see why the measure viewpoint is useful, replace coordinate vectors by functions. Consider the Hilbert space L squared of the interval zero to one with ordinary length measure. A vector is now a square-integrable function. Define A by multiplying a function by its input coordinate t. This is a bounded self-adjoint operator. E of B multiplies a vector by the indicator of the part of B inside zero to one. It keeps the part of the function supported in the chosen spectral window.

<!-- beat -->

This operator has no nonzero eigenvector. An eigenvector with eigenvalue lambda would have to vanish except where t equals lambda, a single point of measure zero. Such a function is zero in L squared. Nevertheless, intervals have nonzero spectral projections. The shaded window shows the support of E of B applied to the constant unit function. Its squared norm is the length of the window. Continuous spectral information is real geometry, even when there are no eigenvectors to draw. Selection has survived without an eigenbasis. We should also examine the infinite-sum requirement: why did we specify convergence for each fixed vector?

## PvStrong: Strong convergence is not operator-norm convergence

Why: Finite spectral cutoffs converge for each fixed vector, but not uniformly over all unit vectors.
Recall: The full example has infinitely many coordinates; only the first few are drawn.

Return to that convergence question using a simpler infinite-dimensional picture: coordinates numbered one, two, three, and so on. Take the Hilbert space of square-summable sequences, indexed by the positive integers. Let E of the integers from one through N keep the first N coordinates and discard the tail. For each fixed vector x, the tail’s squared energy tends to zero, so these projections applied to x converge to x. That is strong convergence to the identity.

<!-- beat -->

Yet the operator norm of I minus this projection is one for every finite N. Choose a unit coordinate vector just beyond the cutoff; it is entirely discarded. The offending vector can change with N. This example explains exactly why the countable-additivity statement uses convergence for each fixed x rather than operator-norm convergence. The dots at the right indicate more coordinates, not the end of the space. Keep this same sequence space in mind. We will now change the spectral weights, so that the projections stay bounded but the operator they reconstruct becomes unbounded.

## PvUnbounded: Unbounded operator, bounded projections

Why: Spectral integration must specify which vectors have a finite weighted second moment.
Recall: Use the same square-summable sequence space, now with eigenvalue n on coordinate n.

The coordinate cutoffs we just used are bounded projections. Keep that same sequence space, but now let A multiply the nth coordinate by n. A puts larger and larger weights on successive spectral components. Can this weighted output remain square-summable for every square-summable input?

<!-- beat -->

The answer is determined by the displayed weighted sum. To belong to the domain of A, a vector x must satisfy that the sum of n squared times the squared magnitude of x n is finite. The projections themselves remain defined on every vector: they only keep or remove coordinates. Weighting those coordinates by n creates the domain restriction.

<!-- beat -->

Take x n equal to one over n. The input is square-summable, but A would send it to the constant sequence one, which is not. In general, the domain condition is a finite second moment of mu x, and that moment equals the squared norm of A x on the domain. This connects the scalar measure back to operator size. Can a spectral window limit the weights enough to put every selected vector safely in the domain?

## PvCutoff: Bounded windows make an unbounded operator manageable

Why: A bounded spectral region limits the stretching that A can perform there.
Recall: B is contained in the interval from minus M to M, with M nonnegative.

The obstacle was the size of the spectral weights. Select only a set B lying between minus M and M, with M nonnegative. On this selected part, the squared weight lambda squared is at most M squared. That is exactly the control needed for the second-moment domain condition.

<!-- beat -->

Therefore every vector E of B x belongs to the domain of A. Its weighted second moment is at most M squared times the squared norm of x, giving the displayed bound. The composition A E of B is bounded and everywhere defined even when A is unbounded.

<!-- beat -->

General spectral projections also preserve the domain and commute with A there. Bounded windows give the extra guarantee we just derived for every input vector. We can now select a spectral subspace and describe A on it with the domain conditions visible. This is the structure needed when a perturbation theorem compares selected subspaces before and after a change of operator.

## PvDk: Where the PVM enters Davis–Kahan

Why: The PVM supplies the spectral spaces that the angle theorem compares.
Recall: A spectral projection selects a reducing subspace of its self-adjoint operator.

Our original question was how to select spectral components without an eigenvector list. We now have a selection rule that also keeps track of infinite sums and operator domains. Choose a spectral region for the reference self-adjoint operator A and a corresponding region for the perturbed operator A hat. Their spectral PVMs give projections P and Q. The ranges of P and Q are the spaces we want to compare. The projection viewpoint works even when those ranges do not come with a finite eigenvector list.

<!-- beat -->

The PVM does not by itself prove a perturbation bound. Davis–Kahan supplies quantitative control under its spectral separation, residual, norm, and domain hypotheses. Our lecture has explained how to interpret the objects in those assumptions: spectral sets, their projections, and the operator restricted to the selected parts. That is the bridge from finite eigenvector pictures to the Hilbert-space statements. This application brings us back to the reason for introducing E of B. Let us collect how selection, vector energy, and weighting fit into that one object.

## PvSummary: Selection, energy, and integration

Why: Keep the three roles separate while remembering how they fit together.
Recall: The measure is projection-valued; a fixed vector produces a scalar measure.

A PVM takes a measurable spectral set and returns an orthogonal projection. Its set operations become compatible operator operations, and disjoint countable unions become vectorwise norm-convergent sums. A fixed vector produces the scalar energy measure mu x. Spectral integration then weights the selected pieces to construct functions of an operator.

<!-- beat -->

An infinite-dimensional PVM need not come from an eigenvector list, and an unbounded spectral integral needs a domain. Bounded spectral windows provide a useful connection between these settings. The next cards record three reusable laws and show their accepted Tau Ceti forms. The optional numerical slide treats finite matrices only, so that a computational procedure is not mistaken for the full spectral theorem. The next three laws are the parts of this route that we will connect explicitly to Lean.

## PvFacts: Three reusable PVM laws

Why: These identities connect the symbolic notation to the next Lean cards.
Recall: B and C are measurable; x is any vector in the Hilbert space.

Intersection corresponds to multiplication of projections. Complementation corresponds to I minus the projection. The scalar mass of a spectral region is the squared norm of the projected vector. These laws hold for a PVM on a complex Hilbert space, independently of whether it arose from a finite matrix, a bounded multiplication operator, or an unbounded self-adjoint operator. We begin with the intersection law, because it states that all the selections come from one compatible family.

## PvLean: Lean companion: intersection

Why: The operator product is composition; measurability witnesses are explicit.
Recall: The slide E of B is Lean P dot proj B hB.

Translate the compatible-selection rule into Lean first. The first Lean card uses the accepted projection-valued measure structure in Tau Ceti. P is the whole PVM. Its proj field takes a set B and a proof hB that B is measurable. The multiplication symbol composes the two bounded operators. The statement is exactly the intersection law shown on the mathematical card. The source structure also carries compatible finite scalar measures for every vector; countable additivity is proved from that measure data. With intersection understood, the next card expresses the selection of everything outside a region.

## PvLeanComplement: Lean companion: complement

Why: This is the spectral meaning of I minus P.
Recall: The superscript complement refers to the set complement in the real line.

The same PVM also represents the complementary selection. The complement of B is written with a superscript c. The theorem says that the corresponding projection is the identity bounded operator minus P dot proj B hB. No finite-dimensional instance is needed. The proof applies Tau Ceti’s accepted complement lemma, rather than reproducing the projection algebra in this lecture. The last card then fixes a vector and turns these projections into the scalar energy measure we used for the domain condition.

## PvLeanMass: Lean companion: scalar energy

Why: A vector-dependent scalar measure records squared projected length.
Recall: P dot diag x is the scalar measure associated with x.

The final Lean card states that the squared norm of the projected vector is the measure of B under P dot diag x, converted to a real number. Lean’s measure value uses extended nonnegative reals, but the PVM structure guarantees that this scalar measure is finite. The conversion therefore does not silently discard an infinite mass. These accepted PVM foundations have documented ancestry through this project and Spectra; the lecture itself does not claim original authorship of those proofs. This closes the mathematical route. The optional numerical slide returns to finite matrices and shows how the selection is applied in computation.

## PvComputation: Computing spectral windows for finite matrices

Why: This is an optional finite-dimensional procedure, not a construction for every PVM.
Recall: A is a symmetric or Hermitian matrix with a computed orthonormal eigenbasis.

For the computational version, return to the finite spectral window with which we began. For a finite matrix, diagonalize it with an appropriate symmetric or Hermitian eigensolver. Select the columns whose eigenvalues belong to B. Applying the projector to a vector can then be done as Q B times Q B adjoint x, without forming the full dense projector. For f of A, weight each eigenvector coefficient by f of its eigenvalue. Membership near a window boundary can be sensitive to numerical errors; a gap or explicit error analysis matters. This finite procedure does not construct the continuous-spectrum example, and finite truncations do not automatically converge in operator norm. The study questions check the two distinctions that became essential along the way: what kind of convergence we have, and where an unbounded operator can act.
