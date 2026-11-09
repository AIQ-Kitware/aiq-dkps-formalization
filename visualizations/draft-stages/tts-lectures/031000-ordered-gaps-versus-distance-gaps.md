# 031000 — Ordered gaps versus distance gaps

**Draft status:** audio-first mathematical lecture. **Prerequisites:** eigenvalues and eigenspaces, reducing subspaces, spectral projections, and Rayleigh quotients. **Next:** coordinate-free finite functional calculus.

<!-- BEGIN SPOKEN LECTURE -->

# When are two groups of eigenvalues separated?

Suppose someone tells you that two groups of eigenvalues are separated by a gap of two. What picture comes to mind? Perhaps one group sits to the left on a number line, there is an empty stretch of length two, and the other group sits to the right.

That picture describes one kind of gap. But it does not describe every kind. Two groups can be separated from each other even when their eigenvalues alternate along the number line. The difference matters because different mathematical arguments require different kinds of separation.

These forms of spectral separation have different consequences for Sylvester equations and perturbation bounds.

## First, two sets on a number line

Start with two nonempty finite sets of real numbers. Call the first group red and the second group blue. Their *distance gap* is the smallest absolute difference between one red number and one blue number.

Take red numbers negative three and positive three, and a single blue number zero. Every red number is three units away from blue. So the distance gap is three.

But could we draw one vertical dividing line so that all red numbers are on one side and all blue numbers are on the other? No. Blue zero lies between the two red values. The groups are separated in the pairwise-distance sense, but they are not ordered.

Now choose red numbers negative two and zero, and blue numbers three and five. Every blue number lies to the right of every red number. The nearest red and blue values are zero and three, so the distance gap is three again. This time we have *ordered separation*: every blue number exceeds every red number by at least three.

The same numerical gap, three, describes two different arrangements.

One is a statement about absolute differences. The other is a statement about an ordering of all pairs.

## Translating the picture to operators

For a self-adjoint matrix, every eigenvalue is real, so the number-line picture applies. But we need to specify *which* eigenvalues belong to each group.

Recall that a spectral projection selects an entire eigenspace for each chosen eigenvalue. If a subspace is reducing, the operator acts on that subspace without sending vectors outside it. We can restrict the operator to the selected subspace and separately to its perpendicular complement.

Those restrictions have spectra of their own.

For example, take a diagonal operator with entries negative three, zero, and three. Let our selected subspace be the plane spanned by the first and third coordinate directions. The restriction to that plane has eigenvalues negative three and three. The complementary line has eigenvalue zero.

So the two restricted spectra have distance gap three. Yet they interlace: the complementary eigenvalue lies between the two selected ones.

If instead we select the first two coordinate directions of a diagonal operator with entries negative two, zero, and three, the selected spectrum is negative two and zero, while the complement has eigenvalue three. Now the blocks are ordered, with a gap of three.

Notice what a gap is *not*. It is not necessarily the distance between consecutive eigenvalues in the full sorted list. It is a distance between two specifically identified spectral groups. Those groups may be chosen in different ways, and different theorems may compare blocks from different operators.

## Internal gaps, external gaps, and mixed gaps

An *internal* gap compares two blocks of the same operator, such as a reducing subspace and its orthogonal complement.

A *mixed* gap compares a selected block of one operator with a complementary block of another. Those blocks are the ranges of spectral projections obtained by summing the eigenspace projections over the selected eigenvalue sets. Later, in the sine-theta theorem, the mixed comparison is exactly what enters a residual equation.

There is also an interval-versus-exterior description. Suppose one spectral group lies between zero and two. The other must lie outside an enlarged interval extending from negative one to three. Then every value in the first group is at least one unit from every value in the second group.

But the exterior group might have values on *both* sides: perhaps negative four and five. So the interval-versus-exterior condition guarantees distance separation without necessarily putting the groups in a single global order.

This is why a theorem that assumes an interval and its enlarged exterior cannot automatically be read as a theorem about two ordered blocks. We have to check the actual statement.

## Ordered separation is stronger

Let's prove a simple implication. Suppose every blue eigenvalue is at least delta greater than every red eigenvalue, where delta is nonnegative.

Choose any red value and any blue value. Blue minus red is at least delta, so its absolute value is also at least delta. Therefore ordered separation implies pairwise distance separation.

The converse fails, as the negative-three, zero, three example demonstrates. Its red and blue spectra are three apart but cannot be put in the demanded order without changing which group is which.

This distinction is not a technicality. It changes the type of argument we can use.

## A first encounter with the Sylvester equation

Consider the scalar equation: a times x, minus x times b, equals c.

Because these are numbers, the left side is simply a minus b, multiplied by x. If a and b are different, the unique solution is c divided by a minus b.

The absolute difference between a and b tells us how large that division can make x. A small denominator means a potentially large solution; a large denominator limits its size.

For diagonal matrices A and B, a matrix equation of the form A X minus X B equals C works entry by entry in exactly the same way. Each entry of X is the corresponding entry of C divided by a difference between an eigenvalue of A and an eigenvalue of B.

This makes the pairwise distance gap look like the natural object: none of those denominators can be smaller in absolute value than the gap.

And for a sum-of-squares measure of matrix size, such as the Frobenius norm, the entry-by-entry argument gives an immediate estimate.

But not every matrix norm behaves by summing independent squares. For the operator norm, cancellation and the way different entries combine can matter. We cannot claim an identical sharp bound for every norm just because the scalar denominators are large.

There is a particularly clean additional idea when the spectra are ordered. Suppose all eigenvalues of A lie below all eigenvalues of B. Then the differences all have the same sign. This allows us, later, to build the inverse of the Sylvester operation using a convergent integral of matrix exponentials, with no conflicting directions of growth.

When the two spectra interlace, the sign can change from one pair to another. That single integral argument is no longer available in the same form. More elaborate constructions are needed for the general separated case.

For the Sylvester equation A X minus X B equals C, an ordered spectral gap supports a decay-integral estimate with constant one, while an interlaced pairwise gap can require a different bound. The location of the spectral sets, not merely the size of a number called a gap, decides which estimate applies.

## Ordered gaps and quadratic forms

There is another description of ordered separation that connects back to Rayleigh quotients.

Suppose A is self-adjoint, and its selected subspace and complement reduce A. Imagine that every unit vector in the selected subspace has Rayleigh quotient at most one, while every unit vector in the complement has quotient at least four.

Then the eigenvalues on the first block lie at or below one, and those on the second block lie at or above four. Their ordered gap is at least three.

Why? An eigenvector's Rayleigh quotient equals its eigenvalue. So the bounds on all unit vectors certainly bound all the eigenvalues. Conversely, the spectral theorem expresses any unit-vector Rayleigh quotient as a weighted average of the eigenvalues in its block, so spectral bounds imply those quadratic-form bounds.

That is the bridge between a geometric picture of two groups of eigenvalues and inequalities we can verify directly on vectors.

## A diagnostic exercise

Here are three questions to test whether the distinctions are clear.

First: selected eigenvalues are negative four and four, and the complement has eigenvalue zero. Is there a positive distance gap? Yes, of size four. Is there a global ordered gap between those two named blocks? No.

Second: selected eigenvalues are one and two, and complementary eigenvalues are five and seven. What ordered gap is guaranteed? Three, with the selected group below the complement.

Third: why does knowing the spectrum of the whole matrix not by itself tell you which gap a theorem is using? Because the theorem may compare *restricted* spectra associated with particular subspaces, or even restrictions belonging to two different operators.

The lesson to carry forward is simple. Before applying a spectral theorem, draw the relevant groups on a number line. Then ask not just how far apart they are, but whether they are ordered, interlaced, or separated as an interval and its exterior.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For self-adjoint restrictions with finite spectra \(\Sigma_1,\Sigma_2\subseteq\mathbb R\), a **distance gap** \(\delta\ge 0\) means \(|\lambda-\mu|\ge\delta\) for all \(\lambda\in\Sigma_1\), \(\mu\in\Sigma_2\). An **ordered gap** in one orientation means \(\lambda+\delta\le\mu\) for all such pairs. The latter implies the former when \(\delta\ge0\), not conversely.

An interval/exterior condition, \(\Sigma_1\subseteq[a,b]\) and \(\Sigma_2\cap(a-\delta,b+\delta)=\varnothing\), implies pairwise distance separation for \(\delta\ge0\), but need not imply a single ordering of the sets.

For diagonal \(A=\operatorname{diag}(a_i)\), \(B=\operatorname{diag}(b_j)\), the Sylvester equation \(AX-XB=C\) reads \((a_i-b_j)X_{ij}=C_{ij}\). If all denominators have absolute value at least \(\delta>0\), then \(\|X\|_F\le\|C\|_F/\delta\). **This does not assert a universal constant-one operator-norm bound in the unordered case.**

**Lean bridge.** In the current DKPS staging source, `ForTauCeti/Analysis/InnerProductSpace/Spectral/Gap.lean` defines the two gap predicates and proves one implication:

```lean
def PointSpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ Module.End.restrictedPointSpectrum A U →
    μ ∈ Module.End.restrictedPointSpectrum B V →
    δ ≤ |lam - μ|
```

The same module defines ordered separation as a second predicate:

```lean
def OrderedGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ Module.End.restrictedPointSpectrum A U →
    μ ∈ Module.End.restrictedPointSpectrum B V →
    lam + δ ≤ μ
```

These are exact declaration bodies from separate locations in the source file (the source also attaches `@[expose]` attributes). The following checked theorem signature appears in the same file:

```lean
theorem PointSpectraSeparated.of_orderedGap {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →ₗ[𝕜] F} {V : Submodule 𝕜 F} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : OrderedGap A U B V δ) : PointSpectraSeparated A U B V δ := by
```

The `Submodule` arguments specify **which** restricted spectra are being compared. The `Prop` return type says the gap is a mathematical hypothesis, not a computed number. The nonnegativity hypothesis `hδ` is needed for the ordered-to-absolute implication. The mathematical definitions in this DKPS-authored staging module remain part of the curriculum regardless of where they may subsequently be upstreamed.

**Reconstruction:** Prove ordered separation implies distance separation. Give a counterexample to its converse. Derive the diagonal Hilbert–Schmidt/Frobenius Sylvester estimate without asserting an unproved estimate for other gauges.
