# 006000 — Unitarily invariant norms and Ky Fan dominance

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 058000. **Section:** norms. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

# Which measurements survive a change of orthonormal coordinates?

Suppose two people measure the same linear map, but one uses a different orthonormal basis for the inputs and a different orthonormal basis for the outputs. They should agree on the map's intrinsic size. The operator, Frobenius, and nuclear norms all have this property. Their common property is invariance under unitary changes of input and output coordinates.

The statement we are heading toward is that, for a fixed finite matrix shape, an invariant norm can be read from its singular values using a symmetric gauge. Conversely, an appropriate symmetric gauge gives a norm on matrices by applying it to their singular values. The word appropriate matters: the triangle inequality is a theorem that we need to establish, rather than a consequence of merely choosing an arbitrary symmetric function.

We will also distinguish a property of one matrix space from a compatible rule that measures operators between many different spaces.

## Begin with orthonormal changes of coordinates

Let A send an input space of dimension n to an output space of dimension m. Choose orthonormal bases. The resulting matrix has m rows and n columns.

Changing the output basis multiplies the matrix on the left by a unitary matrix. Changing the input basis multiplies it on the right by a unitary matrix, with an adjoint depending on which direction the coordinate change is written. So the mathematical question is whether a norm of A stays the same after multiplying by arbitrary unitaries on both sides.

Call a matrix norm unitarily invariant if it does.

For the operator norm, the reason is immediate. A unitary maps the unit sphere onto itself and preserves the length of every output vector. So maximizing output length over unit inputs yields the same value before and after changing bases.

For the Frobenius norm, we can use the sum of squared singular values. For the nuclear norm, we use their sum. In both cases the singular values are unchanged by unitary multiplication.

The interesting question is whether all unitarily invariant norms depend on singular values in essentially this way.

## Use the singular-value decomposition

The singular-value decomposition says that A can be expressed as a unitary change of output coordinates, followed by a rectangular diagonal matrix of singular values, followed by a unitary change of input coordinates.

Because our norm is invariant under the two unitary factors, its value on A equals its value on that rectangular diagonal matrix.

Every singular value is nonnegative. We can arrange them from largest to smallest. There are at most the smaller of m and n positive values, and we include zeros to get a fixed-length list.

Thus a unitarily invariant norm is determined by a function of this list. But which functions are possible?

First, permuting the diagonal positions does not change the matrix norm. We can implement the same permutation using unitary permutation matrices. Second, changing the sign or complex phase of one diagonal entry also leaves the norm unchanged, because a diagonal unitary can supply that sign or phase.

Consequently the associated function of diagonal entries is invariant under permutations and sign changes. Its positive homogeneity and triangle inequality come from the matrix norm applied to diagonal matrices. So it is a symmetric gauge: a norm on an ordinary coordinate list that is blind to signs and reordering.

This proves the forward direction for a fixed shape. We did not assume that the norm was Schatten p. The operator, Frobenius, and nuclear norms are just three choices of gauge.

## Construct an invariant norm from a gauge

Now begin with a symmetric gauge on lists of length equal to the smaller matrix dimension. Define the size of A to be the gauge of A's singular-value list.

Nonnegativity and scaling are straightforward. The size is zero only if all singular values are zero, which happens exactly when A is the zero map. Unitary invariance follows from singular-value invariance.

The challenge is the triangle inequality. The singular values of A plus B are generally not the coordinatewise sums of the singular values of A and B. Their singular vectors may point in entirely different directions.

The Ky Fan inequalities give the needed common comparison across every leading singular-value prefix. For every prefix length, the sum of the largest singular values of A plus B is at most the corresponding prefix sum for A plus the corresponding prefix sum for B.

In other words, the singular-value list of A plus B is weakly majorized by the coordinatewise sum of the two sorted singular-value lists.

A symmetric gauge is monotone under weak majorization of nonnegative lists: if every leading partial sum of one list is bounded by the corresponding sum of another, the first gauge cannot exceed the second. Applying that fact gives an upper bound by the gauge of the coordinatewise sum. Finally, the ordinary triangle inequality for the gauge bounds that by the sum of the two separate gauges.

We have proved the matrix triangle inequality in three moves: Ky Fan comparison, gauge monotonicity, then the gauge's own triangle inequality.

This is a useful proof strategy because it can establish many norm inequalities without repeating an argument for each Schatten exponent.

## Compare the gauges with an example

Take a square diagonal matrix with singular values four, two, and one.

The operator norm gives four, since it retains the largest entry. The nuclear norm gives seven, since it adds all entries. The Frobenius norm gives the square root of sixteen plus four plus one, which is the square root of twenty-one.

The Ky Fan two norm gives six, the sum of the two largest singular values. Do not confuse that with the Schatten two norm, which is Frobenius. The two names both contain the number two, but one counts how many leading singular values we add, while the other specifies a power.

For this same diagonal matrix, all four measurements are invariant if we rotate the input and output bases. They distinguish different features of the map, but they do not depend on how the coordinates were named.

Now replace the diagonal matrix by a matrix with the same three singular values and completely different singular vectors. Every one of these norms still agrees. For questions that depend only on singular values, these two maps are indistinguishable.

## A general comparison theorem

Suppose the singular values of A are weakly majorized by those of B. Then every symmetric gauge gives A no larger a value than B.

The proof is the same majorization principle used in the triangle inequality. It gives a way to move from finitely many scalar prefix inequalities to a whole family of norm inequalities.

The converse is visible through the Ky Fan gauges. If all invariant gauges make A no larger than B, in particular each Ky Fan gauge does. Those Ky Fan comparisons are precisely the defining prefix inequalities of weak majorization.

Thus the Ky Fan sums capture the common order information seen by all unitarily invariant norms in a fixed finite matrix shape.

This is one reason Davis–Kahan estimates are sometimes proved first at the level of singular-value sums. A single family of prefix inequalities can imply operator, Frobenius, nuclear, and many other bounds.

## An operator ideal is an additional structure

So far, A and B have had one fixed matrix shape. In infinite-dimensional analysis, we may want to measure maps between many Hilbert spaces and restrict the domain to operators on which the chosen measurement is finite.

Then the norm is part of a family, often called an operator ideal norm. In addition to ordinary norm laws, the family is required to behave predictably under composing with bounded operators on the left and right.

For example, composing A with a contraction on the output side should not increase its ideal norm. The same is expected for a contraction on the input side. In the finite-dimensional setting, singular-value inequalities explain these facts for standard gauges.

But this compatibility is additional information. Knowing only that each individual matrix space carries some unitarily invariant norm does not ensure consistency when the dimensions change.

A compatible family of unitarily invariant norms needs more than invariance for one matrix size: it must respect appropriate ideal operations, agree with rank-one normalization, and obey the Ky Fan dominance principle used to transfer singular-value comparisons.

## Why this matters for perturbations

A perturbation may rotate several mutually orthogonal directions by different amounts. An operator-norm estimate captures only the worst direction. A Frobenius estimate aggregates squared effects. A nuclear estimate sums their magnitudes. A general unitarily invariant norm lets us decide which aggregate is appropriate for the application.

Our proofs show that the same singular-value comparison can control all these choices. We have converted an apparently open-ended question about norms into concrete inequalities about ordered nonnegative lists.

The next issue is rectangularity. An operator might be represented in a larger output space or with extra zero input directions. Exactly when does adding those zero directions preserve a norm?

## What to reconstruct

Start with a unitarily invariant norm on matrices of one fixed shape. Use the singular-value decomposition to derive its symmetric gauge. Prove the reverse triangle inequality using weak majorization and the gauge triangle inequality.

Then calculate the operator, nuclear, Frobenius, and Ky Fan two values of the diagonal example with singular values four, two, and one. Finally, explain why invariance in one dimension does not yet guarantee consistency with another matrix dimension.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a fixed matrix shape, a unitarily invariant norm satisfies \(\|UAV\|_\Phi=\|A\|_\Phi\) for unitary \(U,V\) and is determined by a symmetric gauge \(\phi\) via \(\|A\|_\Phi=\phi(\sigma(A))\). The triangle inequality uses
\[
\sigma(A+B)\prec_w\sigma(A)+\sigma(B),\qquad
\phi(\sigma(A+B))\le\phi(\sigma(A)+\sigma(B))\le\phi(\sigma(A))+\phi(\sigma(B)).
\]
The normalized source-facing operator-ideal family has stronger cross-space compatibility than bare finite-dimensional unitary invariance.

**Lean bridge (verbatim excerpts).**

`DavisKahan/OperatorIdeal/NormalizedUnitaryInvariantNorm.lean`:

```lean
theorem gauge_comp_isometryEquiv (e : F ≃ₗᵢ[𝕜] G) (f : H ≃ₗᵢ[𝕜] E)
    {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge ((e.toContinuousLinearEquiv : F →L[𝕜] G) ∘L A ∘L
      (f.toContinuousLinearEquiv : H →L[𝕜] E)) = N.gauge A := by
```

This is the cross-space version of unitary invariance: both coordinate changes are linear isometric equivalences. Its ideal-membership assumption is explicit and the underlying family supplies the ideal laws.

`DavisKahan/OperatorIdeal/NormalizedUnitaryInvariantNorm.lean`:

```lean
theorem gauge_comp_left_le (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A)
    (hL : ‖L‖ ≤ 1) : N.gauge (L ∘L A) ≤ N.gauge A :=
```

This is the contraction rule for left composition, a condition stronger than assigning unrelated invariant norms to separate matrix shapes.

**Reconstruction exercise:** Reprove the principal displayed identity from the spoken lecture, then identify the exact source/target types and extra assumptions in each displayed Lean declaration.
