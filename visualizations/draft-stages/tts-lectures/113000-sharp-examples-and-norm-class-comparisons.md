# 113000 — Sharp examples and norm-class comparisons

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `069000` norm-dependent Sylvester estimates and `110000–112000` sine/tangent theorems. **Next:** `114000` off-diagonal perturbations and block reflection.

<!-- BEGIN SPOKEN LECTURE -->

# Sharp examples and norm-class comparisons

We have proved sine and tangent bounds. Now we need a way to judge them. When a theorem has a gap in the denominator and a norm on each side, which factors are inevitable? What does it mean for an estimate to be sharp? And why must we be careful when changing from operator norm to Frobenius norm or a different unitarily invariant norm?

Our answers will come from matrices small enough to calculate by hand.

## Three separate questions about any bound

Suppose a theorem reads: delta times an angular error norm is at most a constant times a residual norm.

We should ask three questions independently. First, are the hypotheses satisfied, including the exact spectral gap? Second, is the constant valid for the specified norm? Third, is that constant the smallest possible over the full permitted class of examples?

A numerical example can demonstrate equality and therefore prove that the constant cannot be improved for a theorem that includes it. An example can also refute a proposed constant by producing a strict failure. But a sample with a large margin proves neither optimality nor failure.

We will use equality and counterexamples, not numerical impressions, to assess theorems.

## A sharp sine example

Let A be diagonal with entries zero and five, and let U be its zero-eigenspace, the horizontal line. Choose the unit trial vector e with coordinates cosine theta and sine theta.

First take a trial operator M equal to zero, without requiring it to be the Ritz compression. The residual equals A e, the vertical vector of length five sine theta. The unwanted eigenvalue equals five, so the gap between M and the unwanted block is five.

The sine of the angle is sine theta. Thus the theorem's two sides are both five sine theta. Equality holds for every angle between zero and ninety degrees.

This proves the coefficient one in the sine theorem cannot be decreased under those assumptions. There is no need to optimize over complicated examples; a planar model already reaches equality.

There is an important qualification. M equals zero is not the Ritz value unless theta is zero. A statement restricted to Ritz compressions cannot cite this example alone as its sharpness proof. We need a different computation for that narrower class.

## A sharp Ritz tangent example

Keep A diagonal with entries zero and five, U the horizontal axis, and the unit trial vector e equal to cosine theta, sine theta. Its Ritz scalar is the inner product of e with A e, namely five sine squared theta. Subtract M e from A e: the residual has first coordinate negative five sine squared theta cosine theta and second coordinate five sine theta cosine squared theta. Its squared length is twenty-five sine squared theta cosine squared theta, so its length is five sine theta cosine theta.

The spectral distance from M to the unwanted eigenvalue five is five cosine squared theta. This is the ordered Ritz gap. Multiply by tangent theta: the result is five sine theta cosine theta, equal to the residual length.

We have equality in the ordered Ritz tangent theorem. In particular, the factor one is optimal even if we restrict to genuine Ritz residuals.

The same data do not give equality in the analogous sine bound with the Ritz gap. That estimate has left side five sine theta cosine squared theta and right side five sine theta cosine theta. Their ratio is cosine theta. It is strictly less than one at every nonzero acute angle.

Sharpness belongs to a theorem with a specific hypothesis class, not to an informal family of similar-looking formulas.

## Why the gap must move with the trial space

Imagine holding five as the gap while switching from the fixed trial operator to the Ritz operator. Then we would claim that five tangent theta is bounded by five sine theta cosine theta. Dividing by positive sine theta gives one over cosine theta at most cosine theta, which is false for every nonzero angle.

The error is easy to locate. Five was the separation between zero and the unwanted eigenvalue. After choosing the Ritz operator, the relevant separation is five cosine squared theta.

This illustrates a general audit rule. A residual, a trial operator, and a gap form a linked set of data. We cannot exchange just one member while pretending the other two are unchanged.

## Why a pairwise gap may not give the same constant

Consider the Sylvester equation A X minus X B equals C. Take A diagonal with entries one and negative one, and B diagonal with entries zero and two. Every cross-spectral distance is at least one.

Take X with rows three, negative three and negative three, one. Direct multiplication gives C with rows three, three and three, negative three.

The operator norm of X is two plus the square root of ten, about five point one six. The operator norm of C is three times the square root of two, about four point two four.

So a pairwise gap of one does not imply the operator-norm estimate norm X at most norm C. The constant one fails even with symmetric diagonal coefficient matrices.

Why did constant one work in the sine and tangent examples? Their spectral hypotheses are stronger. Ordered gaps or an appropriate interval-versus-exterior configuration support the needed Sylvester estimate. Mere pairwise distance can give a different operator-norm constant.

In Frobenius norm, the same pairwise spectral separation does give constant one. When A and B are diagonal, each entry of C equals a spectral difference times the corresponding entry of X. Squaring absolute values, adding, and taking square roots preserves the entrywise lower bound.

The operator norm does not add squared entries. Interactions among rows and columns can make a candidate bound fail even when each individual entry is controlled.

## Learn the three familiar norm classes from singular values

Take the diagonal matrix with entries one and one. Its singular values are one and one. The operator norm is one, the Frobenius norm is the square root of two, and the nuclear norm is two.

For a diagonal matrix with m ones, these values become one, square root of m, and m. Thus changing norms can introduce dimension factors. A bound established in one norm cannot automatically be copied with the same numerical values into another norm.

If the proof is compatible with every unitarily invariant norm, it can be specialized separately to each one. That is stronger than observing an inequality in operator norm and changing the labels afterward.

## Duplicate a sharp example in independent blocks

Now take m mutually orthogonal copies of the sharp planar sine example. Put their operators and trial frames in block-diagonal form, all at the same angle and gap.

The sine representative has m identical nonzero singular values. Its operator norm is their common value. Its Frobenius norm is square root of m times that value. Its nuclear norm is m times that value.

The corresponding residual singular values scale by the same gap, so equality persists in each of these norms when the direct-sum construction satisfies the theorem's hypotheses.

This is the reason operator ideals and symmetric gauges enter the Davis–Kahan development. A proof that treats all singular-value prefixes correctly retains its meaning after independent geometric directions are added.

## The role of Ky Fan inequalities

Suppose we can establish that, for every positive integer k, the sum of the k largest singular values of an angular operator is at most a constant times the sum of the k largest residual singular values.

That is weak majorization. The symmetric-gauge descent machinery turns it into bounds for every unitarily invariant norm in the supported class. The proof works because every permitted gauge is monotone under this prefix-sum relation.

Conversely, a proof controlling only the largest singular value says nothing by itself about the entire sum of singular values. A family could have one small maximum but thousands of comparable directions. The nuclear norm would detect their aggregate contribution.

In infinite dimensions we must also ask whether the angular operator belongs to the stated ideal. A finite scalar-looking upper bound does not excuse omitting that membership conclusion.

## Ratios that reveal the correct constant

For a proposed inequality, divide the left side by the right side whenever the denominator is nonzero. An example with ratio one proves sharpness for a coefficient one. An example with ratio greater than one disproves that coefficient. Under parameter limits, a ratio approaching one can also prove optimality even if equality is never attained.

But a ratio is meaningful only after checking the hypotheses. In particular, a spectral gap cannot be chosen larger than the actual certified separation, and a selected spectral subspace cannot be exchanged for another without justification.

The same discipline applies to doubled-angle estimates. Their factors of two and possible forty-five-degree branch restrictions must follow from the reflection geometry and the exact spectral hypotheses, rather than from numerical guesses.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Three audit examples:

1. Fixed trial scalar `M=0`, `A=diag(0,5)`, `e=(cosθ,sinθ)`: `δ=5`, `‖R‖=5sinθ=δsinθ`.
2. Ritz trial scalar `M=5sin²θ`: `δ=5cos²θ`, `‖R‖=5sinθcosθ=δtanθ`.
3. Pairwise separated Sylvester counterexample: `A=diag(1,-1)`, `B=diag(0,2)`, `X=[[3,-3],[-3,1]]`, `C=[[3,3],[3,-3]]`, `‖X‖=2+sqrt(10)>3sqrt(2)=‖C‖` at `δ=1`.

The first is sharp for a non-Ritz sine theorem; the second is sharp for the Ritz tangent theorem; the third refutes an operator-norm constant-one claim under a *mere pairwise* gap. Their hypotheses must not be interchanged.

### Source declaration excerpts

`DavisKahan/Sources/DavisKahan1970/SineTheta/Sharpness.lean` — `planarResidual` (exact declaration header; body omitted):

```lean
noncomputable def planarResidual (delta theta : ℝ) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
```

`DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` — `tanTheta_residual_le` (exact declaration header; body omitted):

```lean
theorem tanTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) :=
```

`DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean` — `sharp52_constant_one_too_small` (exact declaration header; body omitted):

```lean
theorem sharp52_constant_one_too_small :
    ‖sharpC52.toContinuousLinearMap‖ < 1 * ‖sharpX52.toContinuousLinearMap‖ := by
```

**Mapping.** The `tanTheta_residual_le` API requires the Ritz identity and an `OrderedGap`; the source's explicit sharp Sylvester witness is relevant only to a proposed pairwise-distance bound. The finite-dimensional singular-value and unitarily invariant norm instances explain why operator, Frobenius, and nuclear conclusions are distinct norm statements.
