# 104000 — Real versions of unbounded Sylvester bounds

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `090000` form gaps, `093000` domain-aware Sylvester equations, `094000` unbounded Sylvester estimates, `096000` approximation numbers, `102000–103000` real complexification and spectral descent. **Next:** `105000` proof-readiness assembly.

<!-- BEGIN SPOKEN LECTURE -->

# Solving a real Sylvester equation by temporarily using complex space

Consider two real diagonal matrices. Let A have diagonal entries three and five. Let B have diagonal entries negative one and negative two.

We want to find a matrix X satisfying this equation: A times X, minus X times B, equals a given matrix C.

For a single entry of X, the equation is simple. The entry is multiplied by an eigenvalue of A minus an eigenvalue of B.

For the upper-left entry, that number is three minus negative one, or four. So if C has a one in its upper-left corner and zeros elsewhere, X has one quarter there and zeros elsewhere.

Why is the number four important? Every eigenvalue of A is at least three, and every eigenvalue of B is at most negative one. There is a gap of four between the two spectral regions.

That gap gives a uniform scale for the solution. For our particular C, the norm of X is exactly one quarter of the norm of C.

Our goal is to extend this reasoning to possibly unbounded self-adjoint operators on real Hilbert spaces, and to symmetric operator ideal gauges. We'll use complexification to transport a complex Sylvester theorem back to the real setting without changing the gap constant.

## From entrywise division to an operator estimate

In the matrix example, each entry of X is the corresponding entry of C divided by the difference between one eigenvalue of A and one of B.

It is tempting to say that since all denominators have absolute value at least four, every matrix norm must shrink by at least a factor of four.

That conclusion doesn't follow from entrywise comparison for an arbitrary matrix norm. Singular values depend on how entries combine. We need an argument that controls the whole operator.

For ordered self-adjoint spectral regions, a useful argument comes from an integral. When A is positive and B is negative in the appropriate shifted sense, we can build X by integrating the operators that decay under A on the left and under B on the right.

In our example, A is at least three and B is at most negative one. For positive time t, the norm of the left decay factor is at most the exponential of negative three t. The norm of the right factor is at most the exponential of negative one t. Together they give the exponential of negative four t.

Integrating that scalar upper bound over all positive times gives one quarter. This explains the operator-level constant for an ordered gap, without pretending that entrywise bounds alone prove it.

For general unbounded operators and general symmetric ideals, we must also justify the domains, the exact gap condition, and ideal membership.

## The domain-aware real problem

Let A be a possibly unbounded self-adjoint operator on a real Hilbert space E. Let B be a possibly unbounded self-adjoint operator on another real Hilbert space F.

The unknown X and the given right-hand side C are bounded real-linear maps from F to E.

The Sylvester equation is A X minus X B equals C.

That formula needs a precise meaning when A and B are unbounded. We require X to take each vector in the domain of B into the domain of A. Only then can A X be applied to that input.

On every vector in the domain of B, we require A X x minus X B x to equal C x.

Notice the asymmetry. B acts first on the input space F, while A acts after X has carried the input to E. The domain condition ensures that both sides are legal.

We also require a positive number delta and a particular form-bounded spectral-gap hypothesis. Ordered separation is one covered configuration. An interval-versus-exterior configuration is another. Arbitrarily disjoint spectra are not enough to invoke every constant-one ideal estimate.

## Complexifying an unbounded domain

Here's the important step that doesn't appear in elementary matrix algebra.

If A is defined only for certain real vectors, then its complexification must be defined only for x plus i y when both x and y belong to the domain of A.

Why both? Because multiplication by i exchanges the real and imaginary components. A domain containing x plus i y but rejecting negative y plus i x would fail to be a complex vector subspace.

On this complexified domain, define the new operator by applying A separately to x and to y.

The original graph of A is closed because A is self-adjoint. The graph of the complexification is built from two copies of that closed graph, so it is closed too. Density of the domain transfers coordinatewise.

The adjoint-domain relation transfers as well, and with it self-adjointness. Thus the complexified A and B are legitimate complex self-adjoint operators.

Now take the real Sylvester equation. X maps the domain of B into the domain of A. Applying that statement separately to x and y shows that complexified X maps the complexified B domain into the complexified A domain.

Apply the real equation to both components and combine them. We obtain the complex Sylvester equation with complexified C on the right.

The operator equation survives because its domain conditions have survived.

## Check that the spectral gap survives

Suppose A is bounded below by three and B is bounded above by negative one, as in our example. Their complexified quadratic forms at x plus i y are sums of the corresponding real quadratic forms at x and y.

Therefore the same lower and upper bounds hold, giving the same ordered gap of four.

The argument also handles reversed ordering. For the covered interval-versus-exterior form-gap branch, preservation of self-adjoint spectral information and resolvent behavior supplies the corresponding transfer.

What we gain is precise: the complex operators satisfy the same kind of hypothesis, with the same positive delta. Complexification does not turn an arbitrary pairwise gap into a stronger ordered gap.

We can now apply the complex unbounded Sylvester estimate.

## Why finite Ky Fan sums come first

For a fixed positive integer k, the Ky Fan gauge sums the first k approximation singular values of a bounded operator.

The complex Sylvester theorem gives an estimate of this form: delta times the k-th Ky Fan gauge of complexified X is at most the k-th gauge of complexified C.

But we're after a theorem about real operators. How do we know the complexification hasn't changed the relevant singular-value data?

For a finite real matrix, the answer is clear: viewing the same real matrix over the complex numbers doesn't change its singular values.

For arbitrary Hilbert-space operators, the appropriate fact is equality of approximation numbers. One direction follows by complexifying real finite-rank approximations. For the reverse direction, the singular-value min–max characterization shows that the real and complex problems have the same lower-bound witnesses after extending their spans appropriately.

Thus every approximation number is preserved by complexification, and every finite Ky Fan prefix is preserved exactly.

We can remove the word complexified from the inequality. For each k, delta times the real k-th Ky Fan gauge of X is at most that of C.

No extra factor appears.

## From prefixes to an arbitrary symmetric ideal

A finite-prefix inequality is not yet a theorem about an entire operator ideal.

Some ideals contain only a proper subset of bounded operators. To say that X has finite trace norm, for example, we must first know that X is trace class.

Assume we're working with a real symmetric ideal family that has Ky Fan dominance, and assume C belongs to that ideal.

We have shown that every finite Ky Fan prefix of X is bounded by the corresponding prefix of C divided by delta. The dominance property now supplies both conclusions: X also belongs to the ideal, and its ideal gauge is at most the gauge of C divided by delta.

For our two-dimensional example with C supported in the upper-left corner, this estimate is an equality in operator norm, Hilbert–Schmidt norm, and trace norm. Both the gap and the factor of one are visible directly from the solution with entry one quarter.

If we replace the two coordinates with infinitely many real coordinates and let the diagonal entries grow without bound, A and B can be unbounded. We then have to restrict their domains so their weighted output sequences remain square summable. The same complexification and gap reasoning still applies.

The completed conclusion has three essential ingredients: a legal domain-aware Sylvester equation, an allowed positive form-gap hypothesis, and ideal membership of C together with Ky Fan dominance. Under those assumptions, X belongs to the ideal and delta times its gauge is no greater than the gauge of C.

This is why complexification is effective. It allows the complex spectral argument to do the analytic work while returning the same real operator estimate, the same ideal membership, and the same numerical gap.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

The domain-aware real equation has `A : E →ₗ.[ℝ] E`, `B : F →ₗ.[ℝ] F`, `X C : F →L[ℝ] E`, `X(B.domain) ⊆ A.domain`, and `(AX−XB)x=Cx` on `B.domain`. Partial-map complexification transports closed domains, self-adjointness, resolvents, form bounds, and the Sylvester equation. Approximation numbers and all finite Ky Fan prefixes are exactly preserved. A real `SymmetricOperatorIdealFamily` needs `IsKyFanDominant` and `N.Mem C` to derive `N.Mem X` together with `δ N.gaugeReal X ≤ N.gaugeReal C`.

### Worked example: ordered-gap real Sylvester equation

Let \(A=\operatorname{diag}(3,5)\) and \(B=\operatorname{diag}(-1,-2)\) on \(\mathbb R^2\). The ordered form gap is \(\delta=4\). For \(C=e_1e_1^*\), the solution to \(AX-XB=C\) is \(X=\tfrac14e_1e_1^*\), attaining \(\delta\|X\|_{\mathcal I}=\|C\|_{\mathcal I}\) for operator, Hilbert–Schmidt and trace norms.

If \(A=\operatorname{diag}(n+2)\) and \(B=\operatorname{diag}(-n)\) on real \(\ell^2(\mathbb N_{\ge1})\), both are unbounded self-adjoint diagonal operators on their maximal weighted-square-summability domains. The same ordered lower and upper bounds produce \(\delta=4\). Their complexifications have domains consisting of pairs of vectors in the corresponding real domains.

### Actual Lean source declarations

`DavisKahan/SpectralTheory/PartialMap/Complexification.lean` — `mem_domain_iff` (exact declaration header; proof omitted):

```lean
@[simp] theorem mem_domain_iff
    (A : E →ₗ.[ℝ] E)
    (z : Eℂ) :
    z ∈ domain A ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
```

`DavisKahan/SpectralTheory/PartialMap/Complexification.lean` — `closedSylvesterEquation_complexify` (exact declaration header; proof omitted):

```lean
theorem closedSylvesterEquation_complexify
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {X C : F →L[ℝ] E}
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C) :
    _root_.LinearPMap.SylvesterEquation (complexify A) (complexify B)
      (RealComplexification.complexify X)
      (RealComplexification.complexify C) := by
```

`DavisKahan/SpectralTheory/PartialMap/Complexification.lean` — `isSelfAdjoint_complexify` (exact declaration header; proof omitted):

```lean
theorem isSelfAdjoint_complexify
    {A : E →ₗ.[ℝ] E}
    (hA : IsSelfAdjoint A) :
    _root_.IsSelfAdjoint (complexify A) := by
```

`DavisKahan/OperatorIdeal/ComplexificationApproximation.lean` — `kyFanApproximationGauge_complexify` (exact declaration header; proof omitted):

```lean
theorem kyFanApproximationGauge_complexify
    (T : E →L[ℝ] F) (k : ℕ) :
    ((RealComplexification.complexify T).kyFanGauge k : ℝ) =
      (T.kyFanGauge k : ℝ) := by
```

`DavisKahan/Sylvester/RealUnbounded.lean` — `davisKahan1970_sylvester_real` (exact declaration header; proof omitted):

```lean
theorem davisKahan1970_sylvester_real
    (N : TauCeti.SymmetricOperatorIdealFamily ℝ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gaugeReal X ≤
        N.gaugeReal C := by
```

**Type and hypothesis map.** The complex partial-map domain has real and imaginary coordinates in the original domain. `closedSylvesterEquation_complexify` transports an equation with legal domain compositions; self-adjointness and the form-gap conditions are transported separately. Finite Ky Fan gauges are preserved exactly for real bounded maps. The real Sylvester conclusion assumes a `SymmetricOperatorIdealFamily ℝ`, its `IsKyFanDominant` instance, positive `δ`, a `FormBoundedSylvesterGap`, the domain-aware equation, and `N.Mem C`; it returns both `N.Mem X` and the scaled real gauge bound.

These Lean snippets are copied exactly from the supplied DKPS repository snapshot. The narration is an independent mathematical derivation; this appendix does not claim that the narrated text was compiled in Lean. Foundational results currently in `ForTauCeti` may have been developed in DKPS before upstreaming.
