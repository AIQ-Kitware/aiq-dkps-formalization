# 094000 — Unbounded Sylvester estimates

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `065000` ordered spectral separation, `069000` norm dependence, `090000` half-line form gaps, `092000` unitary groups, `093000` domain-aware Sylvester identities. **Next:** `095000` compactness and finite-rank approximation.

<!-- BEGIN SPOKEN LECTURE -->

# A bounded solution from two unbounded operators

We now have the ingredients for a central result: two self-adjoint operators can be unbounded, yet their Sylvester equation may have a bounded solution with a sharp norm estimate.

The crucial assumption in our first proof is that the spectra are ordered across a positive gap. We will construct the solution by an exponentially decaying integral, verify the unbounded equation on its legal domain, prove uniqueness, and connect the estimate to sine-theta perturbation bounds.

## Set up the ordered equation

Let A be self-adjoint on a Hilbert space E, and B self-adjoint on a Hilbert space F. Suppose A is bounded below by a real number a and B is bounded above by a real number b, where a is strictly greater than b.

Set delta equal to a minus b. It is positive.

Let C be any bounded map from F into E. We seek a bounded map X such that X sends D of B into D of A, and A X y minus X B y equals C y for every y in D of B.

Observe that the two source and target spaces need not be the same. We cannot assume either A or B has a finite operator norm. Only C and the desired solution X are required to be bounded.

## Construct the solution by an integral

For nonnegative time t, let the left semigroup be the exponential of negative t A, and the right semigroup the exponential of t B. Both are bounded by the spectral calculus.

Define X y, for each y in F, as the integral from zero to infinity of the left semigroup, followed by C, followed by the right semigroup, applied to y.

The earlier form estimates show that the norm of this integrand is bounded by the norm of C times the exponential of negative delta times t, multiplied by the norm of y.

Because delta is positive, this scalar function is integrable over the positive half-line. The integral therefore defines a vector X y, and the inequality shows that X is a bounded linear map.

The operator norm of X is at most the norm of C divided by delta. We have obtained the same constant-one estimate as in the bounded ordered-spectra theory without requiring A or B to be bounded.

This construction can be understood using vector-valued integration. For each y, the integrand is a continuous E-valued function of t with an integrable norm majorant. We form X y by integrating that function. Strong continuity is sufficient for this step; we need not pretend that the semigroups are continuous in operator norm at zero.

## The equation requires an additional proof

The integral estimate tells us that X is bounded. It does not yet prove that X y belongs to D of A when y belongs to D of B.

To establish the operator equation, take y in D of B and a test vector x in D of A. Consider the scalar inner product between x and the integrand at time t.

We may differentiate this scalar function. On the left, self-adjointness moves A from the potentially illegal output onto the test vector x, where A is defined. On the right, y belongs to D of B, so differentiating the B semigroup is legitimate.

The derivative is the negative pairing with A x plus the pairing involving B y. Integrate from zero to a finite time T. At zero the semigroups are identities, so the integrand is C y. At time T the exponential gap estimate makes the endpoint tend to zero as T tends to infinity.

After passing to the limit we obtain, for every test vector x in D of A, an identity that pairs A x with X y and pairs x with X B y plus C y.

This identity says that the functional obtained by pairing A x with X y is represented by the Hilbert-space vector X B y plus C y.

By the definition of the adjoint, this places X y in D of A star. Since A is self-adjoint, D of A star equals D of A. Its value is exactly X B y plus C y.

Rearranging gives A X y minus X B y equals C y. We have now verified both required parts of the domain-aware Sylvester equation.

The test-vector argument is the step that a formal manipulation of unbounded exponentials would omit.

## Uniqueness of a bounded solution

Suppose X and Y are two bounded solutions with the same C, both satisfying the domain-mapping condition. Their difference Z solves the homogeneous equation A Z minus Z B equals zero on D of B.

The ordered semigroup identity now implies that the function of t given by the exponential of negative t A, followed by Z, followed by the exponential of t B is constant in t.

To see this, differentiate pairings with domain test vectors. The derivative contains negative A Z plus Z B, which vanishes by the homogeneous equation. Density extends the result to every test vector.

At time zero the value is Z. But the exponential gap estimate bounds its norm by the norm of Z times the exponential of negative delta times t. This tends to zero as t grows.

The same operator cannot be both constant and convergent to zero unless it is zero. Therefore Z is zero and X equals Y.

Existence and uniqueness are both established. The estimate is independent of whether the two spaces are finite-dimensional.

## Sharpness on a diagonal model

Return to ell two. Let A have eigenvalues N plus two and B have eigenvalues negative N, with N starting at one. Their ordered spectral gap is four.

Take C to be the identity map. The integral defining X acts coordinatewise. On coordinate N, the integrand is the exponential of negative two N plus two times t. Its integral is one divided by two N plus two.

Thus X is diagonal with coefficients one divided by two N plus two. Its largest coefficient is one fourth, attained on the first basis vector.

The norm of C is one, the gap is four, and the norm of X is exactly one fourth. So the bound is attained. The constant one cannot be improved in this class of ordered-gap problems.

This example also makes the domain equation explicit: multiplying by A, subtracting the effect of B, and using the common denominator returns the original coordinate.

## What changes for spectra separated but not ordered

If two spectra have positive pairwise distance but interlace, the single decaying semigroup above is no longer available. We cannot choose one sign of time that makes all spectral differences decay simultaneously.

For bounded self-adjoint coefficients with separated spectra, a two-sided Fourier integral of unitary groups against a reciprocal kernel can solve the Sylvester equation. The construction gives an operator-norm estimate with the pi-over-two factor under its precise separation hypotheses. Unlike ordered-gap exponential decay, the method accommodates interlaced spectral sets.

The unbounded extension requires strongly continuous groups and the domain arguments we have just practiced. We should not silently replace a gap based on ordered half-lines by an arbitrary disjoint-spectrum hypothesis while retaining the same constant-one proof.

The Davis-Kahan estimate also has variants under ordered half-line separation and interval-versus-exterior spectral placement. These are specific gap configurations; simply assuming the two spectra are disjoint does not automatically justify the same constant.

## Return to subspace perturbations

Let A and A plus V be the two self-adjoint operators with a bounded perturbation of the original operator, with P and Q their selected spectral projections. Their compressed cross map X obeys a domain-aware Sylvester equation whose right side is a compressed part of V.

If the two restricted spectra are ordered across a positive gap delta, the theorem we proved gives the norm of X at most the norm of V divided by delta.

Because X is identity minus P restricted to Q H, its norm is the largest directed sine of the angle from Q H toward P H. We have therefore converted an unbounded operator perturbation into a geometrical angle estimate.

Controlling every singular-value prefix, rather than only the operator norm, allows ideal-norm estimates that account for many angular directions at once.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:D(A)\subset E\to E\) and \(B:D(B)\subset F\to F\) be self-adjoint with \(A\ge aI\), \(B\le bI\), \(\delta=a-b>0\), and bounded \(C:F\to E\). Then the strongly defined integral

\[
Xy=\int_0^\infty e^{-tA}C e^{tB}y\,dt
\]

produces a bounded solution with \(X D(B)\subset D(A)\) and \(AXy-XBy=Cy\) for \(y\in D(B)\). It satisfies \(\delta\|X\|\le\|C\|\); uniqueness follows from homogeneous intertwining and exponential decay. For \(A=\operatorname{diag}(n+2)\), \(B=\operatorname{diag}(-n)\) on \(\ell^2\), \(n\ge1\), and \(C=I\), we have \(X=\operatorname{diag}(1/(2n+2))\) and equality \(\delta\|X\|=\|C\|=1\).

### Actual source declarations

`DavisKahan/InfiniteDimensional/Sylvester/Basic.lean` — `norm_sylvester_le_of_orderedSeparation`:

```lean
theorem norm_sylvester_le_of_orderedSeparation
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec} {X C : Ec →L[ℂ] Fc}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : ContinuousLinearMap.sylvester A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
```

`DavisKahan/Sylvester/Unbounded/OrderedCutoff.lean` — `kyFan_unbounded_sylvester_le_of_semibounded_direct`:

```lean
theorem kyFan_unbounded_sylvester_le_of_semibounded_direct
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C) :
    ∀ k, δ * (X.kyFanGauge k : ℝ)
      ≤ (C.kyFanGauge k : ℝ) := by
```

`DavisKahan/Sylvester/Unbounded/FormBoundedGap.lean` — `davisKahan1970_sylvester_complex`:

```lean
theorem davisKahan1970_sylvester_complex
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gaugeReal X ≤
        N.gaugeReal C := by
```


**Type and hypothesis map.** The first theorem is intentionally the *bounded* `ContinuousLinearMap` ordered-gap estimate: its `OrderedSpectraSeparated` assumption corresponds to \(\delta\) separating all of B below all of A. The second theorem handles *partial* self-adjoint operators. Its explicit cutoff and truncation interfaces maintain the domain and gap conditions, and its conclusion is a finite Ky Fan gauge estimate for every `k`. The final source-facing theorem strengthens the result to an ideal membership and gauge comparison, under `FormBoundedSylvesterGap` and a `IsKyFanDominant` ideal hypothesis. This includes the ordered branch and certain interval/exterior branches, rather than arbitrary pairwise spectral separation with constant one.

**Scope:** The displayed source includes a bounded ordered-semigroup reconstruction, domain-aware unbounded Sylvester interfaces, and the source-facing unbounded form-gap theorem. The strong-integral proof in the narration provides the bridge; a bounded semigroup declaration alone is not cited as a formal proof of the unbounded extension. General pairwise spectral separation and its `π/2` estimate require different assumptions from the ordered half-line result. These excerpts were checked against the supplied DKPS source; no new Lean code was compiled.
