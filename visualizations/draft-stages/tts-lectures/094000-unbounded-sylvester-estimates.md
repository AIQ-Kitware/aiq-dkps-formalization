# 094000 — Unbounded Sylvester estimates

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `065000` ordered spectral separation, `069000` norm dependence, `090000` half-line form gaps, `092000` unitary groups, `093000` domain-aware Sylvester identities. **Next:** `095000` compactness and finite-rank approximation.

<!-- BEGIN SPOKEN LECTURE -->

# A spectral gap turns into a bound on a Sylvester solution

Suppose two numbers lie on opposite sides of a gap. One is three, and the other is negative one. Consider the equation: three times an unknown, minus the unknown times negative one, equals a prescribed number c.

The unknown is c divided by four. And four is the distance between those two numbers.

This is the scalar version of a Sylvester equation. If we replace the two numbers by self-adjoint operators, does separation of their spectra still control the solution?

Yes, provided we state the separation and the operator domains correctly. The striking part is that the two coefficient operators may be unbounded, yet their Sylvester solution can be bounded by the reciprocal of the gap.

We will see why an integral of decaying exponentials produces the solution, and why a domain argument is needed before the formula really solves the equation.

## From division by a gap to an integral

Return to the scalar equation. Three minus negative one is four, so the answer is c divided by four.

There is another way to produce that number. Multiply c by the exponential of negative four times time, then integrate from time zero to infinity. The integral equals c divided by four.

Why use the integral instead of ordinary division? Because for operators, the expression A X minus X B contains multiplication on different sides of the unknown X. We cannot in general factor X and divide by A minus B as if they were scalar numbers.

But we can still multiply by an exponential of A on the left, multiply by an exponential of B on the right, and integrate the result.

This leads to a construction that works even when A and B are unbounded.

## What an ordered spectral gap means

Let A be self-adjoint on a Hilbert space E and B self-adjoint on a possibly different Hilbert space F.

Suppose every spectral value of A lies at or above a real number a. Suppose every spectral value of B lies at or below a smaller number b.

Define delta to be a minus b. Delta is positive. It is an ordered spectral gap: all the spectrum of A lies above all the spectrum of B.

Let C be any bounded map from F to E. We seek a bounded map X, also from F to E, satisfying A X minus X B equals C.

Because the operators can be unbounded, this equation comes with a domain condition. For every y in the domain of B, X y must belong to the domain of A. Only then can we demand that A X y minus X B y equal C y.

Notice that neither A nor B needs a finite operator norm. The useful hypotheses are one-sided spectral bounds and a strictly positive gap.

## Why the integral converges

For nonnegative time t, consider the exponential of negative t A. Because A is bounded below by a, its spectral multiplier is at most the exponential of negative a times t. The spectral theorem therefore defines a bounded operator, even when A itself is unbounded.

Likewise, because B is bounded above by b, the exponential of positive t B is bounded in norm by the exponential of b times t.

Now compose three maps. First apply the exponential of t B to a vector in F. Then apply C to move into E. Finally apply the exponential of negative t A.

The norm of this composition is at most the norm of C times the exponential of negative delta times t.

That is the essential calculation. The exponent is negative because a is greater than b. The two spectral bounds work together to produce decay.

Individually, one exponential might not decay. If a is negative, the upper bound for the left exponential may grow. If b is positive, the upper bound for the right exponential may grow. But their product still decays at the gap rate.

Integrate the three-map composition from time zero to infinity. For each fixed input y, the integrand is a continuous E-valued function, and its length is bounded by an integrable exponential.

So the integral defines a vector X y and therefore a bounded linear operator X.

Integrating the norm estimate gives the bound: the norm of X is at most the norm of C divided by delta.

We have already obtained the quantitative result. A larger ordered gap forces a smaller response to a fixed forcing term C.

But there is something we have not proved yet.

## A bounded integral is not automatically a solution

The estimate says X is bounded. It does not say X maps the domain of B into the domain of A.

If we formally differentiate the integrand with respect to time, we get negative A applied on the left, plus B applied on the right. Integrating that derivative should give the desired Sylvester equation.

The problem is that writing A times the integral could be illegal. An unbounded operator cannot simply be passed through an integral without a domain argument.

There are two ways to make the calculation rigorous. One uses cutoffs and closedness. Another uses the adjoint and test vectors. The second is especially instructive because it makes the missing domain condition appear at the end of the calculation.

Take an input y from the domain of B. Then choose a test vector x from the domain of A.

Instead of applying A to the unknown X y, pair the integrand with x. Because A is self-adjoint, we may move A onto the legal test vector x. And because y belongs to the domain of B, we can differentiate the exponential of t B applied to y.

Now the scalar pairing can be differentiated without ever assuming that X y already belongs to the domain of A.

Integrate that scalar derivative from zero to a finite time T. At time zero, both exponentials are the identity, so the initial term is the pairing with C y.

At time T, the exponential gap estimate shows that the remaining boundary term tends to zero as T grows.

After taking the limit, we obtain this statement: for every test vector x in the domain of A, the pairing of A x with X y equals the pairing of x with X B y plus C y.

What does that mean?

The expression on the right is the inner product with a fixed Hilbert-space vector, namely X B y plus C y. So the functional that sends x to the pairing of A x with X y is represented by a Hilbert-space vector.

That is precisely the criterion for X y to belong to the domain of the adjoint of A.

Since A is self-adjoint, its adjoint is A itself, with the same domain. Therefore X y belongs to the domain of A, and A X y equals X B y plus C y.

Rearrange, and we have the desired Sylvester equation on the domain of B.

The weak calculation has supplied exactly what the formal calculation was missing: a proof that the output of X is a legal input for A.

## Why the bounded solution is unique

Could there be another bounded operator Y satisfying the same equation and domain condition?

Subtract the two solutions and call the difference Z. The forcing terms cancel, giving A Z minus Z B equals zero on the domain of B.

Consider the same three-part composition used in the integral, but replace C with Z. At time t it is the exponential of negative t A, followed by Z, followed by the exponential of t B.

Because Z solves the homogeneous equation, differentiating appropriate test-vector pairings shows that this composition does not change with time. It remains equal to Z.

On the other hand, the ordered spectral gap bounds its norm by the norm of Z times the exponential of negative delta times t. That upper bound tends to zero as time grows.

A constant bounded operator that tends to zero must be the zero operator. Hence Z is zero, and the two solutions coincide.

We have existence, domain preservation, uniqueness, and a quantitative norm estimate.

## See the sharp constant in an infinite example

Take E and F both equal to ell two. Let A multiply coordinate N by N plus two, and B multiply it by negative N, for N starting at one.

The spectrum of A begins at three and increases without bound. The spectrum of B begins at negative one and decreases without bound. So their ordered gap is four.

Let C be the identity. On coordinate N, our integral has multiplier equal to the integral of the exponential of negative two N plus two times t.

That integral is one divided by two N plus two. Thus X multiplies coordinate N by one divided by two N plus two.

The largest multiplier is one fourth, on coordinate one. Therefore the norm of X equals one fourth, the norm of C equals one, and the gap equals four.

The bound is attained exactly. The constant one in the ordered-gap estimate cannot be lowered in general.

Notice what the example has accomplished. A and B are both unbounded. X is bounded. We can check the domain mapping directly, and the numerical norm bound is sharp.

## When separation has no single direction

Now suppose the two spectra are separated by a positive distance but their pieces alternate along the real line. Some spectral values of A may lie above B, while other values lie below it.

There is no single choice of the two exponentials that makes every spectral difference decay in the same time direction. So the ordered-gap integral no longer provides the same constant-one proof.

There is a more general Sylvester theorem for self-adjoint operators whose spectra have positive distance without an ordering assumption. It uses a two-sided integral of unitary groups with a Fourier kernel representing reciprocal spectral differences.

That argument gives a universal operator-norm bound with the factor pi divided by two in place of one. In the unbounded setting, the bounded solution must again satisfy the strong, domain-aware Sylvester equation.

The change of constant reflects a genuine change of hypothesis. Positive distance between spectral sets is weaker than putting all of one set strictly above all of the other.

## Turn the bound into an angle estimate

One important application comes from perturbing a self-adjoint operator A by a bounded self-adjoint V.

Let P select a spectral subspace of A, and let Q select a spectral subspace of A plus V. Consider the map that takes vectors in the range of Q and projects them onto the orthogonal complement of the range of P.

That cross map measures the directed sine of the angles between the selected subspaces. A domain-aware calculation shows that it satisfies a Sylvester equation. The forcing term is a compression of V, so its norm is no greater than the norm of V.

If the corresponding restricted spectra have an ordered gap delta, the theorem gives a directed-sine bound: the norm of the cross map is at most the norm of V divided by delta.

The same mechanism explains the structure of more refined perturbation estimates. Spectral separation controls the solution of an operator equation. That solution describes how much a selected subspace points into the complementary directions.

The ordered-gap estimate is therefore a precise bridge between the location of spectra and the geometry of spectral subspaces, valid even when the underlying self-adjoint operators are unbounded.

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
