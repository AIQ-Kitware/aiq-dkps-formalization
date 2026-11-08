# 089000 — Spectral projections and reducing domains

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `010000` orthogonal complements, `015000` reducing subspaces, `076000` projection-valued measures, `088000` unbounded domain calculus. **Next:** `090000` quadratic forms and ordered half-infinite gaps.

<!-- BEGIN SPOKEN LECTURE -->

# A subspace must reduce the domain as well as the operator

We know how to split a bounded self-adjoint operator into blocks along a spectral subspace. For an unbounded operator we must ask a prior question. If we project a legal input onto the selected subspace, is the result still a legal input? Without that property, even writing a block matrix for the operator may be meaningless.

Today we will define the right conditions, prove that spectral projections satisfy them, and construct the self-adjoint operator obtained by restricting to a spectral subspace. This supplies the precise block operators used in unbounded Davis–Kahan estimates.

## The domain is part of the operator

Let A be self-adjoint on a complex Hilbert space H. Its domain, which we call D of A, is dense in H but need not equal H.

Let P be an orthogonal projection, and M its range. If A were bounded, we could write A as four blocks using P and its complement. In particular, the upper-left block would take x in M to P A x.

For an unbounded A, A x is defined only if x is in D of A. A formula such as P A P x is valid only after verifying that P x lies in D of A. We therefore require that P carry D of A into itself.

That is the first reducing-domain condition. The second is that A applied to P x equals P applied to A x, for every x in D of A. This is commutation on the operator domain, not an equality of everywhere-defined bounded operators.

Together these properties imply that the complementary projection, identity minus P, also preserves the domain and commutes with A. Just subtract the first identity from A x, and use linearity of the domain.

So both M and its orthogonal complement are preserved, and the action of A separates into two pieces.

## Why spectral projections pass the domain test

Let E of B be the spectral projection of A onto a Borel set B of real spectral values. Write P for this projection.

The spectral theorem describes A by integration against E. It also describes its domain through a square-integrability condition: a vector x is legal precisely when its spectral measure has a finite second moment.

Projecting x onto B discards all spectral contributions outside B. It cannot increase that nonnegative integral. Therefore, if x belongs to D of A, so does P x.

Next, compare A P x with P A x. The first action multiplies the spectral values in B by lambda. The second first multiplies all spectral values by lambda and then discards those outside B. The two operations give the same spectral integral. Hence A P x equals P A x on the domain.

Notice what we have proved. A measurable spectral set can be unbounded. The projection P itself is bounded, but the restricted operator may remain unbounded. Domain invariance does not depend on B being a bounded interval.

## Constructing the operator part

Define A restricted to M on the domain consisting of vectors that lie in both D of A and M. Its output is A x. We already proved that this output lies in M.

The resulting map, call it A M, is densely defined in M. To see this, start with a vector y in M. Because D of A is dense in H, choose domain vectors x n approaching y. Their projections P x n still belong to D of A, now lie in M, and approach P y, which equals y.

The operator A M is symmetric because A is symmetric. The remaining question is whether it is self-adjoint. Symmetry alone does not settle that question for unbounded operators.

Here the resolvent makes the proof clean. Take a nonreal complex number z. Self-adjointness of A implies that A minus z times the identity maps D of A bijectively onto H, with a bounded inverse.

The projection P commutes with that inverse. To prove it, set x equal to the inverse applied to y. We know x is in D of A. Commutation on the domain gives A minus z applied to P x equals P y. By uniqueness of the inverse, P x is the inverse applied to P y.

Consequently the inverse preserves M. If y lies in M, the vector x obtained this way also lies in M and solves the restricted resolvent equation. Thus A M minus z maps its domain onto M. Using both signs of the imaginary part, the usual resolvent criterion shows that A M is self-adjoint.

This proof verifies density, symmetry, domain preservation, and self-adjointness separately. None is being assumed from a formal block-matrix picture.

## A concrete infinite-dimensional split

Return to ell two, the space of square-summable sequences. Let A multiply the N-th coordinate by N, with N starting at one. Its domain consists of sequences for which the sum of N squared times the squared coordinate magnitudes is finite.

Let P keep even-numbered coordinates and erase odd-numbered coordinates. This is a spectral projection, since the eigenvalues of A are precisely the positive integers.

If a sequence x is in the domain, its even-coordinate subsequence is also in the domain. Applying A before or after discarding odd coordinates gives the same result. The restriction to even coordinates is an unbounded self-adjoint operator on the even-coordinate subspace. The odd-coordinate restriction is another such operator.

This is a literal orthogonal decomposition of the Hilbert space and its operator domain. Each piece retains the appropriate weighted square-summability condition.

Now take instead the projection onto the span of the vector with first and second coordinates equal. The domain condition poses no problem for this finite-dimensional range, but the commutation condition fails: A changes the two coordinates by different factors. This is a projection onto a perfectly legitimate subspace, but not a reducing spectral subspace for A.

The distinction becomes important when a trial subspace is almost invariant. It does not necessarily provide an exact reducing restriction.

## Resolvents and the spectrum of a restriction

Because the restricted resolvent is simply the original resolvent restricted to M, spectral values of A M must lie in the spectral region selected by P. More precisely, the spectrum of the restriction lies in the closed support of the spectral measure on that subspace.

Do not identify the selected Borel set itself with the restricted spectrum. A set B might contain points that carry no spectral mass, and it may omit limit points that nevertheless belong to the spectrum of the restriction. The spectrum is closed, while a Borel set need not be.

Consider a multiplication operator on square-integrable functions over the real line, and select the open interval from zero to one. The restricted multiplication operator has spectrum the closed interval from zero to one. The endpoints can belong to its spectrum even though the selected set was open.

For a spectral gap estimate we must formulate separation using the actual restricted spectra, or using verified half-line bounds that imply the separation we need.

## Why this prepares a sine-theta proof

Imagine comparing A with a bounded perturbation, A plus V. A spectral projection P of A reduces A, and a spectral projection Q of the perturbed operator reduces A plus V. Because V is bounded, both unbounded operators have the same domain.

The cross map from Q H into the complement of P H is bounded. To obtain its Sylvester equation, however, we must first check that domain vectors in Q H are carried into the domain of the restricted operator on the complement of P H. The spectral-domain facts proved today make that possible.

Only after constructing the two self-adjoint restrictions can we apply a spectral separation estimate to the cross map. That order of operations is the main lesson.

Spectral projections supply a geometrical decomposition, a legal decomposition of the domain, and self-adjoint restricted operators. All three are required for the perturbation bounds that follow.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:D(A)\subset H\to H\) be self-adjoint and \(P=E_A(B)\) a spectral projection. Then \(P D(A)\subset D(A)\), \(APx=PAx\) for \(x\in D(A)\), and \(D(A_P)=D(A)\cap\operatorname{ran}P\). The restriction \(A_P\) is self-adjoint on \(\operatorname{ran}P\). Its resolvent is the restriction of the full resolvent, with \(P(A-z)^{-1}=(A-z)^{-1}P\). The spectrum of the restricted operator is contained in the support of the restricted spectral measure, not generally equal to the original Borel selector.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_mem_domain`:

```lean
theorem specProjection_mem_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    specProjection hA B hB (x : H) ∈ A.domain := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_apply_domain`:

```lean
theorem specProjection_apply_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩
      = specProjection hA B hB (A x) := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `isSelfAdjoint_specRestrict`:

```lean
theorem isSelfAdjoint_specRestrict : IsSelfAdjoint (specRestrict hA B hB) := by
```


**Type and hypothesis map.** In Lean, `A : H →ₗ.[ℂ] H` is the partially defined linear operator, and `A.domain` is the set of legal input vectors. `hA : IsSelfAdjoint A` supplies self-adjointness, while `(B : Set ℝ)` and `(hB : MeasurableSet B)` authorize a spectral selector. The first theorem proves `specProjection` preserves the domain; the second explicitly inserts that membership proof into the typed application of `A`; the final theorem states self-adjointness of `specRestrict`, the true operator part on the selected spectral range. Its proof in the source uses the domain-preserving resolvent and density, precisely the steps derived in the lecture.

**Scope:** The snippets exhibit spectral-subspace construction, domain preservation and domain-aware commutation. The narrated self-adjoint restriction proof uses the standard nonreal resolvent criterion and is not claimed to be entirely encapsulated by these excerpts. Source declarations are taken from the supplied DKPS snapshot, which includes DKPS-origin results subsequently upstreamed to TauCeti; these excerpts are not newly compiled Lean code.
