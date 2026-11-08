# 088000 — Unbounded spectral theorem and domain calculus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `074000` integration and L two, `076000` projection-valued measures, `082000` spectral cutoffs, `087000` Cayley transforms. **Next:** `089000` reducing domains.

<!-- BEGIN SPOKEN LECTURE -->

# The spectral theorem tells us the domain as well as the action

For bounded self-adjoint operators, we learned to integrate functions against spectral projections. The unbounded spectral theorem preserves that idea, but adds one indispensable condition: the vector on which we act must have enough spectral integrability.

Today we will derive the domain condition, recover the operator through bounded cutoffs, and work through explicit examples. The payoff is a calculus where every proposed unbounded expression has a precise legal domain.

## The projection-valued measure

Let A be self-adjoint on a complex Hilbert space H. Its spectral theorem provides a projection-valued measure E on the Borel subsets of the real line.

For every Borel set B, E of B is an orthogonal projection. Disjoint sets give orthogonal projections, and countable additivity holds in the strong sense: apply the projections to a fixed vector and the partial sums converge in the Hilbert norm.

For a fixed vector x, define a positive scalar measure mu x by taking the squared length of E of B applied to x. Its total mass is the squared length of x.

This scalar measure tells us how much of x occupies each spectral region. If the spectrum is continuous, the mass may be spread over intervals rather than concentrated at eigenvalues.

We will describe the operator A using this measure without assuming that an orthonormal basis of eigenvectors exists.

## The domain condition

First consider a bounded measurable function f on the real line. The operator f of A is bounded, and its output length squared is the integral of the squared absolute value of f against mu x.

Now allow f to be unbounded. We cannot apply f of A to every vector. Instead define its domain as the set of vectors x for which the integral of the squared absolute value of f against mu x is finite.

This condition has a concrete meaning. It says the spectral distribution of x decays fast enough, in the regions where f becomes large, that multiplication by f still produces a Hilbert-space vector.

The operator f of A is then defined as a limit of bounded spectral integrals. Truncate f to a sequence of bounded functions, and apply those bounded functions to x. Their outputs are Cauchy because the squared norm of their difference is an integral of the squared difference of their symbols. Dominated convergence, using the integrable quantity absolute f squared, makes that integral tend to zero.

The limit does not depend on the particular bounded truncations chosen, as long as they converge pointwise and are controlled appropriately. This constructs f of A on exactly its square-integrability domain.

For f of lambda equals lambda, the operator is A itself. Its domain consists of all x for which the integral of lambda squared against mu x is finite.

The same argument gives the norm identity: the squared length of A x equals that integral. It also gives the graph-norm formula: the graph norm squared is the integral of one plus lambda squared against mu x.

## Recovering A with interval cutoffs

Let P R be the projection onto spectral values from negative R to positive R. Every P R x belongs to the domain of A because the function lambda is bounded by R on that interval.

Define a bounded operator A R by integrating lambda only over that interval. Its norm is at most R, and its value at x agrees with A applied to P R x.

If x is in the domain of A, then P R x approaches x in Hilbert norm. Moreover A P R x equals P R A x. The right side approaches A x, so convergence holds in graph norm.

This provides a rigorous construction of A as the graph limit of its bounded spectral pieces. A R need not converge in operator norm; in fact, if A is genuinely unbounded, no sequence of bounded operators can converge to A in the ordinary bounded-operator norm, because A does not even belong to that normed operator space.

For a vector outside the domain, P R x still approaches x. But A P R x cannot converge in H. If it did, closedness of A would imply that x belongs to the domain, contradicting our assumption. Thus the domain can be recognized by whether the truncated outputs converge.

## A diagonal example with two different domains

Take the diagonal operator on ell two with N-th eigenvalue N. The scalar spectral measure of a vector x places mass equal to the squared magnitude of x N at the point N.

The condition for x to belong to the domain of A becomes convergence of the sum of N squared times the squared magnitudes of x N.

Take x N equal to one divided by N squared. This is in ell two, and applying A yields coordinates one divided by N, which are still square summable. Thus x is in the domain of A.

But x is not in the domain of A squared. Applying A twice would produce the constant sequence of ones, which is not square summable. Equivalently, the fourth-power spectral moment diverges.

So membership in the domain of A does not guarantee membership in the domain of A squared.

Likewise, the sequence with N-th coordinate one divided by N lies in the Hilbert space but outside the domain of A. The first spectral moment required for the output norm already diverges.

These examples show why a spectral formula and its domain must always be stated together.

## Continuous spectrum without eigenvectors

Consider square-integrable functions on the real line. Define A to multiply a function by its coordinate: at t, the output is t times the original function value.

The domain consists of functions for which the integral of t squared times the squared magnitude of the function is finite. The spectral projection E of B simply multiplies the function by the indicator of B.

A typical nonzero square-integrable function cannot be an eigenvector of A. If t times the function equaled lambda times the function, the function would have to vanish except perhaps at the single point lambda. A singleton has Lebesgue measure zero, so that function represents the zero vector in L two.

Nevertheless A has a rich spectrum: the entire real line. Its spectral measure and functional calculus work without any ordinary eigenvectors.

This is the reason projection-valued measures are necessary in infinite-dimensional perturbation theory. A decomposition into eigenvectors is not generally available.

## Products and the discipline of domains

If f and g are unbounded functions, f of A and g of A are both operators with domains. We cannot automatically multiply them on all of H.

The composition f of A after g of A is defined only for vectors x that first lie in the domain of g of A and whose g output then lies in the domain of f of A.

On that composition domain the product equals the spectral operator for the pointwise product f times g. But the natural domain of the pointwise product may be larger. For instance, if g vanishes where f grows, the product may be tame even though g by itself imposes a separate integrability condition.

So even a correct identity of scalar functions does not automatically imply equality of unbounded operators with their domains. We must check both the action and the domain.

For A squared there is a convenient simplification: the domain of the operator product A after A is exactly the set of vectors having a finite fourth-power spectral moment. That follows by applying the squared-norm identity first to x and then to A x.

## Back to Davis–Kahan

Suppose we want to select a spectral band, restrict an unbounded operator to it, and compare it with a perturbed operator. The spectral theorem gives a route: use the projection E of the band, verify preservation of the domain, and approximate domain vectors using bounded cutoffs.

It is only after these steps that we can write the residual block or a Sylvester identity without hiding an undefined term.

The unbounded spectral theorem thus supplies more than a way to compute functions of A. It provides a complete description of which vectors can be acted upon, and it makes graph-level approximation possible.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a self-adjoint \(A\) with projection-valued measure \(E\), put \(\mu_x(B)=\|E(B)x\|^2\). The domain of a measurable spectral operator is \(D(f(A))=\{x:\int |f(\lambda)|^2\,d\mu_x(\lambda)<\infty\}\). In particular \(D(A)\) requires the finite second spectral moment, and \(\|Ax\|^2=\int\lambda^2\,d\mu_x\). The cutoff \(P_R=E([-R,R])\) maps all of \(H\) into \(D(A)\), and for \(x\in D(A)\) satisfies \(AP_Rx=P_RAx\to Ax\), while \(P_Rx\to x\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_mem_domain`:

```lean
theorem specProjection_mem_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    specProjection hA B hB (x : H) ∈ A.domain := by
```

Spectral projections preserve the original operator domain.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_apply_domain`:

```lean
theorem specProjection_apply_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩
      = specProjection hA B hB (A x) := by
```

Commutation with an unbounded operator is a typed equality using an explicit proof of domain membership.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `tendsto_specProjection_Icc`:

```lean
theorem tendsto_specProjection_Icc (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
```

The bounded spectral-band projections converge strongly, pointwise on each Hilbert vector.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `truncation_eq_on_specProjection`:

```lean
theorem truncation_eq_on_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ = truncation hA B hB hbnd y := by
```

A bounded truncation agrees with the original operator on the selected bounded band.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `norm_truncation_apply_le`:

```lean
theorem norm_truncation_apply_le {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ‖truncation hA B hB hbnd y‖ ≤ max 0 M * ‖y‖ :=
```

The bounded truncation norm is controlled by the spectral-band radius.

**Scope:** The spectral-moment domain characterization is taught from the spectral theorem; these excerpts formalize the projected-domain, commutation, convergence and bounded-band aspects. They do not assert that arbitrary unbounded products have equal domains. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
