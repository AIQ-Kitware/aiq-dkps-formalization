# 093000 — Domain-aware Sylvester identities and cutoffs

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `071000` compressed Sylvester identities, `089000` reducing domains, `091000` bounded truncations, `092000` unitary groups. **Next:** `094000` unbounded Sylvester estimates.

<!-- BEGIN SPOKEN LECTURE -->

# An operator equation must be legal before we solve it

Consider the equation A times X, minus X times B, equals C. In matrix algebra, this is called a Sylvester equation. We know the shapes of the matrices, multiply them, subtract, and try to find X.

In an infinite-dimensional Hilbert space, the same equation can be meaningful when A and B are unbounded. But there is a question that finite-dimensional notation hides: are we allowed to apply A to the vector produced by X?

A bounded operator X can act on every vector. An unbounded operator A may act only on a dense, proper subspace. B may have its own domain, on a different Hilbert space.

Before estimating a solution, we must establish that the equation itself is defined. Let's make that concrete.

## The two requirements inside a Sylvester equation

Let B act on a Hilbert space F and A act on another Hilbert space E. Both are densely defined self-adjoint operators. Let X be a bounded map from F to E, and let C be another bounded map with the same input and output spaces.

Suppose we want A X minus X B to equal C.

Choose a vector y in the domain of B. We can apply B to y, then apply X, because X is defined on the whole space F. So X B y is legal.

But the other term, A X y, is legal only if X y belongs to the domain of A. Boundedness of X does not guarantee that.

For example, let B be the zero operator on all of ell two, let A multiply coordinate N by N on its weighted domain, and let X be the identity. X is bounded. Yet there are vectors in the domain of B that do not belong to the domain of A. The sequence with N-th coordinate one divided by N is one of them. On that vector, A X y is undefined.

So a domain-aware Sylvester solution must satisfy two statements. First, X carries every vector in the domain of B into the domain of A. Second, for those vectors, the difference A X y minus X B y equals C y.

The first statement makes the second one a legitimate mathematical assertion.

## Solve a diagonal example carefully

Now take both spaces to be ell two. Let A multiply coordinate N by N plus two, and let B multiply it by negative N. Their domains are the corresponding weighted square-summability spaces. Both operators are self-adjoint and unbounded.

Let C be the identity. We want a bounded map X satisfying A X minus X B equals the identity.

Pretend momentarily that the coordinates can be solved separately. On coordinate N, the equation becomes N plus two times the unknown multiplier, minus that multiplier times negative N, equals one.

Collect the terms. Two N plus two times the multiplier equals one. So the multiplier should be one divided by two N plus two.

This is promising. The largest such multiplier is one fourth, at N equal to one. Therefore X is bounded on ell two.

But boundedness is only the first check. We must also show that applying A after X is legal.

On coordinate N, applying A after X multiplies by N plus two divided by two N plus two. That ratio is never greater than one. Consequently A X y belongs to ell two for every y in ell two, not merely for y in the domain of B.

So X maps the domain of B into the domain of A, and even maps the whole input space into that domain.

Now calculate the actual difference. A X contributes N plus two divided by two N plus two. X B contributes negative N divided by the same denominator. Subtracting them gives one on every coordinate.

We have verified both the domain condition and the equation. Notice that the spectrum of A begins at three, while the spectrum of B ends at negative one. Their ordered gap is four. The norm of C is one, and the norm of X is one fourth. So the reciprocal-gap estimate is attained exactly in this example.

## How the equation appears in subspace perturbation theory

Why is a Sylvester equation relevant to angles between invariant subspaces?

Suppose A is a self-adjoint operator on one Hilbert space H. Add a bounded self-adjoint perturbation V, creating a second self-adjoint operator, A plus V. Because V is bounded, the new operator has the same domain as A.

Select a spectral subspace of A and call its orthogonal projection P. Select a spectral subspace of the perturbed operator and call its projection Q.

We want to know how far vectors in the new selected subspace can point away from the old one.

A natural map measures exactly that. Start with a vector in the range of Q, and discard its component in the range of P. The remaining component is obtained by applying identity minus P. Call this cross map X.

Its input space is Q H. Its output space is the orthogonal complement of P H. Its norm measures the largest directed sine of an angle from the Q subspace toward the P subspace.

Now there are two operators to put into a Sylvester equation. On the output side, restrict A to the complement of P H. On the input side, restrict A plus V to Q H.

These restrictions are self-adjoint on their reduced domains because P and Q are spectral projections. In particular, their projections preserve the relevant unbounded-operator domains.

Take a vector y in the domain of the perturbed restriction on Q H. Since V is bounded, y is also in the domain of A. And because identity minus P preserves that domain, X y belongs to the domain of A restricted to the complementary subspace.

That establishes the legal mapping condition.

Now compare the two terms. The restricted A applied to X y equals the complementary projection applied to A y. The other term, X applied to the perturbed restriction, equals the complementary projection applied to A y plus V y.

Subtract. The A terms cancel. What remains is the negative complementary projection of V y.

So our cross map solves a domain-aware Sylvester equation. Its forcing term is a compression of the perturbation V, with norm at most the norm of V.

This is the bridge: estimate a Sylvester solution, and we estimate a directed subspace angle.

## Why cutoffs are useful and also dangerous

Suppose we already know how to estimate bounded Sylvester equations, but the restricted operators A and B are unbounded. We might try to cut off their large spectral values, use the bounded theorem, and then remove the cutoff.

There is a safe way to do this. Choose spectral projections that retain larger and larger bounded spectral bands of A and B. Call them the A cutoff and the B cutoff.

Rather than leave X unchanged, sandwich it between those cutoffs. Apply the B cutoff first, then X, then the A cutoff. This gives a bounded compressed map X sub R.

The reason for cutting both sides is simple: X need not commute with either cutoff. If we changed A and B but kept all of X, the original Sylvester identity would generally not survive.

For the sandwiched map, the cutoff projections commute with their own operators. On the retained bands, the original equation therefore gives a bounded Sylvester equation whose right side is C sandwiched by the same two cutoffs.

At each fixed cutoff scale, that equation is legal for every vector. We may use a bounded-operator estimate.

But there is a second danger: a cutoff can destroy the spectral separation that made the estimate possible.

Return to the diagonal example. A has spectral values three, four, five, and onward. B has spectral values negative one, negative two, negative three, and onward. There is a gap of four between the two spectra.

If we truncate both operators by replacing the discarded coordinates with zero, both truncated spectra acquire zero. The artificial zero values eliminate the ordered gap, even though the original operators had one.

A filled truncation avoids this. On the discarded part of A, use a constant that stays on the high side of the gap. On the discarded part of B, use a constant that stays on the low side. The retained bands still agree with the original operators, and the new bounded operators preserve the necessary spectral order.

## Remove the cutoff without losing the estimate

Suppose the bounded estimates give the same norm bound for every cutoff scale. The cutoff projections approach the identity strongly as the retained bands expand.

For each fixed vector y, the sandwiched X sub R applied to y approaches X y. This follows from strong convergence of the two cutoffs and boundedness of X.

Now apply the uniform estimate to that fixed vector and pass to the limit. The estimate survives. Finally take the supremum over unit vectors to obtain the operator-norm bound for X.

We did not require X sub R to converge to X in operator norm. Strong convergence together with a uniform bound was enough.

And if we want to pass an operator identity through the limit, there is extra work: we must track the legal domains and the images under the unbounded operators. Closedness then identifies the limiting operator value.

The guiding order is important. Establish domain membership, derive a legal Sylvester identity, preserve the spectral gap during approximation, and only then pass a uniform estimate to the unbounded problem.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For self-adjoint partial maps \(A:D(A)\subset E\to E\) and \(B:D(B)\subset F\to F\), a bounded \(X:F\to E\) solves the domain-aware Sylvester equation with bounded \(C\) when \(X D(B)\subset D(A)\) and \(AXy-XBy=Cy\) for all \(y\in D(B)\). If \(\widetilde A=A+V\), with bounded self-adjoint \(V\), and \(P=E_A(I)\), \(Q=E_{\widetilde A}(J)\), then on their reduced domains

\[
A_{P^\perp}X-X\widetilde A_Q=-(I-P)V|_{QH},\qquad X=(I-P)|_{QH}.
\]

The proof uses both reducing-domain identities and \(D(A+V)=D(A)\). For cutoffs \(P_R,Q_R\), one studies \(X_R=P_RXQ_R\), not unmodified \(X\), and keeps the gap hypotheses on the bounded truncations. Strong limits of uniformly bounded maps give norm inequalities without requiring operator-norm convergence.

### Actual source declarations

`DavisKahan/Sylvester/ClosedSylvesterEquation.lean` — `equation_of_mem`:

```lean
theorem equation_of_mem
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (h : _root_.LinearPMap.SylvesterEquation A B X C)
    (x : B.domain) (hx : X (x : F) ∈ A.domain) :
    A ⟨X (x : F), hx⟩ - X (B x) = C (x : F) := by
```

`DavisKahan/Sylvester/CutoffInterface.lean` — `SpectralCutoffInterface`:

```lean
structure SpectralCutoffInterface
    (A : E →ₗ.[𝕜] E) (hA : IsSelfAdjoint A) where
  cutoff : ℝ → E →L[𝕜] E
  isOrthogonalProjection : ∀ τ,
    cutoff τ ∘L cutoff τ = cutoff τ ∧ (cutoff τ).IsSymmetric
  range_le_domain : ∀ τ, LinearMap.range (cutoff τ).toLinearMap ≤ A.domain
  commutes_on_domain : ∀ τ (x : A.domain),
    ∃ hx : cutoff τ (x : E) ∈ A.domain,
      A ⟨cutoff τ (x : E), hx⟩ = cutoff τ (A x)
  tendsto_identity : ∀ x,
    Tendsto (fun τ : ℝ => cutoff τ x) atTop (𝓝 x)
```

`DavisKahan/Sylvester/FilledTruncation.lean` — `filledTruncation_eq_on_cutoff`:

```lean
theorem filledTruncation_eq_on_cutoff
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H →ₗ.[𝕜] H)
    (hA : IsSelfAdjoint A)
    (Pcut : SpectralCutoffInterface A hA)
    (Tcut : BoundedTruncationInterface A hA Pcut)
    (a τ : ℝ) (x : H) :
    ∃ hx : Pcut.cutoff τ x ∈ A.domain,
      filledTruncation A hA Pcut Tcut a τ (Pcut.cutoff τ x) =
        A ⟨Pcut.cutoff τ x, hx⟩ := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `reducesSubspace_specRange`:

```lean
theorem reducesSubspace_specRange : _root_.LinearPMap.IsReducing A (specRange hA B hB) := by
```


**Type and hypothesis map.** `X C : F →L[𝕜] E` are everywhere-defined bounded maps, but `A` and `B` are partial maps. The `LinearPMap.SylvesterEquation` hypothesis carries the domain mapping condition, which `equation_of_mem` uses together with the supplied witness `hx`. `SpectralCutoffInterface` separately records projection, range-in-domain, commutation-on-domain and strong convergence. `filledTruncation_eq_on_cutoff` gives a bounded operator that agrees with `A` where its domain has already been justified. `reducesSubspace_specRange` supplies the reducing conditions for a spectral range.

**Scope:** The domain-aware equation is represented by `LinearPMap.SylvesterEquation`, with its domain-mapping requirement, while the cutoff and truncation interfaces state the precise approximation obligations. The cross-block identity is derived in the narration from reducing spectral restrictions and a bounded perturbation; no claim is made that one quoted declaration alone is the entire perturbation theorem. All excerpts are from the supplied repository snapshot.
