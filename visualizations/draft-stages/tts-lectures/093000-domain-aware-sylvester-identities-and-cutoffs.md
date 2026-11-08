# 093000 — Domain-aware Sylvester identities and cutoffs

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `071000` compressed Sylvester identities, `089000` reducing domains, `091000` bounded truncations, `092000` unitary groups. **Next:** `094000` unbounded Sylvester estimates.

<!-- BEGIN SPOKEN LECTURE -->

# Prove the block identity before estimating its solution

In finite-dimensional perturbation theory we regularly write A X minus X B equals C. Every expression makes sense because all the matrices act on every vector.

For unbounded operators this is no longer automatic. A and B have domains, and even a bounded map X may carry a legal input for B outside the domain of A. Today we will construct the domain-aware Sylvester equation, derive the compressed identity behind sine-theta estimates, and explain what spectral cutoffs can and cannot justify.

## The typed Sylvester equation

Let B be a densely defined self-adjoint operator on a Hilbert space F. Let A be a densely defined self-adjoint operator on another Hilbert space E.

Let X and C be bounded maps from F into E. We would like the equation A X minus X B equals C to hold.

For an input y in D of B, the value B y is defined, and the bounded map X can act on B y. The term X B y therefore makes sense.

The first term, A X y, requires another condition: X y must belong to D of A. Thus the Sylvester equation has two parts. First, X maps D of B into D of A. Second, for every y in D of B, A applied to X y minus X applied to B y equals C y.

Both parts are mathematical assertions. The first is not merely a type-checking inconvenience. Without it, the equation itself has no meaning.

This is the distinction between a domain-aware equation and an identity of bounded operators. If A and B are unbounded, A X and X B are not automatically continuous maps on all of F.

## A diagonal example where the equation is legal

Take E and F both equal to ell two. Let A multiply coordinate N by N plus two, and let B multiply it by negative N. Both operators are self-adjoint on their weighted square-summability domains.

Let C be the identity. Define X to multiply coordinate N by one divided by two N plus two.

This X is bounded, since its largest diagonal multiplier occurs at N equal to one and equals one fourth.

For any y in D of B, the N-th coordinate of X y has been divided by two N plus two. Applying A afterward multiplies by N plus two. The combined multiplier is at most one, so A X y exists. In fact, X sends every vector in ell two into D of A in this example.

The N-th coordinate of A X y minus X B y is the N-th coordinate of y: the numerator is N plus two, minus negative N, divided by two N plus two. It equals one.

Therefore the Sylvester equation holds on D of B. We have verified both domain membership and the coordinate identity.

Now try X equal to the identity instead. The expression A X minus X B would formally multiply coordinate N by two N plus two. That is unbounded. There is no bounded C representing this expression on all inputs. Simply writing down the symbolic matrix difference would hide the failure.

## The cross block from two spectral projections

Now move to the situation that Davis–Kahan theory actually studies. Let A be self-adjoint on H, and let V be a bounded self-adjoint perturbation. Set the perturbed operator equal to A plus V, with exactly the same domain as A.

Let P be a spectral projection of A. Let Q be a spectral projection of A plus V, perhaps selecting a nearby cluster of spectral values.

By the reducing-domain result, the range of P and its orthogonal complement carry self-adjoint operator restrictions of A. Likewise Q H carries a self-adjoint restriction of the perturbed operator.

Define X to take a vector in Q H and project it onto the orthogonal complement of P H. In symbols spoken aloud, X is identity minus P, restricted to Q H.

The domain of the operator B on Q H consists of Q-vectors that also belong to D of A. Take such a vector y.

Since the complementary spectral projection identity minus P preserves D of A, X y belongs to the domain of the restricted A operator on the complement of P H. The first Sylvester requirement holds.

Now calculate. Because identity minus P commutes with A on D of A, the complementary A restriction applied to X y equals identity minus P applied to A y.

The second term, X B y, is identity minus P applied to A plus V acting on y. Subtract these two expressions. The A contributions cancel, leaving negative identity minus P applied to V y.

Thus the precise compressed equation is: complementary A restriction times X, minus X times perturbed restriction, equals the negative complementary projection of V, restricted to Q H.

The right side is bounded, with norm at most the norm of V. And X is the cross-projection map whose norm measures the directed sine of the subspace angles.

This is the bridge from a perturbation V to an angle estimate. The algebra looks like the finite-dimensional proof, but we reached it only after identifying the two restricted domains.

## What a spectral cutoff does

Suppose we want to estimate an unbounded operator equation using a theorem originally proved for bounded operators. Choose spectral cutoffs for A and B.

Each cutoff projects into a bounded spectral band. It preserves the corresponding operator domain and commutes with the corresponding generator there. The bounded truncation agrees with the original operator on the selected band.

The first temptation is to replace A and B by their truncations, keep X unchanged, and claim that the original Sylvester equation remains valid. That is generally wrong. X need not commute with the two cutoff projections.

A safer construction is to cut both the input and output: use a bounded map made by placing the A cutoff on the left of X and the B cutoff on the right.

On vectors lying in the B cutoff range, the original domain-aware equation and the commutation rules give a bounded block equation for the truncated operators. The corresponding right side contains the cutoffs of C.

At each fixed cutoff radius, every map in this block equation is bounded. We can now apply a bounded Sylvester theorem, provided its spectral gap hypotheses survive the truncation.

## Why filling the cutoff complement helps

An ordinary truncation acts as zero outside its retained band. If the original A spectrum lies above five, a zero complement introduces artificial spectral values below five. This can destroy an ordered spectral gap.

The filled truncation instead assigns a chosen scalar to the complement. Choosing that scalar on the correct side of the gap can maintain the necessary form inequality while the retained spectral band expands.

The existence of such a family is more useful than a single convenient formula. We need projections that converge strongly to identity, bounded truncations that converge on domain vectors, and uniform gap inequalities that survive the approximation.

A formal interface can record those exact requirements rather than silently assuming that every cutoff has them.

## Passing from bounded estimates back to unbounded ones

Suppose each cutoff equation yields a uniform bound on the cross map. The cutoffs converge strongly on fixed vectors, so we can pass the estimate to the limit for each vector. Taking the supremum over unit vectors then gives the operator-norm bound for the original X.

Notice the direction of this argument. Uniform estimates pass through strong limits, but strong convergence alone does not imply operator-norm convergence of the approximants.

For an operator identity we need more: convergence on legal domain vectors, convergence of the operator images, and closedness to identify the limit. Domain conditions must be propagated separately from norm estimates.

The following lecture uses these ingredients to prove the sharp ordered-gap Sylvester bound for unbounded self-adjoint operators, and then turns it into a cross-subspace estimate.

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
