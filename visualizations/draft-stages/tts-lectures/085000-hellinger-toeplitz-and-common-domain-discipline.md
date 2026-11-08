# 085000 — Hellinger–Toeplitz and common-domain discipline

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `083000` closed graphs, `084000` adjoint domains. **Next:** `086000` resolvents and coercivity.

<!-- BEGIN SPOKEN LECTURE -->

# Why an unbounded self-adjoint operator must have a proper domain

There is a theorem that sounds surprising when first encountered: if a linear operator is defined on every vector of a Hilbert space and is symmetric, then it must be bounded. This is the Hellinger–Toeplitz theorem.

We will prove it, explain the closed graph theorem behind it, and then use it to understand why operator sums and perturbation identities require explicit common-domain hypotheses.

## The Hellinger–Toeplitz argument

Let T act on every vector of a Hilbert space H. Assume T is symmetric, meaning that for any x and y, the inner product of T x with y equals the inner product of x with T y.

Take any sequence x N converging to x, and suppose T x N converges to some y. We want to show that y equals T x. Fix an arbitrary test vector z.

By continuity of the inner product, the inner product of y with z equals the limit of the inner products of T x N with z. Symmetry changes each of those terms into the inner product of x N with T z. Since T z is one fixed vector, we may pass to the limit again. The result is the inner product of x with T z. Apply symmetry in reverse: it equals the inner product of T x with z.

Thus y and T x have the same inner product against every z. Their difference is orthogonal to every vector, including itself. Hence y equals T x.

We have proved that the graph of T is closed. Because its domain is all of H, the closed graph theorem now says T is bounded.

That completes the proof of Hellinger–Toeplitz.

Notice exactly where we used the full domain. We needed T z to exist for every test vector z, and we needed the closed graph theorem to apply to a linear map whose domain is the entire Banach space H.

## Why the closed graph theorem is plausible

The closed graph theorem is a consequence of completeness, and it is worth understanding the mechanism rather than treating its name as an incantation.

Equip the graph of a closed operator T with the product norm. It is a closed subspace of the Banach space H times H, so it is itself complete. Projection from the graph onto its first coordinate is continuous. If T is everywhere defined, that projection is a bijection from the graph onto H.

The bounded inverse theorem says a continuous linear bijection between Banach spaces has a continuous inverse. One route to that theorem uses the Baire category theorem: a complete metric space cannot be covered by countably many closed sets with empty interior. Applied to images of balls, that fact forces a surjective bounded linear map to send some neighborhood of zero onto a set containing a neighborhood of zero. Linear scaling then gives a uniform bound for the inverse.

Now apply the inverse of the graph projection to x. It returns the pair x together with T x. Continuity of that inverse gives a constant C for which the product length of x and T x is at most C times the length of x. In particular, the length of T x is at most C times the length of x. So T is bounded.

The closed graph theorem and Hellinger–Toeplitz use completeness in a substantive way.

## Why the diagonal example has a restricted domain

Our diagonal operator sends the N-th coordinate to N times that coordinate. On the basis vector e N it multiplies length by N, so it is unbounded. On its maximal weighted-square-summability domain it is self-adjoint: testing its adjoint on individual coordinate basis vectors forces exactly the same domain condition.

Hellinger–Toeplitz tells us that this domain cannot equal all of ell two. The sequence with N-th coordinate one over N is a direct witness: it lies in ell two but not in the operator domain.

There is no contradiction with symmetry. The operator is symmetric on its domain, not everywhere defined. Its graph is closed, but the closed graph theorem does not make it bounded as a map from the ambient Hilbert space because its domain is proper.

If we equip the domain with graph norm, the operator becomes bounded as a map from that graph-norm space into H. This is a different claim, using a stronger norm on the input.

## Adding a bounded perturbation

Let A be self-adjoint with domain D, and let V be an everywhere-defined bounded self-adjoint operator. Define B by B x equals A x plus V x, for x in D. The domain of B is exactly D.

We can prove that B is self-adjoint. First observe the adjoint domain of B. A vector y lies in that domain when the functional in x given by the inner product of A x plus V x with y is bounded by a constant times the length of x, for x in D.

The contribution from V is already bounded: by the adjoint identity for bounded V, it equals the inner product of x with V y. Subtracting this term shows that the whole functional is bounded if and only if the A functional is bounded. Thus the adjoint domains of B and A agree.

For y in that common adjoint domain, B star y equals A star y plus V y. Since A is self-adjoint, and since V is self-adjoint, this is A y plus V y on D. Therefore B is self-adjoint on D.

This proof does not require V to be small in operator norm. Boundedness and self-adjointness of V are enough.

## Comparing graph norms on a common domain

The graph norm for A involves the lengths of x and A x. The graph norm for B involves x and A x plus V x.

The triangle inequality gives the length of B x at most the length of A x plus the operator norm of V times the length of x. Therefore the graph norm of B is bounded above by a constant times the graph norm of A.

Reverse the relation by writing A x equals B x minus V x. The same reasoning gives an upper bound for the graph norm of A in terms of that of B.

So the two graph norms are equivalent on the same domain. They generate the same notion of graph-norm convergence, although their numerical values need not agree.

This is why bounded perturbations are technically manageable: no new operator domain is introduced.

## What goes wrong without a common domain

For two genuinely unbounded operators, the formal sum A plus B is initially defined only on the intersection of their domains. That intersection may not have the properties one wants, and the sum need not be self-adjoint merely because each summand is self-adjoint.

Even identities like A x minus B x require x to belong to both domains. Writing A minus B as though it were automatically bounded on all of H can hide precisely the issue that an unbounded perturbation theorem must solve.

Later we will use estimates involving a perturbation small relative to A, which means controlling the length of V x by a multiple of the length of A x plus a multiple of the length of x. This is a bound in the graph norm. It lets us reason about a perturbation that need not be bounded in the ambient norm, provided it acts on the required domain.

For Davis–Kahan's unbounded theorems, the common-domain assumption is often the hinge between a valid operator equation and an expression that is not even defined. We will state it before manipulating off-diagonal blocks.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Hellinger–Toeplitz: an everywhere-defined symmetric linear operator on a Hilbert space has closed graph, and is therefore bounded by the closed graph theorem. A bounded self-adjoint \(V:H\to H\) added to a self-adjoint \(A:D(A)\to H\) satisfies \(D(A+V)=D(A)\), \((A+V)^*=A^*+V^*\), and is self-adjoint on that domain. For a domain-defined perturbation one may instead assume \(\|Vx\|\le a\|x\|+b\|Ax\|\), a graph-norm relative bound.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `SameDomain`:

```lean
def SameDomain (A B : E →ₗ.[𝕜] E) : Prop :=
  A.domain = B.domain
```

Equality of operator domains is a named condition, not inferred from matching formulas.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `addBounded_domain`:

```lean
@[simp] theorem addBounded_domain (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    (TauCeti.LinearPMap.addBounded A V).domain = A.domain := (rfl)
```

The bounded perturbation has exactly the domain of the unperturbed partial map.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `RelativelyBounded`:

```lean
def RelativelyBounded (A : E →ₗ.[𝕜] E)
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖
```

A relative bound quantifies control by the input norm and the unperturbed output norm.

**Scope:** The narrated Hellinger–Toeplitz proof and the complete abstract self-adjoint bounded-perturbation argument are mathematical teaching material, not claimed as the exact statements of these three Lean declarations. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
