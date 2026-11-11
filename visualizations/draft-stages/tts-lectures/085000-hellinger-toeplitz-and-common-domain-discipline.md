# 085000 — Hellinger–Toeplitz and common-domain discipline

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `083000` closed graphs, `084000` adjoint domains. **Next:** `086000` resolvents and coercivity.

<!-- BEGIN SPOKEN LECTURE -->

# Why an everywhere-defined symmetric operator cannot be unbounded

Take a diagonal matrix whose entries are one, two, three, and so on. If that list were finite, the matrix would be bounded. In an infinite sequence space, the same pattern gives an unbounded operator, because the multiplication factors grow without limit.

But there is a restriction hidden in that example. The infinite operator cannot act on every square-summable sequence. Some input sequences would produce outputs that are not square summable.

Is that merely a defect of our diagonal formula, or is it unavoidable? The Hellinger-Toeplitz theorem answers this question decisively. Every linear operator defined on an entire Hilbert space and symmetric with respect to its inner product must be bounded.

Let's understand why, and then see how the theorem guides calculations involving sums and perturbations of unbounded operators.

## The theorem has two separate hypotheses

Let T be a linear operator from a Hilbert space into itself. Assume first that its domain is the whole Hilbert space. Every vector is allowed as an input.

Assume second that T is symmetric. That means we can move T from one position to the other in an inner product: the inner product of T x with y equals the inner product of x with T y, for every pair of vectors.

The conclusion is a uniform bound. There must be a finite constant C such that the length of T x is at most C times the length of x, for every x.

This does not claim that every symmetric operator is bounded. An unbounded symmetric operator can exist, but it must have a proper domain. And the theorem does not say that every everywhere-defined linear operator is bounded. In infinite dimensions there are everywhere-defined discontinuous linear maps. The symmetry assumption is doing real work.

So why does symmetry, together with the full domain, force continuity?

## Prove that the graph is closed

Imagine we have a sequence of inputs approaching a vector x. We apply T to each input and suppose the outputs approach a vector y. We want to prove that y equals T x.

To compare those two vectors, select an arbitrary test vector z. If two Hilbert-space vectors have the same inner product with every test vector, they must be equal.

Start with the inner product of y with z. Since the outputs approach y, this equals the limit of the inner products of T x N with z.

Use symmetry to move T onto the fixed test vector z. We get the limit of the inner products of x N with T z.

Now T z is a fixed, legitimate vector. It is legitimate precisely because T acts on every vector in the Hilbert space. Since x N approaches x, the limit equals the inner product of x with T z.

Apply symmetry one more time. This equals the inner product of T x with z.

Thus y and T x have the same inner product with every z, so y equals T x. We have proved that the graph of T is closed.

Notice the two uses of the full-domain hypothesis. T z exists for every test vector, and T x exists for the limiting input. If T were defined only on a dense subspace, we could not assume either fact without checking the domain.

## Why a closed graph gives a bound

A closed graph is enough for a boundedness conclusion when the operator is defined on all of a Banach space. That is the closed graph theorem.

Its mechanism is worth a short look. Put all pairs consisting of x and T x into a product space. Because the graph is closed, it is itself complete under the product norm.

Project each graph pair onto its first component. That projection is a continuous linear map from the complete graph space to the original Hilbert space. And because T is everywhere defined, the projection is bijective: every input appears in exactly one graph pair.

The bounded inverse theorem says that a continuous linear bijection between Banach spaces has a continuous inverse. The inverse projection takes x back to the pair consisting of x and T x.

Continuity of that inverse provides a constant controlling the combined lengths of x and T x by the length of x. In particular, it controls the length of T x. That is exactly the bound we wanted.

The Hellinger-Toeplitz proof is now complete. Symmetry and full domain give a closed graph. Full domain and completeness turn that closed graph into boundedness.

## Test the theorem against a concrete operator

Return to ell two, the space of square-summable sequences. Let A multiply coordinate N by N. Its legal domain consists of those sequences for which the weighted coordinate sequence is still square summable.

The vector supported at coordinate N has length one, while its image has length N. So A is unbounded.

On its domain, A is self-adjoint and therefore symmetric. It is also closed. But it does not violate Hellinger-Toeplitz, because its domain is not all of ell two.

The sequence whose N-th entry is one over N belongs to ell two, but applying the coordinate formula would yield the constant sequence of ones. That output is not in ell two, so the vector must be excluded from the domain.

There is another way to see the limit issue. The finite truncations of that reciprocal sequence are legal inputs approaching a vector outside the domain. Their outputs have lengths equal to the square root of the truncation length and do not converge. This is compatible with A having a closed graph.

If we equip the domain with the graph norm, then A is bounded as a map from that graph-norm space into ell two. The input norm has changed, however. We have not made A bounded with respect to the ordinary ell-two norm.

## Add a bounded perturbation without changing the domain

Suppose now that A is an unbounded self-adjoint operator with domain D. Let V be a bounded self-adjoint operator defined on the whole Hilbert space.

We can form a new operator B by applying A and V to the same input and adding the outputs. Which inputs are allowed? Exactly those in D. A cannot be applied outside D, while V introduces no additional restriction. Thus B and A have the same domain.

More surprisingly, B is self-adjoint even when V is not small.

We can see the domain argument directly. To decide whether y belongs to the adjoint domain of B, examine the measurement obtained by taking the inner product of B x with y, with x ranging over D.

Split it into two measurements, one from A and one from V. The V part is already bounded in the ordinary input norm, since V is a bounded operator. Subtracting a bounded functional cannot change whether the remaining A functional is bounded.

Therefore the adjoint domains of A and B are the same. Their adjoint actions differ by V star. Since A and V are self-adjoint, this says B has the same adjoint domain and the same action as B star. Hence B is self-adjoint on D.

The key facts are boundedness of V, self-adjointness of V, and self-adjointness of A. There is no perturbation-size condition in this theorem.

## Compare the graph norms

The graph norm of A measures both the size of x and the size of A x. The graph norm of B measures the size of x and the size of A x plus V x.

Because V is bounded, the length of V x is at most the operator norm of V times the length of x. So the length of B x is controlled by the length of A x plus a fixed multiple of the length of x.

That gives a bound for the graph norm of B in terms of the graph norm of A. Reversing the identity, A x equals B x minus V x, gives the opposite bound.

The two graph norms are equivalent on the common domain. A sequence converges in the graph norm of A exactly when it converges in the graph norm of B.

This is why bounded perturbations are friendly to domain arguments: the new operator uses the same allowable inputs and the same kind of convergence.

## What changes when the perturbation is unbounded

Suppose V is itself unbounded. Then the expression A x plus V x makes sense only for inputs that belong to both domains. That intersection may be too small or may behave poorly under limits. Neither self-adjointness of A nor self-adjointness of V, by itself, guarantees that their sum is self-adjoint.

One way to regain control is to assume that V is relatively bounded with respect to A. That means the length of V x is bounded by a fixed multiple of the length of x plus another fixed multiple of the length of A x, for every x in the domain of A.

This is a graph-norm estimate. With suitable extra assumptions, including symmetry of V and a relative coefficient strictly below one, the Kato-Rellich theorem gives self-adjointness of the sum. The coefficient restriction is relevant here; it was not needed when V was bounded on the whole space.

So the correct habit for working with unbounded operators is to name the domain before adding operators, taking adjoints, or rearranging an equation. Hellinger-Toeplitz tells us why proper domains are unavoidable. The bounded-perturbation argument shows how a domain can stay intact. Relative bounds are one way to proceed when even the perturbation is unbounded.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Hellinger–Toeplitz: an everywhere-defined symmetric linear operator on a Hilbert space has closed graph, and is therefore bounded by the closed graph theorem. A bounded self-adjoint \(V:H\to H\) added to a self-adjoint \(A:D(A)\to H\) satisfies \(D(A+V)=D(A)\), \((A+V)^*=A^*+V^*\), and is self-adjoint on that domain. For a domain-defined perturbation one may instead assume \(\|Vx\|\le a\|x\|+b\|Ax\|\), a graph-norm relative bound.

### Relative-boundedness threshold

The Kato--Rellich theorem applies when \(A\) is self-adjoint, \(V\) is
symmetric on \(D(A)\), and for constants \(a\ge0\), \(0\le b<1\),
\[\|Vx\|\le a\|x\|+b\|Ax\|\qquad(x\in D(A)).\]
Then \(A+V\) is self-adjoint on \(D(A)\). In the bounded self-adjoint
perturbation case, take \(b=0\); no smallness restriction is imposed on
\(\|V\|\).

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
