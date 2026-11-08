# 083000 — Densely defined operators and their graphs

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `010000` Hilbert spaces, `082000` spectral cutoffs. **Next:** `084000` adjoints of unbounded operators.

<!-- BEGIN SPOKEN LECTURE -->

# An operator includes the question of where it is defined

A matrix acts on every vector in its finite-dimensional coordinate space. But in infinite-dimensional Hilbert space, some of the most important operators cannot act on every vector. Their domain is part of the mathematical data.

The graph of an operator records its input-output pairs. Closedness and the graph norm let us pass to limits while respecting the operator's domain.

## A diagonal operator that grows without bound

Take the Hilbert space ell two: the sequences of complex numbers whose squared magnitudes have finite sum. The length of a sequence is the square root of that sum.

Define A by multiplying the first coordinate by one, the second by two, the third by three, and the N-th by N. Formally, the output coordinates are N times the input coordinates.

It would be tempting to write that formula for every square-summable sequence. That is incorrect. Consider the sequence whose N-th entry is one divided by N. Its squares form a convergent series, so the sequence belongs to ell two. But multiplying by N produces the constant sequence of ones, which does not belong to ell two.

The domain of A must therefore consist of those sequences for which the sum of N squared times the squared magnitude of the N-th coordinate is finite. The operator is a linear map from that domain into ell two.

Every sequence having only finitely many nonzero coordinates belongs to the domain. Those finite sequences are dense in ell two, because their initial truncations converge to any square-summable sequence. We say that A is densely defined.

A is nevertheless unbounded. Let e N be the sequence with one in position N and zero elsewhere. Its length is one, while the length of A e N equals N. There is no single constant that bounds the output length by a constant times the input length on the whole domain.

Notice the precise conclusion: A is unbounded as an operator on its domain. Each individual A x is still a perfectly good vector of finite length. Unboundedness does not mean that an individual operator value has infinite norm.

## The graph records both input and output

For any operator A with domain D, form its graph: the set of ordered pairs, x together with A x, for x in D. This is a linear subspace of the product Hilbert space H times H.

The product norm of a graph pair is the square root of the squared length of x plus the squared length of A x. We call that the graph norm of x.

An operator is closed when its graph is a closed subset of this product space. Equivalently, take a sequence of domain vectors x N that converges to x in H, and suppose A x N converges to y in H. Closedness says that x actually belongs to the domain and A x equals y.

That is exactly the limit passage needed for unbounded operators. We cannot infer that A x exists merely because x N converges. But when both input and output converge, closedness makes the limiting pair legal.

Let's prove our diagonal operator is closed. Suppose x N approaches x and A x N approaches y in ell two. Taking the K-th coordinate is continuous: the absolute value of that coordinate never exceeds the length of the entire sequence. Therefore the K-th coordinates converge. For every N, the K-th coordinate of A x N is K times that of x N. Pass to the limit. The K-th coordinate of y is K times that of x. This holds for every K. Because y belongs to ell two, the weighted sequence formed from x is square summable. Thus x is in the domain, and A x equals y. The graph is closed.

The proof used neither a matrix inverse nor a uniform bound on A. Coordinatewise convergence was enough because the output limit itself supplied the required summability.

## Complete in the right norm

The graph norm provides another characterization of closedness. Give the domain D the graph norm, even when D is not closed in the ordinary Hilbert-space norm.

Suppose A is closed and x N is a Cauchy sequence in graph norm. The definition says both x N and A x N are Cauchy in H. Since H is complete, they have limits x and y. Closedness puts x in the domain and identifies y with A x. Both pieces converge, so x N converges in graph norm. The domain is complete in its graph norm.

Conversely, suppose the domain is complete in graph norm. If x N approaches x and A x N approaches y in H, then the pairs are Cauchy, so x N is graph-norm Cauchy. Completeness gives a domain vector v as its graph-norm limit. Ordinary convergence forces v to equal x, and output convergence forces A v to equal y. Hence the graph is closed.

We have proved: on a Hilbert space, a linear operator is closed exactly when its domain, equipped with the graph norm, is complete.

There is a subtle but important point here. The domain of our diagonal A is dense and proper. It is not complete in the ordinary ell-two norm: finite truncations of the sequence one over N converge in ell two to a vector outside the domain. Yet it is complete in the graph norm.

## Dense does not imply closed

Take the zero operator but define it only on finite-support sequences. The formula is as harmless as possible: every allowed input maps to zero. Its domain is dense. Its graph is not closed, though.

Take finite truncations of the sequence one over N. They converge in ell two to a sequence not having finite support. Their zero outputs converge to zero. The limiting pair does not belong to the graph. So this densely defined zero operator is not closed.

Its closure is the zero operator on all of ell two. The word closure here means the operator whose graph is the closure of the original graph, provided that closed set is still the graph of a function.

Not every densely defined operator is closable. The closure of a graph may contain a pair with zero input and nonzero output, which would violate single-valuedness. To check closability, one useful criterion is this: whenever x N approaches zero and A x N approaches y, we must have y equal to zero. If that condition fails, no extension of A can have a closed graph.

A densely defined operator with a densely defined adjoint is closable: the closure of its graph remains the graph of a single-valued operator. Self-adjoint operators are closed, so their spectral and resolvent identities can be passed through graph limits on their specified domains.

## Why spectral cutoffs fit this framework

Recall the spectral projections defined by a bounded spectral cutoff. For a self-adjoint operator A, let P R select the spectral interval from negative R to positive R. Every vector P R x lies in the domain of A, even when x itself does not.

If x belongs to the domain, P R x converges to x, and A P R x equals P R A x, which converges to A x. Thus the cutoffs converge in the graph norm. They are legal approximations in both input and output, rather than approximations that control only one side.

For an unbounded block identity, first state the domain, establish that each expression is defined, and only then pass to limits using closedness or graph-norm convergence.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:D(A)\subseteq H\to H\). Its graph is \(G(A)=\{(x,Ax):x\in D(A)\}\). The graph norm is \(\|x\|_A=(\|x\|^2+\|Ax\|^2)^{1/2}\). In a Hilbert space, \(A\) is closed if and only if \((D(A),\|\cdot\|_A)\) is complete. For \(A:\ell^2\supset D(A)\to\ell^2\) with \((Ax)_n=nx_n\), \(D(A)=\{x:\sum n^2|x_n|^2<\infty\}\). The map is densely defined, unbounded, and closed. Conversely, zero on \(c_{00}\) is densely defined but not closed.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `isClosed_iff_range_isClosed`:

```lean
theorem isClosed_iff_range_isClosed
    (f : E →ₗ.[𝕜] F) :
    f.IsClosed ↔ IsClosed (Set.range fun x : f.domain => ((x : E), f x)) := by
```

Its graph-based closedness predicate coincides with the closed-range formulation used in domain restrictions.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `graphNorm`:

```lean
noncomputable def graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2)
```

The graph norm is defined directly on the subtype `A.domain`, not on all of the ambient space.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `graphNorm_sq`:

```lean
theorem graphNorm_sq (A : E →ₗ.[𝕜] E) (x : A.domain) :
    graphNorm A x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
```

The source makes the sum-of-squares identity exact.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `norm_apply_le_graphNorm`:

```lean
theorem norm_apply_le_graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) :
    ‖A x‖ ≤ graphNorm A x := by
```

A graph-norm estimate controls the operator output for vectors in the domain.

**Scope:** The equivalence with graph-norm completeness is derived in the narration; the quoted Lean lemmas formalize its graph and norm components, not an asserted single Lean equivalence theorem. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
