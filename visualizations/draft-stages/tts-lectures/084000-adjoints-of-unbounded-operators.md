# 084000 — Adjoints of unbounded operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `012000` adjoints and Riesz representation, `083000` graph norms. **Next:** `085000` Hellinger–Toeplitz.

<!-- BEGIN SPOKEN LECTURE -->

# Finding an adjoint when the domain is restricted

For a matrix, the adjoint is the conjugate transpose. In infinite dimensions, that formula leaves out a central question: which vectors belong to the adjoint's domain?

We will derive that domain from first principles, test it on the diagonal operator, and distinguish a symmetric operator from a genuinely self-adjoint one.

## Start with the inner-product identity

Let A be a densely defined linear operator on a complex Hilbert space H, with domain D. For simplicity, say that the inner product is linear in its first argument.

Fix a candidate vector y. We would like to find a vector z such that the inner product of A x with y equals the inner product of x with z, for every x in D. This is the familiar adjoint identity.

But why should such a z exist? Define a linear functional on D by taking the inner product of A x with y. The functional is defined on D; it need not be bounded with respect to the ordinary Hilbert norm of x.

We place y in the domain of A star exactly when there exists a constant C, depending on y, such that the absolute value of that functional is at most C times the length of x, for every x in D.

Because D is dense, such a bounded functional extends uniquely to all of H. The Riesz representation theorem then supplies a unique vector z. We define A star y to be z.

This construction reveals why density matters. If D were not dense, two different representatives z could have exactly the same inner products against all of D: their difference could lie in the orthogonal complement of D. A densely defined operator has an unambiguous adjoint when the boundedness condition holds.

The domain of A star consists of all y passing that boundedness test. It may be a proper subset of H, and it need not agree with D.

## A complete diagonal calculation

Return to ell two. Let A multiply coordinate N by N, but initially define it only on finite-support sequences. Call this operator A minimal.

We can test every proposed adjoint vector y using the finite-support basis vectors. Suppose y is in the adjoint domain, with adjoint output z. Insert x equals e N into the defining identity. On the left we obtain N times the conjugate of the N-th coordinate of y. On the right we obtain the conjugate of the N-th coordinate of z. Therefore z N must equal N y N.

Because z belongs to ell two, the sequence of N times y N must be square summable. This proves a necessary condition.

It is also sufficient. If that weighted sequence is square summable, define z from it. For any finite-support x, the inner-product identity follows by summing the finitely many coordinates. The Cauchy–Schwarz inequality bounds its magnitude by the length of z times the length of x. Therefore y belongs to the adjoint domain.

So the adjoint of A minimal is the maximal diagonal operator: its domain contains every sequence whose weighted coordinates are square summable, not merely finite-support sequences.

That is a concrete example where a symmetric operator is not self-adjoint.

## Symmetric means equality on the original domain

An operator is symmetric if, for all x and y in its domain, the inner product of A x with y equals the inner product of x with A y.

For a densely defined symmetric operator, every y in its domain passes the adjoint boundedness test: the functional in x equals the inner product of x with A y, and its size is bounded by the length of A y times the length of x. Thus the original domain sits inside the adjoint domain, and A star agrees with A on the original domain.

This is an inclusion, not necessarily an equality. For A minimal, the inclusion is strict. Symmetry alone leaves open the possibility that there are extra vectors on which the adjoint acts.

An operator is self-adjoint when A equals A star as an operator: the two domains are equal and the actions agree on that common domain.

The maximal diagonal operator is self-adjoint. To check this, suppose y lies in its adjoint domain. Test again on e N to deduce that the adjoint output must have coordinates N y N. Those coordinates are square summable, forcing y into the maximal domain. Conversely, a maximal-domain vector satisfies the inner-product identity against every domain vector by Cauchy–Schwarz. Hence both domains and actions agree.

Notice the relationship among the three operators. The finite-support diagonal operator is symmetric but not closed. Its adjoint is the maximal self-adjoint diagonal operator. Its closure is that same maximal operator, because finite truncations approximate every maximal-domain vector in graph norm.

This example is especially instructive, but not every symmetric operator is essentially self-adjoint. For other operators, closing the graph may still leave a domain smaller than the adjoint domain.

## Boundary conditions can change the answer

Consider the differential expression negative i times the derivative on square-integrable functions on an interval. To make sense of the derivative, the domain must consist of sufficiently regular functions.

For smooth functions with compact support strictly inside the interval, integration by parts moves the derivative from one function to the other with no boundary contribution. This gives symmetry.

Now allow functions whose endpoint values are nonzero. The integration-by-parts identity acquires a boundary term. Different choices of domain can make that term vanish: for example, periodic boundary conditions identify the two endpoint values. The expression stays the same, but the operator defined by the expression changes with the domain.

The adjoint domain detects exactly which boundary conditions are missing. This is why a self-adjoint differential operator cannot be specified by writing only a derivative formula.

In particular, integration by parts on a small test-function domain proves symmetry there; it does not, by itself, prove that the chosen domain equals the full adjoint domain.

## Closedness and the double adjoint

The adjoint of a densely defined operator is closed. Here is the reason. Let y N approach y and let A star y N approach z. For any x in the original domain, the adjoint identity gives an equality of inner products. Pass to the limit, using ordinary continuity of inner products. We obtain the identity defining membership of y in the adjoint domain, with adjoint output z. Therefore the adjoint graph is closed.

If A star is itself densely defined, A is closable. In that situation, the double adjoint A star star equals the closure of A. For our finite-support diagonal example, taking two adjoints recovers the maximal diagonal operator.

For unbounded operators, both adjoint identities require domain conditions, and these conditions affect the conclusions.

## A practical domain test

There is a useful procedure to remember. First write down the candidate expression for the adjoint using integration by parts or coordinate calculations. Second determine the largest collection of output vectors for which the resulting inner-product functional is bounded in the ordinary ambient norm. Third compare that collection with the original domain.

If the domains are different, the original operator cannot be self-adjoint, even if every formal inner-product manipulation looks symmetric. If the domains match, the same calculation proves self-adjointness. The domain comparison is the decisive step, not the appearance of the formula.

## The relationship with spectral theory

A self-adjoint operator has a full spectral theory, real spectrum, and nonreal resolvents. A merely symmetric operator might lack these properties because it can have too small a domain.

The same domain test applies when an unbounded operator is restricted to a reducing spectral subspace. A formal restriction of the differential expression does not suffice; the restricted domain and its adjoint domain must be identified. This is where the distinctions we established today enter directly into the Davis–Kahan proofs.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For dense \(D(A)\), \(y\in D(A^*)\) iff \(x\mapsto\langle Ax,y\rangle\) is bounded on \(D(A)\) in the ambient \(H\)-norm. Then Riesz representation gives the unique \(A^*y\) satisfying \(\langle Ax,y\rangle=\langle x,A^*y\rangle\). Symmetry means \(A\subseteq A^*\); self-adjointness means equality of domains and actions. For the diagonal map restricted to \(c_{00}\), the adjoint has maximal domain \(\{y:\sum n^2|y_n|^2<\infty\}\), which strictly contains \(c_{00}\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `IsSymmetric`:

```lean
def IsSymmetric (A : E →ₗ.[𝕜] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫_𝕜 = ⟪(x : E), A y⟫_𝕜
```

A partial linear map is symmetric only on `A.domain`.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `isSymmetric_of_isSelfAdjoint`:

```lean
theorem isSymmetric_of_isSelfAdjoint [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : _root_.IsSelfAdjoint A) : IsSymmetric A := by
```

Self-adjointness implies that symmetry identity; the converse is not claimed.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `mem_reducingRestriction_adjoint_domain_iff`:

```lean
theorem mem_reducingRestriction_adjoint_domain_iff
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [CompleteSpace E] [CompleteSpace U]
    (hred : _root_.LinearPMap.IsReducing A U) (y : U) :
    y ∈ (reducingRestriction A U hred).adjoint.domain ↔
      (y : E) ∈ A.adjoint.domain := by
```

The adjoint-domain membership of a reducing restriction is checked explicitly, with its reducing-subspace hypotheses.

**Scope:** The general adjoint-domain characterization and diagonal calculation are mathematical arguments in the spoken lecture; the displayed source anchors symmetry and the domain-aware restriction operation. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
