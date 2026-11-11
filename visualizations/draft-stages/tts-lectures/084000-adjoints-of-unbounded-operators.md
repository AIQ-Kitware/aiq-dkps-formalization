# 084000 — Adjoints of unbounded operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `012000` adjoints and Riesz representation, `083000` graph norms. **Next:** `085000` Hellinger–Toeplitz.

<!-- BEGIN SPOKEN LECTURE -->

# An adjoint is an equation and a domain

For a finite matrix, the adjoint is the conjugate transpose. You can calculate it from the entries, and the result acts on every vector of the appropriate size.

In an infinite-dimensional Hilbert space, the same inner-product equation defines the adjoint, but there is an extra question: which vectors are permitted as inputs to the adjoint?

We will answer that question with one diagonal operator, then see how the same issue appears in differential operators and boundary conditions. The crucial distinction will be between a symmetric operator and a self-adjoint one.

## What the adjoint equation asks for

Begin with a linear operator A acting on a dense subspace of a Hilbert space. Its domain may be smaller than the whole space. We use a complex inner product, taken to be linear in its first input.

Fix a vector y in the Hilbert space. We want to move A from the first position of an inner product to the second. In other words, we want a vector z such that the inner product of A applied to x with y equals the inner product of x with z, for every allowed input x.

If such a z exists, the adjoint sends y to z.

But a vector z need not exist for every y. This is the domain problem.

To recognize when it does exist, hold y fixed and think of the left side as a measurement of x. It is a linear functional on the domain of A. A necessary condition is that this measurement be bounded by a constant times the ordinary length of x. That constant may depend on y, but it must work for every x in the domain.

Why must it be bounded? If the measurement equals the inner product of x with a fixed vector z, the Cauchy-Schwarz inequality makes its absolute value no greater than the length of x times the length of z.

The condition is also sufficient. A bounded linear functional on a dense subspace extends uniquely to the whole Hilbert space. The Riesz representation theorem then gives exactly one representing vector z.

So here is the definition in words. The adjoint domain consists of all vectors y for which the measurement of x given by the inner product of A x with y is bounded in the ordinary ambient norm of x. For such a y, the representing vector is A star applied to y.

Notice which norm appears in the test. We use the ordinary Hilbert-space norm of x, not the graph norm of A. If we used the graph norm, the measurement would be bounded for every y by Cauchy-Schwarz, and we would no longer recover the intended adjoint.

## Calculate an adjoint using coordinates

Let our Hilbert space be ell two, the square-summable sequences. Define A on sequences with only finitely many nonzero entries. It multiplies coordinate one by one, coordinate two by two, and coordinate N by N.

This is a legitimate densely defined operator. It is unbounded, because a unit vector supported in coordinate N is multiplied in length by N.

Now fix a candidate adjoint input y. What would the output z have to be?

Test the adjoint equation using the vector that is one in coordinate one and zero elsewhere. The left side reads off the first coordinate of y. The right side reads off the first coordinate of z. So the first coordinates must agree.

Test using the vector supported in coordinate two. A doubles that test vector. The equation therefore forces the second coordinate of z to be twice the second coordinate of y.

Continue in this way. The N-th coordinate of z must equal N times the N-th coordinate of y.

This is exactly the formula we started with. But the domain has changed.

For z to be a valid ell-two vector, the weighted coordinates N times y N must be square summable. Therefore y can belong to the adjoint domain only if it satisfies that weighted summability condition.

Conversely, if the weighted coordinates of y are square summable, let z be that weighted sequence. The adjoint equation holds for every finite-support test vector by an ordinary finite sum. Cauchy-Schwarz gives the required bound. So the condition is sufficient as well.

We have completely determined the adjoint. It multiplies coordinate N by N, but it acts on the full weighted square-summability domain, which is much larger than the finite-support domain of the original operator.

That calculation establishes something important. Two operators can have exactly the same formula on every input where both are defined, yet still be different operators because their domains differ.

## Symmetric versus self-adjoint

A densely defined operator is symmetric when the inner product of A x with y equals the inner product of x with A y whenever both x and y belong to its domain.

Our finite-support diagonal operator is symmetric. The two inner products are the same finite weighted sum. No boundary terms or hidden convergence issues arise because the inputs have finite support.

Symmetry guarantees that every original domain vector belongs to the adjoint domain, and the two actions agree there. But it does not guarantee that there are no additional adjoint-domain vectors.

Our diagonal example proves the difference. The original domain contains only finite-support sequences. The adjoint domain also contains infinitely supported sequences, provided their weighted squares sum to a finite number. So the original operator is symmetric but not self-adjoint.

An operator is self-adjoint when its domain equals its adjoint's domain and their actions agree on that common domain.

Let's now enlarge the diagonal operator to the weighted square-summability domain. Call that enlarged operator M. Is M self-adjoint?

The same coordinate tests show that any vector in the adjoint domain of M must have weighted coordinates belonging to ell two. That puts it back in the domain of M. Conversely, for two vectors in that domain, the weighted inner-product sum is absolutely convergent by Cauchy-Schwarz. So the adjoint equation holds throughout the domain.

Thus M equals its own adjoint. The maximal diagonal operator is self-adjoint.

The original finite-support operator has not suddenly become self-adjoint. It has a self-adjoint closure, and its closure is M. Finite truncations of any vector in the domain of M approximate that vector both in ordinary length and after applying M.

A symmetric operator whose closure is self-adjoint is called essentially self-adjoint. Our finite-support diagonal operator has that property. Other symmetric operators do not.

## How boundary conditions enter

For a more geometric example, take square-integrable functions on the interval from zero to one. Consider the differential expression negative i times the first derivative.

The formula alone does not specify an operator. We must say what regularity is required and what happens at the endpoints.

Start with smooth functions that vanish outside a compact subset of the open interval. Their values are zero near both endpoints. Integration by parts lets us move the derivative between the two positions of the inner product without leaving a boundary term. So this small-domain operator is symmetric.

But it is not self-adjoint on that small domain. The adjoint allows a much larger family of functions with a square-integrable weak derivative. In particular, those functions do not have to vanish at the endpoints.

Now consider a periodic domain: functions with a square-integrable weak derivative whose endpoint values agree. Integration by parts produces a boundary contribution at zero and one. The periodic condition makes the two contributions cancel. In this setting, the operator is self-adjoint.

The formula remains negative i times the derivative. Changing the domain changes the operator's adjoint and its spectral behavior.

This is why a proof that checks integration by parts on a convenient collection of test functions has established symmetry, but has not necessarily established self-adjointness. The maximal allowable adjoint domain must still be determined.

## Closedness gives another perspective

An adjoint of a densely defined operator is closed. To see the mechanism, suppose adjoint inputs y N approach y, and their adjoint outputs approach z. The defining inner-product equality holds for every y N and every x in the original domain. Pass to the limit in both inner products. The same equality now holds for y and z, so y belongs to the adjoint domain and its output is z.

If the adjoint domain is dense, the original operator is closable, and taking the adjoint twice gives its closure.

These statements explain our diagonal example: the adjoint automatically fills in the weighted square-summability domain, and the double adjoint recovers the closed maximal operator.

They also give us a dependable method for examining a proposed unbounded operator.

First specify the original domain. Next derive the candidate adjoint action from coordinate tests or integration by parts. Then determine which candidate input vectors make the adjoint functional bounded in the ambient norm. Finally compare that adjoint domain with the original one.

The defining issue is whether the domains agree. For an unbounded operator, the formula alone cannot settle self-adjointness.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For dense \(D(A)\), \(y\in D(A^*)\) iff \(x\mapsto\langle Ax,y\rangle\) is bounded on \(D(A)\) in the ambient \(H\)-norm. Then Riesz representation gives the unique \(A^*y\) satisfying \(\langle Ax,y\rangle=\langle x,A^*y\rangle\). Symmetry means \(A\subseteq A^*\); self-adjointness means equality of domains and actions. For the diagonal map restricted to \(c_{00}\), the adjoint has maximal domain \(\{y:\sum n^2|y_n|^2<\infty\}\), which strictly contains \(c_{00}\).

### Worked differential-operator domains

On \(L^2(0,1)\), the minimal momentum operator
\(T_0=-i\,d/dt\) on \(C_c^\infty(0,1)\) is symmetric. Its adjoint
has the action \(-i\,d/dt\) on \(H^1(0,1)\), which strictly contains
\(C_c^\infty(0,1)\). The periodic realization with domain
\(\{f\in H^1(0,1):f(0)=f(1)\}\) is self-adjoint. The formula
alone does not distinguish these realizations.

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
