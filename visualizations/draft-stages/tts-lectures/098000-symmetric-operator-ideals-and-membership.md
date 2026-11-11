# 098000 — Symmetric operator ideals and membership

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `057000` Schatten norms, `058000` invariant gauges, `095000` compactness, `097000` Ky Fan dominance. **Next:** `099000` Hilbert–Schmidt and trace-class operators.

<!-- BEGIN SPOKEN LECTURE -->

# Which operators have a finite notion of total size?

Let's begin with an infinite diagonal operator. It acts on square-summable sequences, multiplying coordinate number n by one over n.

Its largest amplification is one. Its coefficients tend to zero, so it is compact. The sum of the squares of its coefficients is finite. But the sum of the coefficients themselves is infinite.

Here is the question. Is this operator small or large?

The answer depends on what we are measuring. In operator norm, its size is one. In Hilbert-Schmidt norm, its size is finite. In trace norm, it does not even have a finite value.

That is why infinite-dimensional analysis needs operator ideals. An ideal records which operators satisfy a specified kind of summability or approximation condition, and a norm records their size inside that class.

## Separate membership from measurement

Imagine an ordinary number sequence. One sequence might have a finite sum of absolute values. Another might have a finite sum of squares but an infinite sum of absolute values. Both can be bounded sequences, but they belong to different summability classes.

Exactly the same distinction occurs for sequences of singular values of operators.

In finite dimensions, any fixed list of singular values has finite sum and finite sum of squares. Every matrix is automatically trace class and Hilbert-Schmidt. There can be large quantitative differences between norms, but no membership obstruction.

In an infinite Hilbert space, there may be infinitely many singular values. Their ordinary sum can diverge even when their squared sum converges. A bounded operator may fail both conditions.

So when someone states an inequality in trace norm, we have two questions. First, does the operator belong to the trace class? Second, assuming it does, how large is the trace norm?

An operator ideal is built to answer both questions coherently.

## What makes a family of operators an ideal?

Let E and F be Hilbert spaces. We consider bounded linear maps from E to F. They need not be square operators on the same space; rectangular maps are essential when we study subspaces and coordinate embeddings.

An operator ideal selects admissible bounded maps for every compatible pair of Hilbert spaces. The admissible maps are closed under addition and multiplication by scalars.

The defining stability condition is this: start with an admissible operator T. Put any bounded map B before it and any bounded map A after it, provided all the source and target spaces match. The combined operator A T B must remain admissible.

Think about why this makes sense. If T has only finitely many independent output directions, bounded transformations cannot create infinitely many new ones. If T has square-summable singular values, bounded transformations can amplify them by fixed factors, but cannot turn a finite square sum into an infinite one.

This is called the two-sided ideal property.

The ideal norm follows the same pattern. The size of A T B in the ideal norm is bounded by the ordinary operator norm of A, times the ideal norm of T, times the ordinary operator norm of B.

This estimate is central when an operator is compressed to a subspace or moved through an isometric coordinate representation.

## Three concrete examples

The first ideal is the compact operators. A compact operator is one that can be approximated arbitrarily well in operator norm by finite-rank operators. For this ideal, the ordinary operator norm is a natural ideal norm.

The second example is the Hilbert-Schmidt class. For a compact operator, square every singular value, add the results, and take the square root. If that is finite, the operator is Hilbert-Schmidt.

The third example is the trace class. Add the singular values themselves. If their sum is finite, the operator is trace class. That sum is the trace norm, sometimes called the nuclear norm.

In infinite dimensions, trace class is contained in Hilbert-Schmidt, and Hilbert-Schmidt is contained in compact operators.

Let's check this using diagonal examples rather than memorizing the containment diagram.

Our operator with coefficients one over n has squared coefficients one over n squared. Their sum is finite, so it belongs to the Hilbert-Schmidt class. But the harmonic series diverges, so it is not trace class.

Now choose coefficients one over the square root of n. They tend to zero, so the diagonal operator is compact. But their squares are one over n, and that series diverges. So this operator is not Hilbert-Schmidt.

Finally, the identity on infinite-dimensional ell two is bounded but not compact at all. Its singular-size sequence, understood through approximation numbers, remains equal to one forever.

These examples tell us that the three classes are genuinely different, even though every finite matrix belongs to all three.

## Why changing coordinates does not change the size

Suppose we rotate the source and output coordinates by unitary operators. These preserve lengths and inner products. They can change the matrix entries of T, but they preserve its singular values.

A symmetric operator ideal is designed so that the associated gauge is unchanged by such unitary transformations. The choice of orthonormal coordinates should not change whether an operator belongs, or how large it is in that ideal.

The adjoint behaves similarly. T and its adjoint have the same positive nonzero singular values, counted with multiplicity. Hence the familiar symmetric ideals give them equal norms and corresponding membership.

When the source and target Hilbert spaces are different, one may not be able to extend every geometric correspondence to a unitary between the full spaces. This is why ideal theory also works with rectangular maps, partial isometries, and the positive modulus of an operator.

The invariance is about the singular action, not about the superficial arrangement of matrix entries.

## An extended gauge records nonmembership

There is a useful mathematical convenience. Instead of defining the trace norm only for trace-class operators, we can first assign an extended value to every bounded operator.

If the singular values have finite sum, the extended trace gauge is that sum. If the sum diverges, the extended gauge is infinity.

The same design works for Hilbert-Schmidt energy and more general symmetric ideal gauges. A finite value indicates membership in the associated ideal. An infinite value indicates nonmembership.

Why bother doing that? It lets us write certain inequalities uniformly without splitting them into separate cases at every line. But we must remember that infinity is not an ordinary real number.

Suppose we want a perturbation bound in trace norm. The proper conclusion contains both statements: the perturbed quantity is trace class, and its finite trace norm satisfies the bound. We cannot skip the membership claim and treat an infinite extended value like a finite norm.

## Operator norm convergence is too weak for some ideals

Here is a revealing sequence of finite-rank operators. For each N, make a diagonal operator whose first N entries are one over N and whose later entries are zero.

Its ordinary operator norm is one over N. That tends to zero. So the operators converge to zero in operator norm.

But each has exactly N nonzero singular values, all equal to one over N. Their trace norm is N times one over N, which equals one.

The sequence does not converge to zero in trace norm.

This is the difference between controlling the worst individual stretching direction and controlling the sum over all directions. Even a huge collection of tiny stretches can have substantial total size.

The ideal norm is generally stronger than the ordinary operator norm. A sequence converging in trace norm also converges in operator norm, but the converse is false.

When we approximate an operator using finite spectral cutoffs, we have to specify which of these two kinds of error our theorem actually controls.

## Where the composition bound comes from

We can derive the ideal inequality for Schatten norms using approximation numbers.

Start with an operator T and a low-rank approximation R. If we compose both with bounded maps A and B, the approximation A R B has rank no larger than R. The error between A T B and A R B is at most the product of the operator norms of A and B and the original approximation error.

Taking the best error at each rank gives an inequality for every approximation number. If we then raise these nonnegative numbers to a power p at least one, sum them, and take the p-th root, we get the Schatten p composition bound.

For p equal to one, this is the trace norm. For p equal to two, it is the Hilbert-Schmidt norm.

An orthogonal projection has operator norm at most one. Consequently, compressing a Schatten-class operator with orthogonal projections cannot increase its Schatten norm.

This is particularly useful when comparing a full operator with one of its spectral blocks.

## Completeness and what it does not guarantee

The standard Schatten ideals are complete under their ideal norms. Their finite-rank operators are dense for finite p, because we can discard singular values after N terms and make the remaining p-power sum as small as desired.

The compact operators are also complete in the operator norm, and finite-rank operators are dense there as well.

But finite-rank density is not a consequence of every possible symmetric-ideal axiom. Some larger ideals have norms for which the finite-rank closure is a proper subspace. So when a proof uses finite-rank approximation in a particular ideal norm, that property must be available for the chosen ideal.

## One operator, three answers

Return to the diagonal operator with coefficients one over n. In operator norm it has size one. In Hilbert-Schmidt norm it has a finite size determined by the convergent sum of one over n squared. In trace norm it has no finite size at all.

We did not change the operator. We changed the kind of cumulative behavior we wanted to measure.

That is the role of a symmetric operator ideal: it supplies a coordinate-invariant notion of operator size, a class of operators on which that size is finite, and stability under bounded composition. In infinite-dimensional perturbation theory, those three ingredients are what make a norm estimate meaningful.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

A symmetric operator ideal family provides a carrier Mem(T) for rectangular bounded operators and a gauge with composition control and adjoint invariance. An extended gauge equals the finite gauge on members and infinity off the carrier. The compact ideal's carrier is compactness and its finite gauge is operator norm. Schatten p membership, for p at least one, means the p-th powers of approximation numbers are summable; p=2 is Hilbert–Schmidt and p=1 is trace class. The infinite-dimensional identity has finite operator norm but infinite p-gauge for each finite p.

### Actual Lean source declarations

`DavisKahan/OperatorIdeal/UnitarilyInvariant/FamilyCore.lean` — `Core.extendedGauge_ne_top_iff` (declaration header, proof omitted):

```lean
theorem Core.extendedGauge_ne_top_iff {A : E →L[𝕜] F} :
    Core.extendedGauge N A ≠ ∞ ↔ N.Mem A := by
```

`ForTauCeti/Analysis/OperatorIdeal/Family/CompactOperator.lean` — `mem_finiteSubmodule_compactOperatorIdealFamily` (declaration header, proof omitted):

```lean
theorem mem_finiteSubmodule_compactOperatorIdealFamily {A : E →L[𝕜] F} :
    A ∈ ((compactOperatorIdealFamily.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ↔
      IsCompactOperator A := by
```

`ForTauCeti/Analysis/OperatorIdeal/Family/Schatten.lean` — `IsSchattenClass` (declaration header, proof omitted):

```lean
def IsSchattenClass (p : ℝ) (T : E →L[𝕜] F) : Prop := T.schattenENorm p ≠ ∞
```

**Type and hypothesis map.** The notation `N.Mem` is the family carrier. Finiteness of the extended `ℝ≥0∞` gauge is equivalent to membership. Compact-ideal membership is exactly `IsCompactOperator`. `schattenENorm p` is an extended-valued gauge, finite on the Schatten carrier.

These are exact excerpts from the supplied DKPS source snapshot. The mathematical narration develops its arguments independently; citing these declarations does not assert that the narrated intermediate proof has been separately compiled in Lean. Where the current declaration lives in `ForTauCeti`, its placement does not imply the mathematical result originated outside the DKPS project.
