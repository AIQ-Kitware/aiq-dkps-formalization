# 098000 — Symmetric operator ideals and membership

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `057000` Schatten norms, `058000` invariant gauges, `095000` compactness, `097000` Ky Fan dominance. **Next:** `099000` Hilbert–Schmidt and trace-class operators.

<!-- BEGIN SPOKEN LECTURE -->

# A norm that is finite only where it belongs

In finite dimensions, every matrix has a finite nuclear norm, a finite Frobenius norm, and a finite operator norm. The space of matrices is so forgiving that we can describe all these norms without mentioning which matrices are allowed.

Infinite-dimensional Hilbert spaces force a change. The identity operator is bounded, but its singular values do not decay. It is not compact, not Hilbert–Schmidt, and not trace class. Assigning it a finite trace norm would contradict the infinite sum of its singular values.

A symmetric operator ideal addresses this by specifying two things together: a collection of admissible operators, called its carrier, and a norm-like gauge on that collection. We will derive the ideal properties, explain the extended gauge used by Lean, and compare the main examples.

## What an operator ideal contains

Let E and F be Hilbert spaces. For each compatible source-target pair, an operator ideal selects some bounded maps T from E to F.

The selected maps are closed under addition and scalar multiplication. More importantly, if T is in the ideal and A and B are arbitrary bounded operators on either side, then A T B remains in the corresponding ideal.

This is the two-sided ideal property. It says that the notion of smallness survives a bounded change of inputs and a bounded change of outputs.

A norm or gauge on the ideal should obey the usual triangle inequality, scalar homogeneity, and a composition estimate: the gauge of A T B is at most the operator norm of A times the gauge of T times the operator norm of B.

In the standard normalized setting, the ideal gauge also controls the ordinary operator norm. Thus convergence in ideal norm implies convergence in operator norm.

The index spaces matter. A bounded map between two different Hilbert spaces is not a square operator on one space, yet singular values and ideal gauges make sense for it. A useful theory must accommodate such rectangular operators from the beginning.

## Three familiar carriers

The compact operators form an ideal. The carrier consists of exactly the compact bounded operators, and its gauge can be the ordinary operator norm. This is a complete ideal, because the compact operators form a closed subspace of the bounded maps in operator norm.

The Hilbert–Schmidt class consists of maps whose squared singular values have finite sum. Its gauge is the square root of that sum. We will later obtain a basis formula that avoids explicitly choosing singular vectors.

The trace class consists of maps whose singular values have finite ordinary sum. Its gauge is the nuclear or trace norm.

The trace class is contained in the Hilbert–Schmidt class, which is contained in the compact operators. To see why the first inclusion holds, suppose the nonnegative singular values have finite sum. They are bounded, so their squares have finite sum as well. For the second inclusion, a square-summable singular-value sequence tends to zero, which is the compactness criterion.

The inclusions are strict in infinite dimensions. On ell two, diagonal coefficients one over n give a Hilbert–Schmidt operator whose trace norm diverges. Coefficients one over the square root of n tend to zero and give a compact operator whose Hilbert–Schmidt sum diverges.

## Why the gauge takes an infinite value

One convenient formal design assigns an extended nonnegative real number to every bounded operator. If an operator belongs to the ideal, its extended gauge equals its finite norm. If it is outside, its extended gauge is infinity.

This allows one triangle inequality to be written for all bounded maps. If either input is outside the carrier, the right-hand side may be infinite, and the inequality remains valid. If both inputs belong, the extended inequality reduces to the ordinary triangle inequality.

But infinity is not a real number. We cannot divide by it or treat it as an ordinary finite norm. To work inside the Banach space of ideal operators, we first establish carrier membership and then use the finite gauge.

The formalization has a precise equivalence: extended gauge not equal to infinity if and only if the operator is in the carrier. This is why a Davis–Kahan conclusion often has the form of a pair of statements: the displacement belongs to the ideal, and its gauge obeys a bound.

## Why finite ideal gauge controls ordinary errors

Suppose a sequence of trace-class operators converges in trace norm. The ideal norm dominates the ordinary operator norm, so the same sequence converges in operator norm. This means we can identify its limit as a bounded map without ambiguity.

But operator-norm convergence alone is insufficient to conclude trace-norm convergence. Consider the diagonal maps that put one divided by N on the first N coordinate positions and zero elsewhere. Their operator norms tend to zero. Each map has finite rank, yet its trace norm equals one for every N. So these operators converge to zero in operator norm but not in trace norm.

The same phenomenon matters when we replace an infinite-dimensional calculation with a finite cutoff. One must name the topology in which the approximation converges. A proof in the ordinary operator norm cannot automatically be used as a proof in a stronger ideal norm.

## The ideal inequality from approximation numbers

We can see the composition estimate concretely for Schatten classes. Suppose T has singular values s one, s two, and so on. For bounded A and B, the approximation-number inequality from lecture ninety-six gives each approximation number of A T B at most the operator norms of A and B times the corresponding approximation number of T.

Raise both sides to the p-th power and sum for p at least one. Taking the p-th root proves the Schatten composition inequality. In particular, multiplication by an orthogonal projection cannot increase a Schatten norm, because the projection's operator norm is at most one.

For a general symmetric ideal, the same contraction rule is part of the defining structure or a theorem proved from it.

## Symmetry under isometries and adjoints

A unitary change of coordinates on the source or target preserves singular values. Therefore a symmetric ideal should preserve membership and gauge under such changes.

Adjoints are equally important. T and T adjoint have the same positive nonzero singular values, with the appropriate zero-padding convention. Hence a symmetric ideal admits T exactly when it admits T adjoint, and their gauges agree.

For two Hilbert spaces of different dimensions, unitary equivalence between the whole spaces may not exist. This is why partial isometries, modulus, and rectangular transport are essential. We will prove that ideal gauges can be moved through these constructions without assuming the operator is invertible.

## Completion and finite-rank density

A well-behaved Banach ideal is complete in its ideal norm. If a sequence of ideal operators is Cauchy in that norm, it converges to another operator in the ideal, not merely to an arbitrary bounded operator outside it.

Finite-rank operators are dense in the compact ideal under operator norm. They are also dense in the Schatten p-classes for finite p under their Schatten norms, by truncating singular values and using summability of the tail.

Do not generalize finite-rank density to every possible symmetric ideal without checking its definition. A carrier may have a norm in which the finite-rank closure is a proper subideal.

## A test case to remember

Let D be diagonal on ell two with coefficients one divided by n. It is compact, because its coefficients tend to zero. Its Hilbert–Schmidt gauge is finite because the sum of one over n squared converges. Its trace gauge is infinite because the harmonic series diverges.

The same bounded map therefore belongs to two ideals and lies outside a third. Which estimate we can apply depends on the requested ideal, not just on T's ordinary operator norm.

In the next lecture we will derive the Hilbert–Schmidt and trace-class constructions carefully, including basis independence and the existence of a genuine trace.

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
