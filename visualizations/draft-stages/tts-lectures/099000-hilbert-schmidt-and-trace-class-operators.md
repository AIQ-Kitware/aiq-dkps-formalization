# 099000 — Hilbert–Schmidt and trace-class operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `012000` adjoints and Riesz, `036000` SVD, `074000` integration and L2, `098000` operator ideals. **Next:** `100000` modulus, polar factors, and ideal invariance.

<!-- BEGIN SPOKEN LECTURE -->

# Measuring the energy of an operator

In finite dimensions, the Frobenius norm of a matrix can be calculated in two ways. We can square and sum every matrix entry, or square and sum its singular values. Those totals agree because orthonormal changes of coordinates preserve squared length.

The Hilbert–Schmidt construction extends this to infinite-dimensional Hilbert spaces. It lets us measure the total squared output length of an operator on an orthonormal basis, and the result is independent of which basis we choose.

We will prove that independence, connect the formula to singular values, then distinguish Hilbert–Schmidt operators from trace-class operators. Finally, we will derive the trace and explain why products of two Hilbert–Schmidt operators are trace class.

## Start with an orthonormal basis

Let T map a Hilbert space E boundedly into another Hilbert space F. Choose an orthonormal basis e one, e two, and so on, assuming for illustration that E is separable.

Form the sum of the squared lengths of T e n. Every term is nonnegative, so the sum is well-defined as an extended nonnegative real value, possibly infinity.

We call this the Hilbert–Schmidt energy of T. If it is finite, T is Hilbert–Schmidt, and the square root of the energy is its Hilbert–Schmidt norm.

For a diagonal operator on ell two with coefficients t n, the energy is simply the sum of squared absolute values of t n.

Take t n equal to one divided by n. The sum of one over n squared converges. Thus this diagonal operator is Hilbert–Schmidt. If instead t n equals one divided by the square root of n, the energy is the harmonic series and diverges. This operator is compact but not Hilbert–Schmidt.

The definition seems to depend on the chosen basis. To make it intrinsic, we must prove otherwise.

## Why the basis does not matter

Choose an orthonormal basis f j of the output space as well. By Parseval's identity, the squared norm of T e n equals the sum over j of the squared absolute values of the inner products between T e n and f j.

Summing over n produces a double sum of nonnegative terms. Since nonnegative sums can be rearranged, interchange the order of the two indices.

By the defining identity of the adjoint, the inner product between T e n and f j equals the corresponding inner product between e n and T adjoint f j, up to the usual conjugation convention. Their absolute values are equal.

Apply Parseval again, now in the input space. Summing over n yields the squared norm of T adjoint f j. Summing over j gives exactly the Hilbert–Schmidt energy of T adjoint, computed in the output basis.

So the energy of T in one input basis equals the energy of its adjoint in any output basis. Apply the same argument with a second input basis and the same output basis. Both calculations agree.

This proves basis independence and, at the same time, equality of the Hilbert–Schmidt norms of T and T adjoint.

For nonseparable Hilbert spaces the basis index can be arbitrary; sums of nonnegative terms are defined by suprema over finite subsets. The same proof works with that convention.

## The operator inner product

For two Hilbert–Schmidt operators S and T with the same input and output spaces, define their Hilbert–Schmidt pairing by summing the inner products of S e n with T e n over an orthonormal input basis.

The Cauchy–Schwarz inequality for series bounds the absolute value of the sum by the product of their Hilbert–Schmidt norms. It therefore converges absolutely and defines an inner product on the Hilbert–Schmidt class.

Its squared norm agrees with the energy we just defined. The Hilbert–Schmidt class is complete under this norm, so it is itself a Hilbert space.

In finite dimensions, this pairing is the familiar trace of S adjoint T. We will now explain when that trace makes sense in infinite dimensions.

## Trace class is a stronger condition

If T is compact, list its singular values s one, s two, and so on. T is trace class when the sum of these singular values is finite. Its trace norm is that sum.

Every trace-class operator is Hilbert–Schmidt: since the singular values have a finite sum, they are bounded and their squares also have a finite sum. But the reverse fails. The diagonal with t n equal to one divided by n is Hilbert–Schmidt, while its trace norm would be the divergent harmonic series.

For a positive trace-class operator, the trace is the sum of its nonnegative eigenvalues, counted with multiplicity. The trace norm and trace agree in this positive case.

For a general trace-class operator, define its trace by summing the diagonal inner products between e n and T e n. This sum converges absolutely and does not depend on the orthonormal basis.

The bound on the absolute value of the trace by the trace norm is essential. It protects the definition against basis changes and conditional rearrangements.

## Why two Hilbert–Schmidt factors make a trace-class product

Suppose S maps E to F and T maps F to E, and both are Hilbert–Schmidt. The composition T S maps E to itself.

Intuitively, each factor loses enough singular-value mass that their product has summable singular values. More precisely, the Schatten Hölder inequality gives the trace norm of T S at most the Hilbert–Schmidt norm of T times the Hilbert–Schmidt norm of S.

One route to the inequality uses finite-rank approximations. First prove it for matrices by singular-value inequalities and Cauchy–Schwarz, then approximate S and T in their Hilbert–Schmidt norms by finite-rank maps. The estimates make the products Cauchy in trace norm; completeness of trace class supplies the limit, which agrees with T S in operator norm.

Another route factors a nuclear operator through the square root of its modulus, producing two Hilbert–Schmidt factors. This factorization explains why the trace norm is naturally connected to a product of two square-summable quantities.

## An example of the product estimate

On ell two, let both factors be diagonal with entries one over n. Each is Hilbert–Schmidt because the sum of squared entries converges. Their product has diagonal entries one over n squared, whose ordinary sum is finite. Thus the product is trace class.

This example makes the exponent arithmetic visible: multiplying two square-summable sequences gives a summable product by Cauchy–Schwarz. The operator theorem generalizes that estimate to maps that cannot be simultaneously diagonalized.

## Cyclicity with a bounded factor

If T is trace class and B is bounded, both B T and T B are trace class when the compositions are square. The trace satisfies trace of B T equals trace of T B.

The finite-dimensional proof expands entries and rearranges a finite sum. In infinite dimensions we justify cyclicity using finite-rank approximations and continuity of the trace in trace norm. Without the trace-class hypothesis, the two displayed traces might fail to exist.

This caveat prevents a common error: the ordinary operator trace is not defined on every bounded operator, and cyclic rearrangement cannot rescue a divergent sum.

## Spectral truncation in ideal norm

For a Hilbert–Schmidt compact operator, truncate its singular-value expansion after N terms. The squared Hilbert–Schmidt norm of the remainder is the sum of squares of singular values beyond N, which tends to zero by summability.

For a trace-class operator, the trace norm of the same remainder is the tail sum of singular values, which also tends to zero.

This proves finite-rank density in both norms and provides the bridge from finite matrix proofs to the infinite-dimensional ideal theorems we need later.

The central distinction to retain is that different summability conditions define different classes. A bound on the largest singular value alone says nothing about the total square energy or the trace sum. Those require their own ideal estimates.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a Hilbert basis e_i of E, HS energy of T:E→F is sum_i ‖T e_i‖², with extended value allowed. Parseval, the adjoint identity and interchange of nonnegative sums prove basis independence and equality with HS energy of T*. For compact T this energy equals sum_i s_i(T)². The trace-class norm is sum_i s_i(T); absolute summability ensures the basis-independent trace ∑⟨e_i,T e_i⟩. Two Hilbert–Schmidt factors compose to trace class with nuclear norm ≤ product of their Hilbert–Schmidt norms.

### Actual Lean source declarations

`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtBasis.lean` — `hilbertSchmidtBasisEnergy_indep` (declaration header, proof omitted):

```lean
theorem hilbertSchmidtBasisEnergy_indep
    {ι κ : Type*} (b c : HilbertBasis ι 𝕜 F)
    (d : HilbertBasis κ 𝕜 E) (A : F →L[𝕜] E) :
    hilbertSchmidtBasisEnergy b A =
      hilbertSchmidtBasisEnergy c A := by
```

`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtBasis.lean` — `approximationNumberEnergy_eq_basisEnergy` (declaration header, proof omitted):

```lean
theorem approximationNumberEnergy_eq_basisEnergy {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A = hilbertSchmidtBasisEnergy b A := by
```

`ForTauCeti/Analysis/OperatorIdeal/Nuclear/Trace.lean` — `nuclearTrace_eq_tsum_inner` (declaration header, proof omitted):

```lean
theorem nuclearTrace_eq_tsum_inner
    (A : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) (hA : A.nuclearENorm ≠ ∞) :
    A.nuclearTrace = ∑' i, ⟪b i, A (b i)⟫_𝕜 := by
```

`ForTauCeti/Analysis/OperatorIdeal/Nuclear/Trace.lean` — `norm_nuclearTrace_le_nuclearENorm` (declaration header, proof omitted):

```lean
theorem norm_nuclearTrace_le_nuclearENorm
    (A : E →L[𝕜] E) (hA : A.nuclearENorm ≠ ∞) :
    ‖A.nuclearTrace‖ ≤ A.nuclearENorm.toReal := by
```

**Type and hypothesis map.** The input-basis energy is unchanged between Hilbert bases using adjoint cross-swap. This bridge relates the approximation-number energy to basis-column energy; note all Hilbert basis assumptions. The `nuclearENorm ≠ ∞` hypothesis is essential for the basis-independent trace series. A trace-class hypothesis yields the canonical trace bound.

These are exact excerpts from the supplied DKPS source snapshot. The mathematical narration develops its arguments independently; citing these declarations does not assert that the narrated intermediate proof has been separately compiled in Lean. Where the current declaration lives in `ForTauCeti`, its placement does not imply the mathematical result originated outside the DKPS project.
