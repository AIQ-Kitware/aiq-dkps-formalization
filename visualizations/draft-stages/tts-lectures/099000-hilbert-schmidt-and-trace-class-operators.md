# 099000 — Hilbert–Schmidt and trace-class operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `012000` adjoints and Riesz, `036000` SVD, `074000` integration and L2, `098000` operator ideals. **Next:** `100000` modulus, polar factors, and ideal invariance.

<!-- BEGIN SPOKEN LECTURE -->

# Two ways to add up the size of an operator

Imagine a two-by-two diagonal matrix. It stretches the first coordinate by three and the second by one.

What is the size of this matrix? If we ask for the maximum stretch of a unit vector, the answer is three. If we add the squared magnitudes of every entry and take the square root, the answer is square root of ten. If we add its two singular values, the answer is four.

All three answers are correct. They measure different things.

The first is the operator norm. The second is the Frobenius norm. The third is the trace norm.

In infinite dimensions, the difference becomes more than a numerical choice. The Frobenius-style calculation may converge while the trace-norm calculation diverges. That is why we distinguish Hilbert-Schmidt operators from trace-class operators.

## Extend the Frobenius calculation

Let's start with ell two, the Hilbert space of square-summable sequences. An operator T acts on each standard basis vector, one at a time. We can measure the length of every resulting output vector.

Square those output lengths and add them over all basis vectors. This sum might be finite or infinite. When it is finite, we say T is Hilbert-Schmidt. The square root of the sum is its Hilbert-Schmidt norm.

Why is this the infinite-dimensional Frobenius norm? In a finite matrix, the image of a standard basis vector is one column of the matrix. The squared length of that column is the sum of the squared magnitudes of its entries. Adding over all columns produces exactly the sum of squared magnitudes of every matrix entry.

So the Hilbert-Schmidt construction is simply the same calculation allowed to run over infinitely many orthonormal input directions.

For a diagonal operator with coefficients one over n, applying T to basis vector n produces a vector of length one over n. The squared lengths add to the convergent series one plus one quarter plus one ninth, and so forth. This operator is Hilbert-Schmidt.

Change the coefficients to one over the square root of n. They still tend to zero, so the diagonal operator is compact. But their squared lengths add to the harmonic series, which diverges. So this operator is not Hilbert-Schmidt.

We are measuring accumulated squared output size, not merely the largest output size.

## A serious question: which basis?

Our definition appeared to depend on the chosen orthonormal basis. Suppose we rotate the basis. Do we get a different Hilbert-Schmidt norm?

We need to prove that we do not.

Take one orthonormal basis in the input space, and another orthonormal basis in the output space. We will temporarily call their vectors e and f.

Apply T to one input basis vector e. Parseval's identity says the squared length of T e equals the sum of the squared magnitudes of its inner products with all the output basis vectors f.

Now add that identity over every input basis vector. We have a double sum: one index for input directions and one for output directions.

Every summand is nonnegative. That lets us exchange the order of summation without relying on conditional cancellation.

Next use the adjoint. The inner product of T e with f has the same absolute value as the inner product of e with T adjoint applied to f. This simply transfers T from one side of the inner product to the other.

For each fixed output basis vector f, Parseval's identity in the input space now adds the squared inner products over e. The result is the squared length of T adjoint f.

We have proved that the sum of squared output lengths of T in the input basis equals the corresponding sum for T adjoint in the output basis.

Now repeat the calculation with a different input basis but the same output basis. Both versions give the same sum for T adjoint. Therefore the original sum is independent of the input basis.

We also learned that T and its adjoint have equal Hilbert-Schmidt norms.

For a nonseparable Hilbert space, orthonormal bases may have arbitrary index sets. The same reasoning uses suprema of finite subsums in place of a single numbered series.

## Connect the energy to singular values

For a compact operator T, its singular values measure the stretches in its mutually orthogonal singular directions. When we choose those directions as part of an orthonormal basis, T sends the n-th singular direction to a vector of length equal to the n-th singular value.

Because the Hilbert-Schmidt energy is basis independent, we may compute it using these convenient directions. We get the sum of the squares of all singular values.

So there are two equivalent descriptions. We can square the output lengths on any orthonormal input basis, or we can square the singular values and sum them. They give the same Hilbert-Schmidt energy.

This equivalence helps us move between concrete matrix entries and the intrinsic spectral description of an operator.

## The Hilbert-Schmidt operators form a Hilbert space

There is a further payoff. Suppose S and T are both Hilbert-Schmidt and have the same input and output spaces.

Apply each operator to an orthonormal input basis. Take the inner product of S e with T e for each basis vector e, and add those inner products.

The ordinary Cauchy-Schwarz inequality for series tells us that the absolute sum is bounded by the product of the two Hilbert-Schmidt norms. Therefore this pairing is well-defined.

It behaves like an inner product on the space of operators. Pairing T with itself gives its squared Hilbert-Schmidt norm. And the class is complete in that norm.

That means Hilbert-Schmidt operators form a Hilbert space in their own right. We can use familiar geometric ideas, such as orthogonality and projections, but now the points of the space are operators rather than vectors.

In finite dimensions this pairing is the Frobenius inner product. In infinite dimensions it is the corresponding trace pairing, once we establish why the trace exists.

## Why trace class is stricter

For a compact operator, take its singular values and add them without squaring. If the sum is finite, the operator is trace class. That sum is its trace norm.

Our diagonal operator with coefficients one over n is the perfect separator. It has a finite sum of squared singular values, but an infinite sum of singular values. So it is Hilbert-Schmidt and not trace class.

Any trace-class operator is Hilbert-Schmidt. Here is the reason. A summable sequence of nonnegative singular values is bounded, and multiplying each value by itself cannot destroy summability when all the values are uniformly bounded. More concretely, the sum of squares is at most the largest singular value times the sum of singular values.

Thus trace class sits inside Hilbert-Schmidt. The containment is strict in infinite dimensions.

In finite dimensions every matrix belongs to both classes. It is the infinite number of directions that creates the membership question.

## The trace itself

For a positive trace-class operator on a single Hilbert space, the trace is the sum of its eigenvalues, counted with multiplicity. Because the operator is positive, the eigenvalues are nonnegative, and this sum equals its trace norm.

For a general trace-class operator on one Hilbert space, the trace can be computed by choosing any orthonormal basis and summing the diagonal inner products of each basis vector with its image under the operator.

The trace-class condition ensures that this series converges absolutely and that the answer is independent of the basis. The absolute value of the trace is at most the trace norm.

The distinction between trace and trace norm is important. The trace can involve cancellations, and it may even be zero for a nonzero operator. The trace norm adds the nonnegative singular values and never relies on cancellation.

Also, the trace belongs naturally to operators from a Hilbert space back to itself. The trace norm still makes sense for rectangular operators between different Hilbert spaces.

## Why multiplying two square-summable operators works

Suppose S sends vectors from E to F, and T sends vectors from F back to E. Both are Hilbert-Schmidt.

Their composition T after S maps E back to itself. A powerful theorem says that this product is trace class, with trace norm at most the Hilbert-Schmidt norm of T times the Hilbert-Schmidt norm of S.

Let's see the mechanism in a diagonal example. Suppose both factors multiply coordinate number n by one over n. Each factor is Hilbert-Schmidt, because the sum of one over n squared converges.

Their product multiplies coordinate n by one over n squared. Now the sum of the singular values of the product converges. So the product is trace class.

The scalar calculation suggests Cauchy-Schwarz: multiplying two square-summable sequences produces a summable sequence.

For general operators we cannot assume the factors share singular vectors. The operator version is a Schatten Holder inequality. One rigorous route starts with finite-rank approximations, proves the matrix inequality, and then passes to the limit in the Hilbert-Schmidt and trace norms. It yields exactly the same product bound without requiring simultaneous diagonalization.

The operator inner product from a moment ago can now be identified with the trace of a product involving the adjoint. Its existence is explained by this theorem.

## Cyclicity needs a finite trace

In finite-dimensional linear algebra, we know the trace of B T equals the trace of T B. In infinite dimensions, we must ensure both traces are defined.

If T is trace class and B is bounded on the same Hilbert space, then both products are trace class, and the traces are equal.

The proof can begin with finite-rank T, where ordinary matrix cyclicity applies. Approximate a general trace-class T by finite-rank operators in trace norm. The trace is continuous in that norm, so the identity passes to the limit.

Without a trace-class hypothesis, there may be no trace to cycle. A bounded operator can have infinitely many diagonal contributions whose sum diverges.

## Return to finite-dimensional approximations

For a Hilbert-Schmidt operator, retain its first N singular directions. The squared Hilbert-Schmidt error is the sum of the squares of all omitted singular values. Since the full square sum converges, that tail tends to zero.

For a trace-class operator, the trace-norm error is the ordinary sum of the omitted singular values. It also tends to zero because the full sum is finite.

These two facts justify using finite-rank operators to prove many infinite-dimensional statements, provided the approximation is taken in the correct norm.

The lesson is that one operator can have several valid notions of size, each collecting its singular directions differently. The operator norm records the largest stretch. Hilbert-Schmidt records accumulated squared stretch. Trace norm records accumulated singular stretch. Only the last two impose the corresponding infinite-dimensional summability conditions.

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
