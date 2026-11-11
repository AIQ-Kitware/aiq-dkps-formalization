# 089000 — Spectral projections and reducing domains

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `010000` orthogonal complements, `015000` reducing subspaces, `076000` projection-valued measures, `088000` unbounded domain calculus. **Next:** `090000` quadratic forms and ordered half-infinite gaps.

<!-- BEGIN SPOKEN LECTURE -->

# Cutting an unbounded operator into genuine spectral parts

For a diagonal matrix, separating the coordinates into two groups is easy. If the matrix has no entries mixing those groups, each group evolves independently under the transformation.

In infinite-dimensional spectral theory, we want to make the same kind of separation. We may want the part of an operator associated with high energies, or with one cluster of spectral values, without carrying the rest of the space along.

For a bounded operator, we can often describe this with a block matrix. For an unbounded operator, a block formula can be meaningless unless every vector to which we apply the operator belongs to its domain.

The central question is therefore: when does a spectral projection split both the Hilbert space and the allowable inputs of an unbounded operator?

## Begin with the simple diagonal model

Take ell two, the Hilbert space of square-summable sequences. Let A multiply coordinate N by N. Its domain consists of all sequences for which the weighted sequence of N times the coordinates is also square summable.

Suppose we keep only the even-numbered coordinates and erase the odd ones. Call this projection P.

Every ell-two vector splits uniquely into its even part and its odd part, and those two parts are perpendicular.

Now consider a vector in the domain of A. Its weighted coordinate squares have a finite sum. If we discard the odd terms, that sum can only decrease. So the even part remains in the domain.

Also, multiplying the coordinates by their indices and then discarding the odd ones gives the same result as discarding the odd ones and then multiplying. In other words, P commutes with A on the domain of A.

These two facts are what we need. The even and odd parts are each legal inputs, and A never mixes them.

This gives two operators: one acting on the even-coordinate Hilbert space, the other on the odd-coordinate Hilbert space. Both are unbounded, and both have precisely the weighted domain condition inherited from A.

## What can fail for a different projection

Now choose a different one-dimensional subspace: the line spanned by the vector whose first two coordinates are one and one, with all later coordinates zero.

Projecting onto that line produces a perfectly valid bounded orthogonal projection. Its range consists of finite-support vectors, so it even behaves well with the domain condition in this example.

But the line is not invariant under A. Applying A to that vector changes its first two coordinates to one and two. The result no longer lies on the original line.

So projecting and then applying A is not the same as applying A and then projecting. A mixes the chosen line with its perpendicular complement.

This distinguishes an arbitrary trial subspace from a reducing subspace. A trial subspace may be useful for approximation, but it does not necessarily define an independent part of the original operator.

## The two reducing-domain conditions

Let A be a self-adjoint operator on a Hilbert space H, and let P be an orthogonal projection. Its range is a closed subspace M.

For P to reduce A, we require two things on the domain of A.

First, P must preserve the domain. If x is an allowed input to A, then P x must also be allowed. Otherwise A applied after P might not even make sense.

Second, A applied to P x must equal P applied to A x, for every allowed x. This is commutation on the operator domain.

When these conditions hold, the complementary projection, one minus P, also preserves the domain and commutes with A. Each domain vector splits into two legal pieces, one in M and the other in its perpendicular complement.

The operator acts independently on those pieces, just as a block diagonal matrix would.

But we have earned the block picture by proving that the blocks are defined.

## Why spectral projections satisfy the conditions

A self-adjoint operator has a spectral projection for every Borel set of real spectral values. For a diagonal operator, the projection selects coordinates whose eigenvalues lie in the chosen set. For an operator with continuous spectrum, it selects an entire spectral region.

Write E of B for this projection, and let P equal E of B.

The spectral theorem gives a useful test for membership in the domain of A. A vector x belongs to the domain when the integral of the square of the spectral value against the scalar spectral measure of x is finite.

Applying P discards spectral mass outside B. Since we are integrating a nonnegative quantity, the integral cannot increase. Thus P x remains in the domain whenever x was in the domain.

Commutation follows from the same picture. Applying A multiplies each spectral component by its spectral value. Applying P removes components outside B. Those operations can occur in either order without changing the result.

So a spectral projection preserves the domain and commutes with the operator on that domain.

The selected Borel set does not need to be bounded. It might include arbitrarily large spectral values. The projection is always bounded, but the restricted operator may still be unbounded.

## Construct the restricted operator carefully

We can now define the operator part associated with M. Its Hilbert space is M, rather than all of H. Its domain is the intersection of M with the original domain of A. And its action on an allowed vector x is simply A x.

Why does A x land back in M? Because P commutes with A, and P x equals x for vectors in M. Thus P A x equals A x.

Why is the domain dense in M? Take any vector y in M. Since the original domain is dense in H, choose domain vectors approaching y. Project each of them into M. Domain preservation makes those projected vectors legal, and boundedness of P makes them approach y.

The restricted operator is symmetric because A is symmetric. But for unbounded operators, symmetry alone is not self-adjointness. We still need to justify the adjoint domain.

## Resolvents establish self-adjointness

The resolvent gives a clean route.

Choose a nonreal complex number z. Because A is self-adjoint, A minus z has a bounded inverse on the whole Hilbert space.

We claim that this inverse commutes with P. To see why, start with any vector y and let x be its image under the resolvent. Then x belongs to the domain of A, and A minus z applied to x equals y.

Apply P to both sides. Domain preservation and commutation tell us that A minus z applied to P x equals P y. By uniqueness of the solution, P x must be the resolvent applied to P y.

So applying P before or after the resolvent gives the same result.

Now suppose y lies in M. Then P y equals y, which forces the resolvent output x to lie in M as well. That output solves the shifted equation for the restricted operator.

Both nonreal shifts, with positive and negative imaginary parts, are therefore onto M. The restricted operator is densely defined and symmetric, and these surjectivity properties establish that it is self-adjoint.

This argument shows exactly why the restriction inherits self-adjointness: not because the block formula looks symmetric, but because spectral projection preserves the domain and the resolvent.

## The selected set is not automatically the spectrum

There is one last distinction. Suppose we select a Borel set B and form the restricted operator. Does its spectrum equal B?

Not necessarily. B might contain points that carry no spectral mass. And its boundary points might enter the restricted spectrum even if they were not included in the selected set.

For a concrete example, consider the operator that multiplies square-integrable functions on the real line by their input coordinate t. Select functions supported in the open interval from zero to one.

The restricted operator is multiplication by t on square-integrable functions over that interval. Its spectrum is the closed interval from zero to one. Zero and one are spectral values of the restriction, even though the selected Borel set was open.

So spectral gaps must be checked using the actual spectra of the restricted operators, rather than only the written sets used to select them.

A spectral projection gives more than a geometric decomposition. It supplies legal restricted domains, self-adjoint operator parts, and the bounded resolvents needed to analyze those parts. That is the foundation for comparing separated spectral subspaces of unbounded operators.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:D(A)\subset H\to H\) be self-adjoint and \(P=E_A(B)\) a spectral projection. Then \(P D(A)\subset D(A)\), \(APx=PAx\) for \(x\in D(A)\), and \(D(A_P)=D(A)\cap\operatorname{ran}P\). The restriction \(A_P\) is self-adjoint on \(\operatorname{ran}P\). Its resolvent is the restriction of the full resolvent, with \(P(A-z)^{-1}=(A-z)^{-1}P\). The spectrum of the restricted operator is contained in the support of the restricted spectral measure, not generally equal to the original Borel selector.

### Selected set versus restricted spectrum

For \(A=M_t\) on \(L^2(\mathbb R)\), let
\(P=E_A((0,1))\). Then \(PH\cong L^2(0,1)\) and the operator
part \(A_P\) multiplies by \(t\). Its spectrum is \([0,1]\), although
its Borel selector is \((0,1)\). Any spectral-gap hypothesis must use the
actual restricted spectra or verified bounds on them.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_mem_domain`:

```lean
theorem specProjection_mem_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    specProjection hA B hB (x : H) ∈ A.domain := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_apply_domain`:

```lean
theorem specProjection_apply_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩
      = specProjection hA B hB (A x) := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `isSelfAdjoint_specRestrict`:

```lean
theorem isSelfAdjoint_specRestrict : IsSelfAdjoint (specRestrict hA B hB) := by
```


**Type and hypothesis map.** In Lean, `A : H →ₗ.[ℂ] H` is the partially defined linear operator, and `A.domain` is the set of legal input vectors. `hA : IsSelfAdjoint A` supplies self-adjointness, while `(B : Set ℝ)` and `(hB : MeasurableSet B)` authorize a spectral selector. The first theorem proves `specProjection` preserves the domain; the second explicitly inserts that membership proof into the typed application of `A`; the final theorem states self-adjointness of `specRestrict`, the true operator part on the selected spectral range. Its proof in the source uses the domain-preserving resolvent and density, precisely the steps derived in the lecture.

**Scope:** The snippets exhibit spectral-subspace construction, domain preservation and domain-aware commutation. The narrated self-adjoint restriction proof uses the standard nonreal resolvent criterion and is not claimed to be entirely encapsulated by these excerpts. Source declarations are taken from the supplied DKPS snapshot, which includes DKPS-origin results subsequently upstreamed to TauCeti; these excerpts are not newly compiled Lean code.
