# 080000 - Measurable spectral restrictions

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `015000` reducing subspaces, `030000` spectral projections, `075000-079000` functional calculus and spectral measures. **Next:** `081000` resolvents from spectral integrals.

<!-- BEGIN SPOKEN LECTURE -->

# Restricting an operator to a spectral region

In finite-dimensional linear algebra, selecting several eigenspaces and restricting a self-adjoint matrix to their direct sum is routine. We now know how to make a similar selection even when the operator has no eigenvectors.

Take a bounded self-adjoint A and choose a Borel set B of real numbers. Its spectral projection E of B gives us a closed subspace K, namely the range of that projection. We want to study the operator that A induces on K, and to understand how its spectral calculus relates to the original one.

The key fact is that spectral selection is compatible with restriction. But there is an important boundary issue: the spectrum of the restricted operator need not lie inside B itself when B is not closed.

## First establish invariance

The projection P, meaning E of B, is a bounded Borel function of A. We proved last time that every Borel function of A commutes with A. Therefore A P equals P A.

Let x belong to K. Then P x equals x. Apply P to A x. By commutation, P A x equals A P x, which equals A x. Hence A x lies in K.

Now take y in the orthogonal complement of K. Because P is orthogonal, P y equals zero. Again P A y equals A P y, which is zero. Thus A y stays in the orthogonal complement.

So K reduces A. The restriction A sub K acts on a complete Hilbert space in its own right, since K is a closed subspace of H.

Self-adjointness passes to the restriction. For vectors x and y in K, their inner products with the restricted operator agree with their ambient inner products, and the self-adjoint identity for A applies. Equivalently, in the decomposition H equals K orthogonally summed with its complement, A is block diagonal.

## Spectral projections inside the subspace

Suppose C is another Borel set. The spectral projection E of C preserves K because it commutes with P. Its restriction to K is again an orthogonal projection.

What projection does it represent for A sub K? It represents the portion of the restricted spectrum lying in C. In the notation of spectral measures, E sub K of C is E of C restricted to K.

Here is the proof mechanism. For a simple scalar symbol, the functional calculus is a finite linear combination of spectral projections. Restricting that combination to K clearly agrees with the same finite combination of restricted projections.

Uniformly approximate a bounded Borel symbol by simple symbols and pass to the operator-norm limit. The identity remains true for every bounded Borel function.

In particular, calculating f of the restricted operator gives the same result as first calculating f of A and then restricting to K, after interpreting f on the restricted spectral domain.

This is called naturality of the functional calculus under restriction.

## What the range projection means

A useful identity follows immediately from the product rule:

E of C applied to a vector in K equals E of B intersect C applied to that vector.

Indeed, write a vector x in K as P x, and then E of C P x equals E of B intersect C applied to x.

If C is disjoint from B, this is zero. Thus the restriction has no spectral weight in any Borel set disjoint from B.

But be careful. This statement about spectral weight does not imply that every point of the restricted spectrum lies in B itself. It implies containment in the closure of B intersected with the original spectrum, provided K is nonzero. The closure enters because spectra are closed sets and spectral weight can accumulate near boundary points.

## The open-interval boundary example

Take A to be multiplication by t on L two of the unit interval. Let B be the open interval from zero to one half.

The range of E of B consists of functions supported in that interval, up to equality almost everywhere. On this subspace, A still multiplies by t.

What is the spectrum of the restriction? It is the closed interval from zero to one half, not the open interval. The endpoints belong to the spectrum because there are normalized functions supported in very short intervals approaching zero or one half. On such vectors, multiplication by t is arbitrarily close to multiplication by the endpoint value.

Yet neither endpoint has a nonzero eigenvector in this model. The spectral projection of each singleton endpoint is zero. We have spectral accumulation without point spectrum.

Therefore the statement that the restricted spectrum is contained in B would be false. It is the closure of the selected essential spectral support that controls the spectrum.

## Why the restricted spectrum cannot invent a new point

For a reducing subspace K, A decomposes as a block diagonal operator A sub K and A sub its complement. If a complex number z lies outside the spectrum of A, the full operator A minus z has a bounded inverse.

Because the projection onto K commutes with A, it also commutes with that inverse. We can therefore restrict the inverse to K and obtain an inverse of A sub K minus z.

So every point of the restricted spectrum was already in the spectrum of A. There can be loss of spectral values, but not new ones.

This proof is valid for bounded reducing restrictions. It is more robust than trying to track individual eigenvectors, which might not exist.

## Restriction and composition under a unitary change of coordinates

Suppose U is a unitary map and another operator T is obtained by transporting A through U. Applying any bounded Borel symbol to T gives the transported version of f of A.

The reason is again simple-function approximation. Spectral projections transport under unitary conjugation, and finite combinations inherit that property. The uniform limit preserves it.

This naturality is useful when we choose a cyclic multiplication model. A spectral restriction can be performed before or after moving to the L two coordinates. In the multiplication model, restricting to B simply keeps functions supported on B.

The mathematical result depends on the operator and spectral set, not on whichever orthonormal coordinates were chosen to display them.

## Two different operators are different

There is a possible confusion that later perturbation theory will punish. Spectral projections of the same self-adjoint operator commute. Projections associated with different self-adjoint operators generally do not.

Take a two-dimensional space. The first operator may have the coordinate axes as eigenspaces. A second operator obtained by rotating the eigenbasis has different rank-one spectral projections. Unless those axes line up in a special way, the selected projections do not commute.

Our direct-rotation and principal-angle lectures studied exactly that noncommutativity. The spectral calculus does not make it disappear.

If we perturb A to A plus a small self-adjoint operator V, it is meaningful to compare the old spectral projection P and the new spectral projection Q. We will need spectral gaps and resolvent estimates to control their difference. The result is not a consequence of a single P V M product law, because P and Q come from distinct measures.

## Restricting a bounded Borel symbol

Suppose f is bounded and measurable on the spectrum of A. Let f sub K denote the same scalar function restricted to the spectrum of A sub K. Since that spectrum is contained in the original one, this restriction makes sense.

Then f sub K of A sub K equals the restriction to K of f of A.

One can prove this from the diagonal measures. For x in K, its scalar measure for the restricted operator agrees with its ambient scalar measure, after viewing the restricted spectrum inside the full spectrum. Therefore the integrals specifying all diagonal matrix elements coincide. Polarization converts the diagonal equality into equality of operators.

That argument is also what the Lean implementation uses to connect compression with the Borel calculus, rather than relying on a selected eigenbasis.

## The result to retain

A Borel spectral region defines a closed reducing subspace. Its restricted functional calculus is the ambient calculus restricted to that subspace, and the restricted spectral projection for C is simply the ambient projection for C acting on the selected subspace.

The spectrum of the restriction lies in the original spectrum and in the closure of the selected region, but may include boundary points not contained in the original Borel set. Next we will use spectral integration to construct resolvents, whose norm detects the distance to the full spectral support.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For `P = E(B)` and `K = range P`, `PA = AP` makes `K` reducing and `A|K` self-adjoint. For a Borel `C`, `E_K(C) = E(C)|K`. For bounded Borel `f`, the restricted calculus satisfies `f(A|K) = f(A)|K` after composing symbols with the spectral inclusion. `spectrum(A|K)` is a subset of `spectrum(A)` and is contained in `closure(B intersect spectrum(A))`; it need not be a subset of a nonclosed `B`.

**Lean bridge (verbatim source declaration headers).**

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean` - `specProj_inter`:

```lean
theorem specProj_inter (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    specProj (H := H) ha hκ B₁ hB₁ * specProj ha hκ B₂ hB₂
      = specProj ha hκ (B₁ ∩ B₂) (hB₁.inter hB₂) :=
```

The product of two spectral projections is the projection of the set intersection, which makes all projections for a fixed operator commute.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Restriction.lean` - `spectrum_compress_subset`:

```lean
theorem spectrum_compress_subset (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    spectrum ℂ (compress K a) ⊆ spectrum ℂ a :=
```

The spectrum of the compressed normal operator is contained in the ambient spectrum, under the calculus-invariance hypothesis.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Restriction.lean` - `borelCalculus_compress`:

```lean
theorem borelCalculus_compress (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) :
    borelCalculus (isStarNormal_compress ha hK) (hf.comp_specIncl ha hK)
      = compress K (borelCalculus ha hf) :=
```

The Borel calculus of the restricted operator agrees with compression of the ambient Borel calculus, after restricting symbols by the spectral inclusion.

**Scope:** The excerpts are declaration headers, not complete proof bodies. Their enclosing modules supply scalar types, normality/self-adjointness assumptions, and typeclass instances. The prose derives the mathematical statements and does not claim that all of the pedagogical arguments have separate local Lean theorems.
