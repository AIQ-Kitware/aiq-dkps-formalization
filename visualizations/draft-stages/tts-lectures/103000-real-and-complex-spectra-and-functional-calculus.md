# 103000 — Real and complex spectra and functional calculus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `032000` finite functional calculus, `075000` continuous functional calculus, `079000` Borel calculus, `102000` real Hilbert complexification. **Next:** `104000` real versions of unbounded Sylvester bounds.

<!-- BEGIN SPOKEN LECTURE -->

# Bringing spectral information back to a real Hilbert space

To use the complex spectral theorem for a real self-adjoint operator, complexify its Hilbert space and extend the operator complex-linearly. Norms and adjoints behave compatibly under this extension. The subtler question is which spectral statements and operator functions return to the original real Hilbert space.

For a real self-adjoint operator, our goal is to use complex spectral theory and then return to a real spectral assertion. To accomplish that, we will follow an explicit chain: invertibility, spectral location, functional calculus, conjugation symmetry, and descent.

The main point will be that continuous real-valued functions of a real self-adjoint operator descend cleanly. Spectral projections across a genuine gap can then be recovered by choosing a continuous function that agrees with an indicator on the spectrum.

## First recall what spectrum tests

For a bounded operator T and a scalar lambda, the resolvent test asks whether T minus lambda times the identity is invertible with a bounded inverse.

The spectrum consists of those scalars for which this test fails. This includes failures of injectivity, surjectivity, and bounded invertibility. In infinite dimensions, eigenvalues alone do not describe the full spectrum.

Complexifying a real operator preserves products and the identity. Therefore, if T minus a real scalar is invertible over the reals, its complexification has a bounded inverse obtained by complexifying the original inverse.

The converse is more interesting. Suppose the complexified operator has a bounded complex inverse at a real scalar. Because the original complexified operator commutes with canonical conjugation, its inverse also commutes with conjugation. We prove this by multiplying the commutation identity on both sides by the inverse. The inverse therefore sends real vectors to real vectors and descends to a bounded real inverse.

So, at real scalar parameters, invertibility agrees before and after complexification. That is the key reason the real spectral information is preserved.

Notice what we did not prove: that an arbitrary real operator has exactly the same full spectrum when viewed over the complex numbers. A ninety-degree real rotation has complex eigenvalues i and minus i. Its real spectrum, in the usual real-scalar sense, cannot list those complex eigenvalues. The comparison is of real spectral parameters, and self-adjointness is what makes that comparison sufficient for our later theory.

## Why self-adjointness changes the situation

Let A be a bounded real self-adjoint operator. Its complexification is complex self-adjoint because the adjoint commutes with complexification.

The spectral theorem for a complex self-adjoint operator says that its spectrum is a compact subset of the real axis. Therefore every spectral parameter of the complexified A is real.

Since the real-scalar invertibility test agrees with the complex test, the real spectrum of A and the complex spectrum of its complexification describe the same numerical subset of the real line, after identifying real numbers with complex numbers having zero imaginary part.

This explains why we can safely use complex self-adjoint spectral theory to locate the spectrum of a real self-adjoint operator. The restriction to self-adjointness does real work.

A further example makes this concrete. Let A be the real diagonal matrix with entries minus two and three. The complexification has exactly the same two eigenvalues. Nothing about their positions changes. If instead A were the ninety-degree rotation, complexification would reveal two imaginary spectral points. We should not transfer a self-adjoint spectral conclusion to that rotation.

## Continuous functional calculus preserves conjugation symmetry

Now suppose f is a continuous real-valued function on the spectrum of the self-adjoint complexified operator.

The functional calculus associates to f an operator f of A. For polynomials with real coefficients, this is easy to understand: every power of the complexified A commutes with conjugation, real scalar coefficients preserve that property, and sums preserve it as well.

The continuous functional calculus is obtained by extending these polynomial rules through uniform approximation. Since operator-norm limits of conjugation-commuting operators still commute with conjugation, f of A also commutes with conjugation.

There is a more abstract proof using uniqueness of the continuous functional calculus as a real star-algebra homomorphism. Conjugating every operator value of the calculus gives another homomorphism that sends the identity function to the same self-adjoint operator. Uniqueness forces the two calculi to agree.

Either proof establishes the same property: applying a continuous real-valued function to a conjugation-fixed self-adjoint operator produces another conjugation-fixed operator.

A bounded complex-linear operator commuting with conjugation descends to a bounded real operator: restricting it to the real fixed vectors recovers the original action. This is the descent of the continuous functional calculus.

It also preserves positivity. If f is nonnegative on the spectrum, the spectral theorem says f of A is positive. Restricting its quadratic form to real vectors gives positivity of the descended real operator.

The same reasoning transports spectral estimates. If f lies between constants a and b on the spectrum, then the quadratic form of f of A lies between a times the squared norm and b times the squared norm. Since real vectors embed isometrically, the inequality descends with the same constants.

## An actual spectral projection requires more care

A spectral projection onto a subset S of the spectrum corresponds to the indicator function of S: one on S, zero outside S.

Indicators are usually discontinuous. Continuous functional calculus alone cannot evaluate an arbitrary discontinuous indicator. Bounded Borel calculus can, but descending every Borel operation requires additional machinery and the right invariance statements.

There is an important case where continuous calculus is enough. Suppose the spectrum is separated into two pieces by an open gap. Then a function may switch continuously from one to zero inside the gap, where there is no spectrum at all.

For our diagonal example with eigenvalues minus two and three, choose a threshold zero. Define a continuous real-valued function that equals one below zero, decreases through the empty gap, and equals zero at and above three. On the spectrum, that function is exactly the indicator of the lower spectral component.

Functional calculus gives the projection onto the minus-two eigenspace. Its matrix is diagonal with entries one and zero. Because the function is real valued, the projection commutes with conjugation and therefore descends to the real plane.

We can also describe it without choosing eigenvectors. The descended real operator is idempotent and self-adjoint. Its complexification is the complex spectral projection. Hence its real range complexifies to the chosen complex spectral subspace.

This is the mechanism behind real spectral subspaces associated with an actual gap.

## What happens at a spectral boundary

Consider a self-adjoint multiplication operator whose spectrum fills an interval and choose a threshold in its interior. The indicator of the lower half is discontinuous at that threshold.

The bounded Borel spectral projection still exists in complex Hilbert space, but it no longer arises from the same simple continuous function that equals the indicator on the entire spectrum.

For special operators, we may prove conjugation invariance of that Borel projection directly, or approximate indicators in a suitable strong topology. Those are additional arguments. It would be incorrect to claim that the continuity proof above automatically handles every Borel set.

This difference matters because Davis–Kahan theorems frequently select exact spectral subspaces. Sometimes the selected set is separated from the remainder by a positive gap, so continuous calculus suffices. Other formulations permit boundaries touching the spectrum and need the full Borel spectral framework.

## Resolvents and gap preservation

We can now connect spectra to numerical estimates. If a real self-adjoint A has spectrum at least delta away from a real scalar t, then the complex self-adjoint resolvent has operator norm at most one divided by delta.

The resolvent of the real operator is obtained by descent, and complexification preserves operator norm. Therefore the same bound holds on the real Hilbert space, with no extra dimension-dependent constant.

That is an example of a transferable inequality whose hypotheses and conclusion survive exactly.

But spectral separation for two operators is not, by itself, a promise that every operator-norm Sylvester bound has constant one. Earlier we proved that ordering of spectra gives stronger integral estimates than mere pairwise disjointness. Complexification preserves our data; it does not strengthen the gap hypothesis.

## The strategy

We have proved how to transfer bounded spectral structure.

Our standard will be the same. State the exact object being transported. Prove that its defining data survive. Then use complex theory and descend the conclusion with the same constants.

The spectrum of a self-adjoint operator controls its functional calculus. Conjugation symmetry tells us which of the constructed bounded operators are genuinely real. Together, these principles allow complex proofs to produce real spectral projections and resolvent estimates without replacing the underlying real problem.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For `T : E →L[ℝ] E`, invertibility at a real scalar parameter is preserved and reflected by complexification. If `T` is self-adjoint, the complexified operator is self-adjoint and its complex spectrum lies in `ℝ`; the real spectra agree. The operator-conjugation involution fixes `complexify T`. Continuous real-valued functional calculus preserves this fixed-point algebra. In a genuine gap, a continuous `spectralGapSymbol` agrees on the spectrum with the half-line indicator, permitting descent of the selected spectral projection and its range.

### Actual Lean source declarations

`ForTauCeti/Analysis/InnerProductSpace/Complexification/Spectrum.lean` — `mem_spectrum_complexify_iff` (exact declaration header; proof omitted):

```lean
theorem mem_spectrum_complexify_iff (T : E →L[ℝ] E) (r : ℝ) :
    (r : ℂ) ∈ spectrum ℂ (complexify T) ↔ r ∈ spectrum ℝ T := by
```

`ForTauCeti/Analysis/InnerProductSpace/Complexification/FunctionalCalculus.lean` — `conjugateOperator_cfcHom` (exact declaration header; proof omitted):

```lean
theorem conjugateOperator_cfcHom
    (C : RealComplexification E →L[ℂ] RealComplexification E) (hC : IsSelfAdjoint C)
    (hfix : conjugateOperator C = C) (g : C(spectrum ℝ C, ℝ)) :
    conjugateOperator (cfcHom hC g) = cfcHom hC g := by
```

`DavisKahan/SpectralTheory/Complexification/BoundedGapProjection.lean` — `realBoundedSpectralProjectionIicOfGap` (exact declaration header; proof omitted):

```lean
noncomputable def realBoundedSpectralProjectionIicOfGap
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (_hdelta : 0 < delta)
    (_hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    E →L[ℝ] E :=
```

`DavisKahan/SpectralTheory/Complexification/BoundedGapProjection.lean` — `complexify_realBoundedSpectralProjectionIicOfGap` (exact declaration header; proof omitted):

```lean
theorem complexify_realBoundedSpectralProjectionIicOfGap
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    complexify (realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap) =
      boundedSelfAdjointSpectralProjection (complexify B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          ((complexify_isSelfAdjoint_iff B).2 hB))
        (Set.Iic alpha) measurableSet_Iic := by
```

**Type and hypothesis map.** The spectral membership theorem compares **real scalar parameters** for the real operator and its complexification. `conjugateOperator_cfcHom` assumes a self-adjoint complexified-space operator fixed by conjugation and a real-valued continuous symbol. The real spectral projection constructor requires a strictly positive gap and spectral containment in two separated half-lines; the companion theorem identifies its complexification with the selected complex spectral projection. The cited declarations do not by themselves assert descent for every arbitrary Borel indicator.

These Lean snippets are copied exactly from the supplied DKPS repository snapshot. The narration is an independent mathematical derivation; this appendix does not claim that the narrated text was compiled in Lean. Foundational results currently in `ForTauCeti` may have been developed in DKPS before upstreaming.
