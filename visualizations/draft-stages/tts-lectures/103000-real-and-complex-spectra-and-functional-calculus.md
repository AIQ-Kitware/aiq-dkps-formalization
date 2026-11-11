# 103000 — Real and complex spectra and functional calculus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `032000` finite functional calculus, `075000` continuous functional calculus, `079000` Borel calculus, `102000` real Hilbert complexification. **Next:** `104000` real versions of unbounded Sylvester bounds.

<!-- BEGIN SPOKEN LECTURE -->

# Can a spectral projection built with complex numbers be real?

Take a real diagonal matrix with eigenvalues negative two and three. Suppose you want to keep the first eigendirection and discard the second.

There's an obvious answer: use the projection that keeps the first coordinate and kills the second.

But let's construct that projection in a different way, without writing down the eigenvectors.

Consider the function that takes a number t to three minus t, divided by five. At negative two, the function is one. At three, it is zero.

Now apply that function to the matrix. Since the function is a polynomial, this means take three times the identity, subtract the matrix, and divide by five. The resulting matrix is exactly the projection we wanted.

We've selected a spectral subspace by applying a scalar function to an operator. This is the basic idea of functional calculus.

Now imagine that the available spectral theorem was proved over complex Hilbert spaces, while the operator and the subspace we care about are real. Can we use the complex theorem and recover a genuine real projection, with no change in norms or spectral gaps?

## First preserve the resolvent test

A real Hilbert space can be complexified by replacing each real vector with a pair, written x plus i y. A bounded real operator T becomes a complex operator by applying T separately to x and to y.

The original real space sits inside as the vectors with imaginary part zero. Complex conjugation identifies that real copy: it fixes x plus i zero.

Suppose we shift T by a real number t. The question is whether T minus t times the identity has a bounded inverse.

If it has a real inverse, complexify the inverse. It undoes the complexified shifted operator, so the complex inverse exists.

Conversely, suppose the complexified shifted operator has a bounded inverse. The shifted operator commutes with conjugation, and its inverse must commute with conjugation as well. Therefore that inverse carries real vectors to real vectors. Restricting to the real copy gives a bounded real inverse.

So for a real scalar t, the shifted operator is invertible over the reals exactly when its complexification is invertible at that same t.

This proves agreement of the real-scalar resolvent tests. We have not said that an arbitrary real operator has the same entire spectrum in every sense. For example, a real ninety-degree rotation acquires the complex eigenvalues i and negative i after complexification.

## Self-adjointness makes spectral location transfer

Now assume T is self-adjoint on the real Hilbert space.

Its complexification is also self-adjoint, because complexification respects adjoints. The complex spectral theorem then places its spectrum on the real number line.

That removes the extra nonreal spectral possibilities. The real spectrum of T, defined through real-scalar invertibility, agrees with the complex spectrum of its complexification after identifying real numbers with points on the real axis.

In our diagonal example, both versions have spectral values negative two and three. The same separation survives complexification.

Why do we care about exact preservation? If an estimate depends on a gap of five, changing fields should not replace that number with a weaker constant. The norm-preserving complexification and the matching real spectral locations let us keep the original numerical bound.

## From polynomials to continuous functions

The polynomial in our example was chosen to be one on the selected eigenvalue and zero on the other. But a matrix with many eigenvalues, or an operator with a continuous spectrum, may need a less elementary function.

For a bounded self-adjoint operator, continuous functional calculus assigns an operator to every continuous function on its spectrum. It respects addition, multiplication, adjoints, and norm limits.

Start with real polynomials. The complexified real operator commutes with conjugation. Powers of it commute with conjugation; so do real scalar multiples and sums. Thus every real polynomial applied to it commutes with conjugation.

Continuous real-valued functions on a compact real spectrum can be uniformly approximated by real polynomials. Applying the functional calculus and passing to the operator-norm limit preserves the conjugation relation.

Therefore a continuous real-valued function of a complexified real self-adjoint operator commutes with conjugation. It restricts to a bounded real operator.

Positivity and order estimates come back too. If the function is nonnegative at every spectral value, the resulting operator is positive. If it lies between two real constants on the spectrum, the operator's quadratic form lies between the corresponding bounds. Restricting to real vectors preserves those inequalities.

This is the central transfer principle for continuous spectral calculus.

## Why the gap is useful when selecting a projection

An indicator function takes the value one on a chosen set and zero outside it. Applied through spectral calculus, it should produce the projection onto that spectral part.

Indicators are generally discontinuous. This is where a spectral gap helps.

Return to the matrix with eigenvalues negative two and three. There are no spectral values between them. We are free to choose a continuous function that is one on the lower spectral component, transitions across the empty gap, and is zero on the upper component.

The function doesn't have to jump at a point in the spectrum. On the spectrum itself, it agrees exactly with the desired indicator.

Our simple polynomial, three minus t divided by five, already does the job on those two spectral points. In a more general bounded self-adjoint operator, we can choose a continuous real-valued function that equals one on one isolated closed spectral piece and zero on the other. Continuous functional calculus produces a self-adjoint idempotent operator: an orthogonal projection.

Because the function is real valued, the projection commutes with conjugation. Its restriction is the corresponding real projection, whose range is a real spectral subspace.

The open gap did two jobs: it identified a genuinely isolated part of the spectrum, and it let us use continuous rather than discontinuous functional calculus to select that part.

## What changes at a spectral boundary

Now replace the matrix with multiplication by the coordinate on square-integrable functions over the interval from zero to one.

The spectrum fills the entire interval. Suppose we want to keep the functions supported below one half and discard those supported above one half.

The required projection multiplies each function by an indicator: one for inputs below one half, zero for inputs above it. It is a perfectly well-defined bounded orthogonal projection.

But the indicator jumps at one half, right in the spectrum. There is no continuous function on the entire spectral interval that agrees with it point by point.

The continuous functional calculus alone therefore doesn't give this projection through a continuous symbol. We need bounded Borel functional calculus, or another argument that handles the discontinuity.

Real spectral measures do admit such projections, but the descent from complex space needs the corresponding conjugation-invariance argument for Borel operations. A proof that handled only uniform limits of polynomials is not enough.

This distinction is especially important for spectral selections whose boundary touches the spectrum.

## The numerical value of preserving spectra

Suppose t lies a positive distance delta away from the spectrum of a real self-adjoint operator. The norm of the shifted inverse in complex Hilbert space equals the reciprocal of that distance.

The complex inverse commutes with conjugation, so it descends to the real shifted inverse. Since complexification preserves operator norms, the same resolvent bound holds in real space with the same delta.

This illustrates the full pattern. We transfer the operator, preserve its self-adjointness and real spectral location, apply the complex theorem, and recognize the resulting bounded operator by its conjugation symmetry.

The result is a real operator with the same norm estimate. For spectral projections, a genuine gap makes the construction accessible through continuous functional calculus; a spectral boundary inside the spectrum calls for the stronger Borel theory.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For `T : E →L[ℝ] E`, invertibility at a real scalar parameter is preserved and reflected by complexification. If `T` is self-adjoint, the complexified operator is self-adjoint and its complex spectrum lies in `ℝ`; the real spectra agree. The operator-conjugation involution fixes `complexify T`. Continuous real-valued functional calculus preserves this fixed-point algebra. In a genuine gap, a continuous `spectralGapSymbol` agrees on the spectrum with the half-line indicator, permitting descent of the selected spectral projection and its range.

### Worked example: a real spectral projection via functional calculus

Let \(A=\operatorname{diag}(-2,3)\) on \(\mathbb R^2\). The real polynomial \(f(t)=(3-t)/5\) satisfies \(f(-2)=1\) and \(f(3)=0\). Therefore
\[
f(A)=\frac{3I-A}{5}=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\]
which projects onto the lower eigenspace. A continuous function agreeing with the indicator on two disjoint closed spectral components produces the corresponding gap projection. For multiplication by \(t\) on \(L^2([0,1])\), the indicator of \([0,1/2]\) is discontinuous on the spectrum, so its projection requires Borel rather than continuous functional calculus.

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
