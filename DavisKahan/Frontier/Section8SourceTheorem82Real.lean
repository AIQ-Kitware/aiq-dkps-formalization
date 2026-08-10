/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8SourceTheorem82
import DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv

/-!
# Davis--Kahan 1970, Theorem 8.2, over a real Hilbert space

Standing assumption 1 of the source says the Hilbert space is "real or
complex".  Every Section 8 declaration in this repository was stated over `ℂ`.
This module descends Theorem 8.2 to a real Hilbert space.

## Why this is an exact transport, where Theorem 8.1 was not

`Section8/SourceTheorem81Real.lean` had to do real work: Theorem 8.1 *asserts
the existence* of the canonical branch, so its real form has to exhibit a real
subspace whose complexification is the complex branch, and that needed the
bounded-gap spectral descent `realBoundedSpectralSubspaceIicOfGap`.  Picking an
arbitrary reducing subspace would not have done.

Theorem 8.2 carries no such existential.  Both subspaces are supplied by the
caller together with their spectral placements, and every printed hypothesis
and every conclusion is preserved **and reflected** by complexification:

* `spectrumIn_complexifySubmodule_iff` for the three spectral placements;
* `complexify_reduces_iff` for `P` reducing `A`;
* `norm_complexify` for both smallness alternatives;
* `directedGap_complexifySubmodule` and `subspaceGap_complexifySubmodule` for
  the conclusions.

So the theorems below are exact transports.  They add no hypothesis the printed
statement does not have: no acuteness, no branch selection, no dimension
restriction is introduced by the descent.

## The printed residual

`residual_eq_comp_subtypeL` identifies the residual `R = (A + H)E₀ - E₀A₀` of
equation (1.8) with `H E₀` from invariance of `P` alone, and that argument
never sees the scalars; it is now stated over any `RCLike` field.  With
`norm_comp_subtypeL_eq_norm_comp_starProjection`, also scalar-generic, the
printed residual norm becomes `‖H P_P‖`, which complexifies term by term.  That
is `norm_residual_complexify` below, the module's only computation.

## Main results

* `theorem8_2_perturbationHalfGap_source_real`;
* `theorem8_2_residualHalfGap_source_real`;
* `theorem8_2_branch_source_directed_real` -- the printed disjunction;
* `theorem8_2_perturbationHalfGap_source_real_maximalAngle_lt` and
  `theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects` -- the
  printed `Θ < π/4`, under the finite form of (1.5) and under Section 3's
  standing assumption (3.5) respectively; the second carries no dimension
  hypothesis of any kind.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1 and
  Theorem 8.2.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section8

open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Experimental.Foundation
open TauCeti.DavisKahan.Experimental.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ### 1. The printed residual complexifies -/

/-- **The printed residual (1.8) has the same norm before and after
complexification.**

Both sides reduce to `‖H P_P‖` by `residual_eq_comp_subtypeL` and
`norm_comp_subtypeL_eq_norm_comp_starProjection`, and the complexified
projection is the complexification of the projection
(`starProjection_complexifySubmodule`), so `norm_complexify` closes it. -/
theorem norm_residual_complexify
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (hPinv : ∀ x ∈ P, A x ∈ P) :
    ‖residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
        (compressOperator (complexifySubmodule P) (complexify A))‖ =
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ := by
  classical
  have : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have : CompleteSpace (complexifySubmodule P) :=
    ((complexifySubmodule P).isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hPinvC : ∀ z ∈ complexifySubmodule P, complexify A z ∈ complexifySubmodule P :=
    fun _ hz => mapsTo_complexifySubmodule hPinv hz
  rw [residual_eq_comp_subtypeL (complexify A) (complexify K)
      (complexifySubmodule P) hPinvC,
    residual_eq_comp_subtypeL A K P hPinv,
    Krein.norm_comp_subtypeL_eq_norm_comp_starProjection,
    Krein.norm_comp_subtypeL_eq_norm_comp_starProjection,
    starProjection_complexifySubmodule, ← complexify_comp, norm_complexify]

/-! ### 2. The two printed alternatives over `ℝ` -/

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, over a REAL
Hilbert space.**

`‖H‖ < δ/2` together with the printed spectral placement of `A₀` gives the
directed quarter-angle bound `directedGap P Q < √2/2`, exactly as over `ℂ`.
Every hypothesis is the real reading of the printed one, and the proof is the
complexification transport described in this module's header; the perturbation
theory itself is not re-run. -/
theorem theorem8_2_perturbationHalfGap_source_real
    {A K : E →L[ℝ] E} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2) :
    directedGap P Q < Real.sqrt 2 / 2 := by
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  have hAc : IsSelfAdjointOperator (complexify A) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff A).2
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
  have hKc : IsSelfAdjointOperator (complexify K) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff K).2
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK))
  have hQc : Foundation.SpectrumIn (complexify A + complexify K) (complexifySubmodule Q)
      (Set.Icc beta alpha) := by
    rw [hsum]
    exact spectrumIn_complexifySubmodule Q (A + K) _ hQ
  have hQperpc : Foundation.SpectrumIn (complexify A + complexify K) (complexifySubmodule Q)ᗮ
      (gapExterior beta alpha delta) := by
    rw [hsum, ← complexifySubmodule_orthogonal Q]
    exact spectrumIn_complexifySubmodule Qᗮ (A + K) _ hQperp
  have hPredc : (complexify A).Reduces (complexifySubmodule P) :=
    (complexify_reduces_iff A P).2 hPred
  have hPc : Foundation.SpectrumIn (complexify A) (complexifySubmodule P)
      (Set.Icc (beta - delta / 2) (alpha + delta / 2)) :=
    spectrumIn_complexifySubmodule P A _ hP
  have hsmallc : ‖complexify K‖ < delta / 2 := by
    rw [norm_complexify]; exact hsmall
  have hmain := theorem8_2_perturbationHalfGap_source hAc hKc hdelta hab hQc
    hQperpc hPredc hPc hsmallc
  rwa [directedGap_complexifySubmodule] at hmain

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, over a REAL Hilbert
space.**

`‖R‖ < δ/2` for the printed residual (1.8) of equation (1.8), with the same
directed conclusion.  Krein's completion is not re-proved over `ℝ`: the residual
norm is transported by `norm_residual_complexify` and the complex alternative is
applied. -/
theorem theorem8_2_residualHalfGap_source_real
    {A K : E →L[ℝ] E} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    directedGap P Q < Real.sqrt 2 / 2 := by
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  have hAc : IsSelfAdjointOperator (complexify A) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff A).2
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
  have hKc : IsSelfAdjointOperator (complexify K) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff K).2
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK))
  have hQc : Foundation.SpectrumIn (complexify A + complexify K) (complexifySubmodule Q)
      (Set.Icc beta alpha) := by
    rw [hsum]
    exact spectrumIn_complexifySubmodule Q (A + K) _ hQ
  have hQperpc : Foundation.SpectrumIn (complexify A + complexify K) (complexifySubmodule Q)ᗮ
      (gapExterior beta alpha delta) := by
    rw [hsum, ← complexifySubmodule_orthogonal Q]
    exact spectrumIn_complexifySubmodule Qᗮ (A + K) _ hQperp
  have hPredc : (complexify A).Reduces (complexifySubmodule P) :=
    (complexify_reduces_iff A P).2 hPred
  have hPc : Foundation.SpectrumIn (complexify A) (complexifySubmodule P)
      (Set.Icc (beta - delta / 2) (alpha + delta / 2)) :=
    spectrumIn_complexifySubmodule P A _ hP
  have hRsmallc : ‖residual (complexify A + complexify K)
      (complexifySubmodule P).subtypeL
      (compressOperator (complexifySubmodule P) (complexify A))‖ < delta / 2 := by
    rw [norm_residual_complexify A K P hPred.1]
    exact hRsmall
  have hmain := theorem8_2_residualHalfGap_source hAc hKc hdelta hab hQc
    hQperpc hPredc hPc hRsmallc
  rwa [directedGap_complexifySubmodule] at hmain

/-- **Theorem 8.2's printed disjunction over a REAL Hilbert space.**  Either
printed smallness alternative gives the directed quarter-angle bound. -/
theorem theorem8_2_branch_source_directed_real
    {A K : E →L[ℝ] E} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (halt : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    directedGap P Q < Real.sqrt 2 / 2 := by
  rcases halt with hsmall | hRsmall
  · exact theorem8_2_perturbationHalfGap_source_real hA hK hdelta hab hQ hQperp
      hPred hP hsmall
  · exact theorem8_2_residualHalfGap_source_real hA hK hdelta hab hQ hQperp
      hPred hP hRsmall

/-! ### 3. The printed `Θ < π/4` over `ℝ`

Neither of the two bridges from the directed bound to the printed symmetric
conclusion needs the complexification at all: both
`subspaceGap_eq_directedGap_of_finrank_eq` -- equation (1.5) in its finite form
-- and `subspaceGap_eq_directedGap_of_crossedDefects` -- Section 3's standing
assumption (3.5) -- are `RCLike`-generic, as is
`maximalAngle_lt_pi_div_four_iff`.  So the real forms below read the printed
`Θ < π/4` off the real directed theorems above with no further transport, and
the dimension-free one carries no dimension hypothesis of any kind. -/

/-- **Davis--Kahan 1970, Theorem 8.2, printed conclusion `Θ < π/4` over a REAL
Hilbert space, under the finite form of the standing convention (1.5).**

The real counterpart of `theorem8_2_perturbationHalfGap_source_maximalAngle_lt`.
Finite dimensionality and equal rank are the printed statement's own standing
convention, exactly as over `ℂ`. -/
theorem theorem8_2_perturbationHalfGap_source_real_maximalAngle_lt
    [FiniteDimensional ℝ E]
    {A K : E →L[ℝ] E} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : Module.finrank ℝ P = Module.finrank ℝ Q)
    (hsmall : ‖K‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 := by
  have hdir := theorem8_2_perturbationHalfGap_source_real hA hK hdelta hab hQ
    hQperp hPred hP hsmall
  have hlt : subspaceGap P Q < Real.sqrt 2 / 2 := by
    rw [subspaceGap_eq_directedGap_of_finrank_eq P Q hrank]
    exact hdir
  exact (DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_iff P Q).2 hlt

/-- **Davis--Kahan 1970, Theorem 8.2, printed conclusion `Θ < π/4` over a REAL
Hilbert space, in any dimension, under Section 3's standing assumption (3.5).**

The real counterpart of `maximalAngle_lt_pi_div_four_of_crossedDefects`, applied
to Theorem 8.2's printed disjunction: either printed smallness alternative, plus
(3.5) in its constructive form, gives the printed symmetric conclusion with
**no** finite-dimensionality and **no** rank hypothesis, over `ℝ` exactly as
over `ℂ`. -/
theorem theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects
    {A K : E →L[ℝ] E} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hcross : CrossedDefectsEquivalent P Q)
    (halt : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_crossedDefects hcross
    (theorem8_2_branch_source_directed_real hA hK hdelta hab hQ hQperp hPred hP halt)

end

end Section8
end Frontier
end Experimental
end DavisKahan
end TauCeti
