/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import DavisKahan.Geometry.Polar.DirectRotation
-- supplies `spectraReflectionProduct` and `IsAcute.symm`
import DavisKahan.Geometry.Polar.DirectRotationSquare
-- supplies `reflectedSubspace` and its projection/conjugation calculus used by
-- Proposition 3.4.  This module imports only `SinTheta`/`SpectralTheory`
-- material and never touches `Frontier`, so the dependency is acyclic.
import DavisKahan.InfiniteDimensional.DoubleAngle
-- supplies the completed nonacute construction and acute characterizations used
-- to ground the Proposition 3.2 and Corollary 3.2 source statements below.  The
-- construction depends on the polar and acute machinery under `MathAhead`, which
-- itself never imports this module, so the dependency is acyclic.
import DavisKahan.Geometry.Polar.Section3Nonacute
-- supplies the forward direction of the operator-level Halmos classification
-- (`sameHalmosInvariant_of_pairEquiv`).  This module imports only Frontier/Core,
-- so the dependency is acyclic.
import DavisKahan.Geometry.Halmos.Classification
import DavisKahan.Geometry.Halmos.GenericReconstruction
import ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence
import DavisKahan.Geometry.Halmos.CompactClassification

/-!
# Section 3 frontier: separation and classification of two subspaces

These declarations state the remaining source results and the reusable
classification bridges beneath them.  The first completion target is the
constructive nonacute direct-rotation criterion.  The spectral-multiplicity
formulation is separated from the operator-level Halmos classification so the
latter can be completed without inventing direct-integral infrastructure.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section3

open TauCeti.DavisKahanExt (reflectedSubspace starProjection_reflectedSubspace)
open TauCeti.DavisKahan

universe u v

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- Davis--Kahan 1970, Proposition 3.1: in the acute case the direct rotation
is the unique unitary intertwiner whose diagonal `U`-compressions are positive.

The predicate `IsPaperDirectRotation` records the diagonal compressions only
through their numerical range (`0 ≤ re ⟪x, (P T P) x⟫`), which is strictly
weaker than operator positivity and does not pin the phase on the common part:
on `U = V` every scalar `exp (I * θ)` with `|θ| < π / 2` satisfies all five
fields yet differs from the identity direct rotation.  Uniqueness therefore
needs the diagonal compressions to be self-adjoint (equivalently genuinely
positive operators, which the canonical direct rotation satisfies because its
diagonal blocks are the positive Halmos cosine).  These two self-adjointness
hypotheses are the minimal strengthening; with them the operator squares to the
reflection product and the square-root branch is fixed by accretivity. -/
theorem proposition3_1_positivity_characterization
    (hacute : IsAcute U V) (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPaperDirectRotation U V T ↔
      T = spectraDirectRotation U V hacute := by
  constructor
  · intro hT
    -- Resolution of the identity relative to `U`.
    have hone : projection U + complementaryProjection U = 1 := by
      rw [show complementaryProjection U = 1 - projection U from
        Submodule.starProjection_orthogonal' U]
      abel
    have hRsub : reflectionOperator U = projection U - complementaryProjection U := by
      rw [reflectionOperator_eq_projection_add_projection_sub_one U,
        show complementaryProjection U = 1 - projection U from
          Submodule.starProjection_orthogonal' U]
      abel
    have hTblock : T = projection U * T * projection U
        + projection U * T * complementaryProjection U
        + complementaryProjection U * T * projection U
        + complementaryProjection U * T * complementaryProjection U := by
      calc T = (projection U + complementaryProjection U) * T
            * (projection U + complementaryProjection U) := by
              rw [hone, one_mul, mul_one]
        _ = _ := by noncomm_ring
    -- The four `U`-blocks of `star T` in terms of the blocks of `T`.
    -- Diagonal blocks are self-adjoint; off-diagonal blocks are sign-flipped.
    have e11 : projection U * star T * projection U
        = projection U * T * projection U := by
      have h := hsource_sa.star_eq
      rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
        ← mul_assoc] at h
      exact h
    have e22 : complementaryProjection U * star T * complementaryProjection U
        = complementaryProjection U * T * complementaryProjection U := by
      have h := hcomplement_sa.star_eq
      rw [star_mul, star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq,
        ← mul_assoc] at h
      exact h
    have e12 : projection U * star T * complementaryProjection U
        = -(projection U * T * complementaryProjection U) := by
      have h := congrArg star hT.crossed_blocks
      rw [star_neg, star_star, star_mul, star_mul,
        (isSelfAdjoint_starProjection U).star_eq,
        (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
      exact h
    have e21 : complementaryProjection U * star T * projection U
        = -(complementaryProjection U * T * projection U) := by
      have h := hT.crossed_blocks
      rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
        (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
      rw [h, neg_neg]
    -- `R_U (star T) R_U = T`: block-diagonal blocks fixed, off-diagonal negated.
    have hkey : reflectionOperator U * star T * reflectionOperator U = T := by
      rw [hRsub]
      have expand : (projection U - complementaryProjection U) * star T
          * (projection U - complementaryProjection U)
          = projection U * star T * projection U
            - projection U * star T * complementaryProjection U
            - complementaryProjection U * star T * projection U
            + complementaryProjection U * star T * complementaryProjection U := by
        noncomm_ring
      rw [expand, e11, e12, e21, e22]
      conv_rhs => rw [hTblock]
      abel
    -- Reflection intertwining and the resulting square identity.
    have hTR : T * reflectionOperator U = reflectionOperator V * T := by
      rw [reflectionOperator_eq_projection_add_projection_sub_one U,
        reflectionOperator_eq_projection_add_projection_sub_one V,
        mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul, hintertwines]
    have hRV : reflectionOperator V = T * reflectionOperator U * star T := by
      have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunitary
      calc reflectionOperator V
          = reflectionOperator V * (T * star T) := by rw [hTsT, mul_one]
        _ = reflectionOperator V * T * star T := by rw [mul_assoc]
        _ = T * reflectionOperator U * star T := by rw [← hTR]
    have hsq : T * T = spectraReflectionProduct U V := by
      have hexp : spectraReflectionProduct U V
          = T * (reflectionOperator U * star T * reflectionOperator U) := by
        show reflectionOperator V * reflectionOperator U = _
        rw [hRV]; noncomm_ring
      rw [hexp, hkey]
    -- Accretivity fixes the square-root branch.
    have hre : ∀ x, 0 ≤ Complex.re ⟪T x, x⟫_ℂ := by
      intro x
      have h := MathAhead.HiddenFoundations.re_inner_paperDirectRotation_nonneg U V T hT x
      rwa [← inner_re_symm (𝕜 := ℂ) (T x) x, RCLike.re_eq_complex_re] at h
    exact spectraDirectRotation_unique_of_sq U V hacute T hunitary hsq hre
  · rintro rfl
    exact MathAhead.Section3.spectraDirectRotation_isPaperDirectRotation U V hacute

omit [CompleteSpace H] [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection] in
/-- The paper's crossed intersections are exactly the Halmos source and target
defect spaces. -/
theorem crossed_intersections_are_halmos_defects :
    halmosSourceDefect U V = U ⊓ Vᗮ ∧
      halmosTargetDefect U V = Uᗮ ⊓ V :=
  ⟨rfl, rfl⟩

/-- Davis--Kahan 1970, Proposition 3.2: a nonacute direct rotation exists
exactly when the crossed defect spaces have equal Hilbert dimension, expressed
constructively by a linear isometric equivalence. -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent :
    (∃ T : H →L[ℂ] H, IsPaperDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V :=
  MathAhead.HiddenFoundations.proposition3_2_completed U V

/-- Explicit parameterization of the freedom in Proposition 3.2.  Distinct
unitaries between the crossed defect spaces must produce distinct direct
rotations. -/
theorem proposition3_2_parameterized_nonuniqueness
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) →
          (H →L[ℂ] H),
      (∀ J, IsPaperDirectRotation U V (build J)) ∧
      Function.Injective build :=
  MathAhead.HiddenFoundations.proposition3_2_parameterization_completed U V hdefect

/-- A unitary principal square root of the reflection product. -/
structure IsPrincipalUnitarySquareRoot
    (A T : H →L[ℂ] H) : Prop where
  unitary_mem : T ∈ unitary (H →L[ℂ] H)
  square_eq : T * T = A
  spectrum_right_half_plane :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re

open scoped ComplexOrder in
/-- Davis--Kahan 1970, Proposition 3.3, converse direction.  The crossed
intersection mapping condition selects the correct square root on the
minus-one spectral subspace. -/
theorem proposition3_3_principalSquareRoot_converse
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot
      (spectraReflectionProduct U V) T)
    (hcross : T '' (halmosSourceDefect U V : Set H) =
      (halmosTargetDefect U V : Set H)) :
    IsPaperDirectRotation U V T := by
  set A := spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) with hAdef
  have hunit := hroot.unitary_mem
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunit
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hunit
  haveI hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunit
  -- (1) accretive: 0 ≤ T + star T
  have hTpos : (0 : H →L[ℂ] H) ≤ T + star T := by
    have e2 : cfc (fun z : ℂ => star z) T = star T := by
      rw [cfc_star (R := ℂ) (fun z : ℂ => z) T, cfc_id' ℂ T]
    have e3 : T + star T = cfc (fun z : ℂ => z + star z) T := by
      rw [cfc_add (R := ℂ) T (fun z : ℂ => z) (fun z : ℂ => star z)
        continuous_id.continuousOn continuous_star.continuousOn, cfc_id' ℂ T, e2]
    rw [e3]
    apply cfc_nonneg
    intro z hz
    have hre : 0 ≤ z.re := hroot.spectrum_right_half_plane z hz
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.zero_re, Complex.add_re, Complex.star_def, Complex.conj_re]
      linarith
    · simp only [Complex.zero_im, Complex.add_im, Complex.star_def, Complex.conj_im]
      ring
  -- accretive quadratic form
  have haccr : ∀ y : H, 0 ≤ RCLike.re ⟪T y, y⟫_ℂ := by
    intro y
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive (T + star T)).mp hTpos
    have hy := hp.re_inner_nonneg_left y
    rw [add_apply, inner_add_left, map_add] at hy
    have hstar : RCLike.re ⟪star T y, y⟫_ℂ = RCLike.re ⟪T y, y⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      exact inner_re_symm (𝕜 := ℂ) y (T y)
    rw [hstar] at hy
    linarith
  -- (2) T + star T = A + A
  have hkey : T + star T = A + A := by
    have hsqeq : (T + star T) * (T + star T) = (A + A) * (A + A) := by
      have expand : (T + star T) * (T + star T)
          = T * T + T * star T + star T * T + star T * star T := by noncomm_ring
      have hstarTT : star T * star T = star (spectraReflectionProduct U V) := by
        rw [← star_mul, hroot.square_eq]
      have expandR : (A + A) * (A + A) = A * A + A * A + A * A + A * A := by noncomm_ring
      have hAA : A * A = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V :=
        spectraOperatorAbsoluteValue_mul_self _
      rw [expand, hroot.square_eq, hTsT, hsTT, hstarTT, expandR, hAA]
      have hG : spectraReflectionProduct U V + 1 =
          spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
        rw [add_comm]
        exact (spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V).symm
      have hstarG : star (spectraReflectionProduct U V) + 1 =
          star (spectraCanonicalIntertwiner U V) + star (spectraCanonicalIntertwiner U V) := by
        have h := congrArg star hG
        rwa [star_add, star_add, star_one] at h
      have hSS : spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V)
          = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V :=
        spectraCanonicalIntertwiner_add_star U V
      calc spectraReflectionProduct U V + 1 + 1 + star (spectraReflectionProduct U V)
          = (spectraReflectionProduct U V + 1) + (star (spectraReflectionProduct U V) + 1) := by
            abel
        _ = (spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V)
              + (star (spectraCanonicalIntertwiner U V) + star (spectraCanonicalIntertwiner U V)) := by
            rw [hG, hstarG]
        _ = (spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V))
              + (spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V)) := by
            abel
        _ = (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V)
            + (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V) := by
            rw [hSS]
        _ = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V := by
            abel
    have h2A_nonneg : (0 : H →L[ℂ] H) ≤ A + A :=
      add_nonneg (spectraOperatorAbsoluteValue_nonneg _) (spectraOperatorAbsoluteValue_nonneg _)
    calc T + star T
        = CFC.sqrt ((T + star T) * (T + star T)) := (CFC.sqrt_unique rfl hTpos).symm
      _ = CFC.sqrt ((A + A) * (A + A)) := by rw [hsqeq]
      _ = A + A := CFC.sqrt_unique rfl h2A_nonneg
  -- (3) T * A = S
  have hTA : T * A = spectraCanonicalIntertwiner U V := by
    have h1 : T * (T + star T) = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
      rw [mul_add, hroot.square_eq, hTsT,
        spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V]
      abel
    rw [hkey, mul_add] at h1
    -- h1 : T * A + T * A = S + S
    have hh : (2 : ℂ) • (T * A) = (2 : ℂ) • spectraCanonicalIntertwiner U V := by
      rw [two_smul, two_smul]; exact h1
    exact smul_right_injective (H →L[ℂ] H) (two_ne_zero) hh
  -- crossed_blocks and compressions and intertwines
  have hAP : A * projection U = projection U * A :=
    (spectraCanonicalAbsoluteValue_commute_projection U V).eq
  -- hXA
  have hXA : (T * projection U - projection V * T) * A = 0 := by
    have step : T * projection U * A = projection V * T * A := by
      calc T * projection U * A
          = T * (projection U * A) := by rw [mul_assoc]
        _ = T * (A * projection U) := by rw [← hAP]
        _ = (T * A) * projection U := by rw [mul_assoc]
        _ = spectraCanonicalIntertwiner U V * projection U := by rw [hTA]
        _ = projection V * spectraCanonicalIntertwiner U V :=
            spectraCanonicalIntertwiner_mul_projection U V
        _ = projection V * (T * A) := by rw [hTA]
        _ = projection V * T * A := by rw [mul_assoc]
    rw [sub_mul, step, sub_self]
  -- G = -1 on source defect
  have hGneg : ∀ z, z ∈ halmosSourceDefect U V → spectraReflectionProduct U V z = -z := by
    intro z hz
    obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosSourceDefect hz
    have hRU : reflectionOperator U z = z := by
      rw [Submodule.reflectionOperator_apply, hPz]; module
    rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply, hQz]
    module
  -- X vanishes on ker A
  have hXker : ∀ x : H, A x = 0 → (T * projection U - projection V * T) x = 0 := by
    intro x hx
    have hSx : spectraCanonicalIntertwiner U V x = 0 := by
      have hn : ‖spectraCanonicalIntertwiner U V x‖ = 0 := by
        rw [← norm_spectraOperatorAbsoluteValue_apply (spectraCanonicalIntertwiner U V) x, ← hAdef,
          hx, norm_zero]
      exact norm_eq_zero.mp hn
    have hSexpand : spectraCanonicalIntertwiner U V x =
        projection V (projection U x) + complementaryProjection V (complementaryProjection U x) := by
      show (projection V * projection U + complementaryProjection V * complementaryProjection U) x = _
      simp only [add_apply, mul_apply_eq_comp]
    rw [hSexpand] at hSx
    have hmemV : projection V (projection U x) ∈ V := V.starProjection_apply_mem _
    have hmemVc : complementaryProjection V (complementaryProjection U x) ∈ Vᗮ :=
      Vᗮ.starProjection_apply_mem _
    have hab_inner : ⟪projection V (projection U x),
        complementaryProjection V (complementaryProjection U x)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmemV hmemVc
    have hQPx : projection V (projection U x) = 0 := by
      have hself : ⟪projection V (projection U x), projection V (projection U x)⟫_ℂ = 0 := by
        calc ⟪projection V (projection U x), projection V (projection U x)⟫_ℂ
            = ⟪projection V (projection U x),
                projection V (projection U x)
                  + complementaryProjection V (complementaryProjection U x)⟫_ℂ
              - ⟪projection V (projection U x),
                complementaryProjection V (complementaryProjection U x)⟫_ℂ := by
              rw [inner_add_right]; ring
          _ = 0 := by rw [hSx, hab_inner, inner_zero_right]; ring
      exact inner_self_eq_zero.mp hself
    have hPxsource : projection U x ∈ halmosSourceDefect U V := by
      refine Submodule.mem_inf.mpr ⟨U.starProjection_apply_mem x, ?_⟩
      exact (Submodule.starProjection_apply_eq_zero_iff V).mp hQPx
    have hQcPcx : complementaryProjection V (complementaryProjection U x) = 0 := by
      have := hSx
      rw [hQPx, zero_add] at this
      exact this
    have hPcxtarget : complementaryProjection U x ∈ halmosTargetDefect U V := by
      refine Submodule.mem_inf.mpr ⟨Uᗮ.starProjection_apply_mem x, ?_⟩
      have := (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hQcPcx
      simpa using this
    -- x = Px + Pᗮx
    have hxsplit : projection U x + complementaryProjection U x = x :=
      U.starProjection_add_starProjection_orthogonal x
    -- T (Px) ∈ target defect ⊆ V
    have hTPx_mem : T (projection U x) ∈ halmosTargetDefect U V := by
      have : T (projection U x) ∈ (halmosTargetDefect U V : Set H) := by
        rw [← hcross]
        exact Set.mem_image_of_mem T hPxsource
      exact this
    have hQTPx : projection V (T (projection U x)) = T (projection U x) :=
      V.starProjection_eq_self_iff.mpr (mem_halmosTargetDefect.mp hTPx_mem).2
    -- T (Pᗮx) ∈ source defect ⊆ Vᗮ
    have hTPcx_mem : T (complementaryProjection U x) ∈ halmosSourceDefect U V := by
      have hmem : complementaryProjection U x ∈ (halmosTargetDefect U V : Set H) := hPcxtarget
      rw [← hcross] at hmem
      obtain ⟨z, hzsource, hzeq⟩ := hmem
      have hTz : T (T z) = spectraReflectionProduct U V z := by
        have := congrArg (fun f : H →L[ℂ] H => f z) hroot.square_eq
        simpa [mul_apply_eq_comp] using this
      have : T (complementaryProjection U x) = -z := by
        rw [← hzeq, hTz, hGneg z hzsource]
      rw [this]
      exact Submodule.neg_mem _ hzsource
    have hQTPcx : projection V (T (complementaryProjection U x)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).mpr
      exact (mem_halmosSourceDefect.mp hTPcx_mem).2
    -- assemble
    have hTx : T x = T (projection U x) + T (complementaryProjection U x) := by
      rw [← map_add, hxsplit]
    show (T * projection U - projection V * T) x = 0
    rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      hTx, map_add, hQTPx, hQTPcx, add_zero, sub_self]
  -- final intertwining: X = 0
  have hXeq : T * projection U = projection V * T := by
    haveI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
    haveI : A.ker.HasOrthogonalProjection := inferInstance
    have hrangeLe : A.range ≤ (T * projection U - projection V * T).ker := by
      rintro y ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      have := congrArg (fun f : H →L[ℂ] H => f z) hXA
      simpa [mul_apply_eq_comp] using this
    have hself : ContinuousLinearMap.adjoint A = A := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (spectraOperatorAbsoluteValue_isSelfAdjoint _).star_eq
    have horthEq : A.kerᗮ = A.range.topologicalClosure := by
      have h1 : A.rangeᗮ = A.ker := by rw [A.orthogonal_range, hself]
      calc A.kerᗮ = A.rangeᗮᗮ := by rw [h1]
        _ = A.range.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure _
    have hOrthLe : A.kerᗮ ≤ (T * projection U - projection V * T).ker := by
      rw [horthEq]
      exact Submodule.topologicalClosure_minimal _ hrangeLe
        (T * projection U - projection V * T).isClosed_ker
    have hsub : ∀ x : H, (T * projection U - projection V * T) x = 0 := by
      intro x
      have hsplit := A.ker.starProjection_add_starProjection_orthogonal x
      rw [← hsplit, map_add]
      have h1 : (T * projection U - projection V * T) (A.ker.starProjection x) = 0 := by
        apply hXker
        exact LinearMap.mem_ker.mp (A.ker.starProjection_apply_mem x)
      have h2 : (T * projection U - projection V * T) (A.kerᗮ.starProjection x) = 0 :=
        LinearMap.mem_ker.mp (hOrthLe (A.kerᗮ.starProjection_apply_mem x))
      rw [h1, h2, add_zero]
    have hzero : T * projection U - projection V * T = 0 := ContinuousLinearMap.ext hsub
    exact sub_eq_zero.mp hzero
  -- crossed_blocks
  refine
    { unitary_mem := hunit
      intertwines := hXeq
      source_compression_nonnegative := ?_
      complement_compression_nonnegative := ?_
      crossed_blocks := ?_ }
  · intro x
    have h := haccr (projection U x)
    have hPTP : (projection U * T * projection U) x = projection U (T (projection U x)) := by
      simp only [mul_apply_eq_comp]
    have hsymm : ⟪projection U x, T (projection U x)⟫_ℂ
        = ⟪x, projection U (T (projection U x))⟫_ℂ :=
      U.starProjection_isSymmetric x (T (projection U x))
    have heq : RCLike.re ⟪x, (projection U * T * projection U) x⟫_ℂ
        = RCLike.re ⟪T (projection U x), projection U x⟫_ℂ := by
      rw [hPTP, ← hsymm]
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [heq]; exact h
  · intro x
    have h := haccr (complementaryProjection U x)
    have hPTP : (complementaryProjection U * T * complementaryProjection U) x
        = complementaryProjection U (T (complementaryProjection U x)) := by
      simp only [mul_apply_eq_comp]
    have hsymm : ⟪complementaryProjection U x, T (complementaryProjection U x)⟫_ℂ
        = ⟪x, complementaryProjection U (T (complementaryProjection U x))⟫_ℂ :=
      Uᗮ.starProjection_isSymmetric x (T (complementaryProjection U x))
    have heq : RCLike.re ⟪x, (complementaryProjection U * T * complementaryProjection U) x⟫_ℂ
        = RCLike.re ⟪T (complementaryProjection U x), complementaryProjection U x⟫_ℂ := by
      rw [hPTP, ← hsymm]
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [heq]; exact h
  · have hcomm : Commute (T + star T) (projection U) := by
      rw [hkey]
      exact (spectraCanonicalAbsoluteValue_commute_projection U V).add_left
        (spectraCanonicalAbsoluteValue_commute_projection U V)
    have hblock : complementaryProjection U * (T + star T) * projection U = 0 := by
      calc complementaryProjection U * (T + star T) * projection U
          = complementaryProjection U * ((T + star T) * projection U) := by rw [mul_assoc]
        _ = complementaryProjection U * (projection U * (T + star T)) := by rw [hcomm.eq]
        _ = (complementaryProjection U * projection U) * (T + star T) := by rw [mul_assoc]
        _ = 0 := by rw [complementaryProjection_mul_projection U, zero_mul]
    have hstar : star (projection U * T * complementaryProjection U)
        = complementaryProjection U * star T * projection U := by
      rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
        (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc]
    rw [hstar]
    have hsum : complementaryProjection U * T * projection U
        + complementaryProjection U * star T * projection U = 0 := by
      have h := hblock
      rw [mul_add, add_mul] at h
      exact h
    exact eq_neg_of_add_eq_zero_left hsum

/-- Reflection through the mirror image `reflectedSubspace V U` is the
conjugate of the reflection through `U` by the reflection through `V`.
Since the mirror image has projection `R_V P_U R_V`, its reflection
`2 P - 1` equals `R_V (2 P_U - 1) R_V = R_V R_U R_V`. -/
theorem reflectionOperator_reflectedSubspace :
    reflectionOperator (reflectedSubspace V U)
      = reflectionOperator V * reflectionOperator U * reflectionOperator V := by
  have hRR : reflectionOperator V * reflectionOperator V = 1 :=
    reflectionOperator_mul_self_complex V
  have hPVref : projection (reflectedSubspace V U)
      = reflectionOperator V * projection U * reflectionOperator V :=
    starProjection_reflectedSubspace V U
  rw [reflectionOperator_eq_projection_add_projection_sub_one (reflectedSubspace V U),
      reflectionOperator_eq_projection_add_projection_sub_one U, hPVref]
  have expand : reflectionOperator V * (projection U + projection U - 1)
      * reflectionOperator V
      = reflectionOperator V * projection U * reflectionOperator V
        + reflectionOperator V * projection U * reflectionOperator V
        - reflectionOperator V * reflectionOperator V := by noncomm_ring
  rw [expand, hRR]

/-- The canonical intertwiner and the Halmos cosine square carry the same
numerical real part.  The Hermitian part of `S` is `S⋆ S = |S| ^ 2`, which is
exactly `halmosCosineSq U V`, so `re ⟪S x, x⟫ = re ⟪halmosCosineSq x, x⟫`. -/
theorem re_inner_intertwiner_eq_cosineSq (x : H) :
    RCLike.re ⟪spectraCanonicalIntertwiner U V x, x⟫_ℂ
      = RCLike.re ⟪halmosCosineSq U V x, x⟫_ℂ := by
  have hSstar : spectraCanonicalIntertwiner U V
        + star (spectraCanonicalIntertwiner U V)
      = halmosCosineSq U V + halmosCosineSq U V := by
    rw [spectraCanonicalIntertwiner_add_star U V,
      ← spectraOperatorAbsoluteValue_mul_self,
      spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq]
  have h := congrArg (fun T : H →L[ℂ] H => RCLike.re ⟪T x, x⟫_ℂ) hSstar
  have hstar : RCLike.re ⟪star (spectraCanonicalIntertwiner U V) x, x⟫_ℂ
      = RCLike.re ⟪spectraCanonicalIntertwiner U V x, x⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
    exact inner_re_symm x (spectraCanonicalIntertwiner U V x)
  simp only [add_apply, inner_add_left, map_add, hstar] at h
  linarith

/-- Under the corrected half-angle bound (cosine *square* at least `1/2`), the
ordered reflection product `R_V R_U` is accretive.  Using `2 S = 1 + R_V R_U`
one has `re ⟪(R_V R_U) x, x⟫ = 2 * re ⟪halmosCosineSq x, x⟫ - ‖x‖ ^ 2`, which is
nonnegative precisely when `re ⟪halmosCosineSq x, x⟫ ≥ ‖x‖ ^ 2 / 2`. -/
theorem re_inner_reflectionProduct_nonneg
    (hhalf : ∀ x : H,
      0 ≤ RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2)
    (x : H) :
    0 ≤ RCLike.re ⟪spectraReflectionProduct U V x, x⟫_ℂ := by
  have hG : spectraReflectionProduct U V
      = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V - 1 := by
    have h1 : spectraReflectionProduct U V + 1
        = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
      rw [add_comm]
      exact (spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V).symm
    exact eq_sub_of_add_eq h1
  have hcos : RCLike.re ⟪spectraCanonicalIntertwiner U V x, x⟫_ℂ
      = RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ := by
    rw [re_inner_intertwiner_eq_cosineSq U V x]
    exact (inner_re_symm _ _).symm
  have hself : RCLike.re ⟪x, x⟫_ℂ = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq]
  rw [hG]
  simp only [sub_apply, add_apply,
    one_apply_eq_self, inner_sub_left, inner_add_left, map_sub, map_add,
    hself, hcos]
  have := hhalf x
  linarith

/-- Davis--Kahan 1970, Proposition 3.4 in source form: the square of the direct
rotation is the direct rotation between the reflected source and target
subspaces.  The natural reflected pair is `Uref = U`, `Vref = reflectedSubspace
V U`, for which `spectraDirectRotation U V hacute` squared is the ordered
reflection product `R_V R_U = spectraReflectionProduct U V` (see
`spectraDirectRotation_sq`).  Because `reflectionOperator (reflectedSubspace V U)
= R_V R_U R_V`, the reflection product of the reflected pair is `(R_V R_U) ^ 2`,
so `R_V R_U` is a unitary square root of it; the accretive branch is the direct
rotation between the reflected subspaces.

Two hypothesis corrections are recorded here relative to the originally printed
statement.  First, the half-angle threshold is on the cosine *square*,
`re ⟪halmosCosineSq x, x⟫ ≥ ‖x‖ ^ 2 / 2` (cosine `≥ 1 / √2`, double angle
`≤ π / 2`); it is *not* the pointwise bound `re ⟪|S| x, x⟫ ≥ ‖x‖ ^ 2 / 2`, which
is strictly weaker since `|S| ≤ 1`.  The algebra `2 S = 1 + R_V R_U` together
with the normality identity `Re S = S⋆ S = |S| ^ 2 = halmosCosineSq` shows this
cosine-square bound is exactly accretivity of `R_V R_U`
(`re_inner_reflectionProduct_nonneg`), which is the branch condition needed to
identify the square root with the direct rotation.

Second, acuteness of the reflected pair `IsAcute U (reflectedSubspace V U)` is
carried as an *independent* hypothesis.  It is genuinely not derivable from the
cosine-square bound and is not implied by it: a boundary cosine square of `1/2`
makes the double angle exactly `π / 2`, so the reflected pair has gap `1` and is
not acute, while the cosine-square bound still holds nonstrictly.  Conversely
acuteness of the reflected pair alone does not force accretivity of `R_V R_U`:
a pair carrying a single principal angle in `(π/4, π/2)` has an acute reflected
pair (double angle folded below `π/2`) yet a reflection product with strictly
negative numerical real part on the corresponding vectors, so the conclusion
fails without the cosine-square bound.  Both conditions are therefore necessary;
a single uniform spectral-gap field on `R_V R_U` would subsume them, but the
present two-hypothesis form is the faithful minimal correction. -/
theorem proposition3_4_square_is_reflected_directRotation
    (hacute : IsAcute U V)
    (hacuteReflected : IsAcute U (reflectedSubspace V U))
    (hhalf : ∀ x : H,
      0 ≤ RCLike.re
        ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2) :
    -- the reflected pair is existentially quantified, so its orthogonal
    -- projections cannot be found by instance search; they are bound here and
    -- reinstated with `haveI` inside the body
    ∃ (Uref Vref : Submodule ℂ H) (iU : Uref.HasOrthogonalProjection)
        (iV : Vref.HasOrthogonalProjection),
      haveI : Uref.HasOrthogonalProjection := iU
      haveI : Vref.HasOrthogonalProjection := iV
      ∃ hacuteRef : IsAcute Uref Vref,
        spectraDirectRotation U V hacute *
            spectraDirectRotation U V hacute =
          spectraDirectRotation Uref Vref hacuteRef := by
  refine ⟨U, reflectedSubspace V U, inferInstance, inferInstance, hacuteReflected, ?_⟩
  have hWsq : spectraDirectRotation U V hacute * spectraDirectRotation U V hacute
      = spectraReflectionProduct U V := spectraDirectRotation_sq U V hacute
  rw [hWsq]
  have hGunit : spectraReflectionProduct U V ∈ unitary (H →L[ℂ] H) :=
    spectraReflectionProduct_mem_unitary U V
  have hGsq : spectraReflectionProduct U V * spectraReflectionProduct U V
      = spectraReflectionProduct U (reflectedSubspace V U) := by
    show spectraReflectionProduct U V * spectraReflectionProduct U V
      = reflectionOperator (reflectedSubspace V U) * reflectionOperator U
    rw [reflectionOperator_reflectedSubspace U V]
    show (reflectionOperator V * reflectionOperator U)
        * (reflectionOperator V * reflectionOperator U)
      = reflectionOperator V * reflectionOperator U * reflectionOperator V
        * reflectionOperator U
    noncomm_ring
  have hGre : ∀ x, 0 ≤ Complex.re ⟪spectraReflectionProduct U V x, x⟫_ℂ :=
    re_inner_reflectionProduct_nonneg U V hhalf
  exact spectraDirectRotation_unique_of_sq U (reflectedSubspace V U) hacuteReflected
    (spectraReflectionProduct U V) hGunit hGsq hGre

/-- A subspace on which both projections reduce and every nonzero vector makes
the fixed angle with the opposite subspace.

Correction relative to the originally printed predicate.  The printed version
constrained only the source (`M ∩ U`) and target (`M ∩ V`) vectors.  That is
insufficient for the maximality half of Proposition 3.5: a nonzero vector in the
exterior `Uᗮ ⊓ Vᗮ` (which is compatible with acuteness) spans a subspace that
reduces both projections and meets the source and target conditions vacuously,
yet on it the cosine square is `1`, not `c ^ 2`.  So for `c < 1` the printed
predicate admits subspaces that are not contained in the fixed-cosine
eigenspace.  The paper's phrasing — *all nonzero vectors make the fixed angle
with the opposite subspace* — is captured by adding the two complement
conditions on `M ∩ Uᗮ` and `M ∩ Vᗮ`, which is exactly what excludes the
exterior and makes the eigenspace maximal. -/
def IsFixedCosineReducingSubspace
    (M : Submodule ℂ H) (c : ℝ) : Prop :=
  (projection U).Reduces M ∧
  (projection V).Reduces M ∧
  (∀ x : H, x ∈ M → x ∈ U → ‖projection V x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ V → ‖projection U x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ Uᗮ → ‖complementaryProjection V x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ Vᗮ → ‖complementaryProjection U x‖ = c * ‖x‖)

/-- Polarization on a reducing subspace: a bounded operator that preserves a
subspace and has vanishing quadratic form there vanishes on it. -/
theorem eigen_of_reducing_quadratic {T : H →L[ℂ] H} {W : Submodule ℂ H}
    (hTW : ∀ w ∈ W, T w ∈ W) (hquad : ∀ w ∈ W, ⟪T w, w⟫_ℂ = 0)
    {w : H} (hw : w ∈ W) : T w = 0 := by
  have key : ∀ v ∈ W, ⟪T w, v⟫_ℂ = 0 := by
    intro v hv
    have hqw := hquad w hw
    have hqv := hquad v hv
    have h1 := hquad (w + v) (W.add_mem hw hv)
    have hi := hquad (w + (Complex.I • v)) (W.add_mem hw (W.smul_mem _ hv))
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hqw, hqv, Complex.conj_I,
      mul_zero, add_zero, zero_add] at h1 hi
    have hab : ⟪T w, v⟫_ℂ - ⟪T v, w⟫_ℂ = 0 := by
      have hI : Complex.I * (⟪T w, v⟫_ℂ - ⟪T v, w⟫_ℂ) = 0 := by linear_combination hi
      exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
    have h2a : (2 : ℂ) * ⟪T w, v⟫_ℂ = 0 := by linear_combination h1 + hab
    exact (mul_eq_zero.mp h2a).resolve_left (by norm_num)
  exact inner_self_eq_zero.mp (key (T w) (hTW w hw))

/-- The Halmos cosine square is symmetric in the ordered pair: it is
`1 - (P_U - P_V) ^ 2`, invariant under swapping the projections. -/
theorem halmosCosineSq_symm :
    halmosCosineSq U V = halmosCosineSq V U := by
  rw [halmosCosineSq_eq_one_sub_projection_sub_sq U V,
    halmosCosineSq_eq_one_sub_projection_sub_sq V U]
  noncomm_ring

/-- Squared-norm quadratic form, with the real-to-complex coercion pinned to
`Complex.ofReal`. -/
theorem inner_self_ofReal (x : H) : ⟪x, x⟫_ℂ = (‖x‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K x

/-- The quadratic form of an orthogonal projection is its squared norm. -/
theorem inner_starProjection_self_eq (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (y : H) :
    ⟪K.starProjection y, y⟫_ℂ = (‖K.starProjection y‖ : ℂ) ^ 2 := by
  have hidem : K.starProjection (K.starProjection y) = K.starProjection y :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem y)
  calc ⟪K.starProjection y, y⟫_ℂ
      = ⟪K.starProjection (K.starProjection y), y⟫_ℂ := by rw [hidem]
    _ = ⟪K.starProjection y, K.starProjection y⟫_ℂ := K.starProjection_isSymmetric _ _
    _ = (‖K.starProjection y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _

/-- On the source subspace, the cosine-square quadratic form is `‖P_V x‖ ^ 2`. -/
theorem inner_halmosCosineSq_source (x : H) (hx : x ∈ U) :
    ⟪halmosCosineSq U V x, x⟫_ℂ = (‖projection V x‖ : ℂ) ^ 2 := by
  have hPU : projection U x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hPUc : complementaryProjection U x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[ℂ] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show complementaryProjection U x = Uᗮ.starProjection x from rfl, hx', hPU, sub_self]
  have hval : halmosCosineSq U V x = projection U (projection V x) := by
    show (projection U * projection V * projection U
      + complementaryProjection U * complementaryProjection V
        * complementaryProjection U) x = _
    simp only [add_apply, mul_apply_eq_comp, hPU,
      hPUc, map_zero, add_zero]
  rw [hval]
  calc ⟪projection U (projection V x), x⟫_ℂ
      = ⟪projection V x, projection U x⟫_ℂ := U.starProjection_isSymmetric _ _
    _ = ⟪projection V x, x⟫_ℂ := by rw [hPU]
    _ = (‖projection V x‖ : ℂ) ^ 2 := inner_starProjection_self_eq V x

/-- On the source complement, the cosine-square quadratic form is
`‖Pᗮ_V x‖ ^ 2`. -/
theorem inner_halmosCosineSq_source_compl (x : H) (hx : x ∈ Uᗮ) :
    ⟪halmosCosineSq U V x, x⟫_ℂ = (‖complementaryProjection V x‖ : ℂ) ^ 2 := by
  have hPUc : complementaryProjection U x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hPU : projection U x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[ℂ] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show complementaryProjection U x = Uᗮ.starProjection x from rfl] at hPUc
    have hUeq : U.starProjection x = x - Uᗮ.starProjection x := by rw [hx']; abel
    rw [show projection U x = U.starProjection x from rfl, hUeq, hPUc, sub_self]
  have hval : halmosCosineSq U V x
      = complementaryProjection U (complementaryProjection V x) := by
    show (projection U * projection V * projection U
      + complementaryProjection U * complementaryProjection V
        * complementaryProjection U) x = _
    simp only [add_apply, mul_apply_eq_comp, hPU,
      hPUc, map_zero, zero_add]
  rw [hval]
  calc ⟪complementaryProjection U (complementaryProjection V x), x⟫_ℂ
      = ⟪complementaryProjection V x, complementaryProjection U x⟫_ℂ :=
        Uᗮ.starProjection_isSymmetric _ _
    _ = ⟪complementaryProjection V x, x⟫_ℂ := by rw [hPUc]
    _ = (‖complementaryProjection V x‖ : ℂ) ^ 2 := inner_starProjection_self_eq Vᗮ x

/-- The fixed-cosine subspace: the `c ^ 2`-eigenspace of the Halmos cosine
square `cos²Θ`.  For a singleton this eigenspace coincides with the
`{c ^ 2}`-spectral subspace, but presenting it as `ker (cos²Θ - c ^ 2)` makes
the fixed-cosine eigenvalue equation available definitionally, so no
projection-valued-measure eigenvalue extraction is needed downstream. -/
noncomputable def fixedCosineSubspace (c : ℝ) : Submodule ℂ H :=
  (halmosCosineSq U V - (c : ℂ) ^ 2 • (1 : H →L[ℂ] H)).ker

/-- Membership in the fixed-cosine subspace is the eigenvalue equation. -/
theorem mem_fixedCosineSubspace (c : ℝ) (w : H) :
    w ∈ fixedCosineSubspace U V c ↔ halmosCosineSq U V w = (c : ℂ) ^ 2 • w := by
  rw [fixedCosineSubspace, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, one_apply_eq_self]
  rw [sub_eq_zero]

/-- A projection commuting with the cosine square reduces the eigenspace. -/
theorem reduces_projection_of_commute (c : ℝ) (W : Submodule ℂ H)
    [W.HasOrthogonalProjection]
    (hcomm : Commute (halmosCosineSq U V) (projection W)) :
    (projection W).Reduces (fixedCosineSubspace U V c) := by
  refine reduces_orthogonalComplement W.starProjection_isSymmetric ?_
  intro x hx
  rw [mem_fixedCosineSubspace] at hx ⊢
  have hcm := congrArg (fun T : H →L[ℂ] H => T x) hcomm.eq
  simp only [mul_apply_eq_comp] at hcm
  rw [hcm, hx, map_smul]

/-- Extract a real norm equality from a complex squared identity. -/
theorem norm_eq_from_ofReal_sq {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (h : (p : ℂ) ^ 2 = (c : ℂ) ^ 2 * (q : ℂ) ^ 2) : p = c * q := by
  have hr : p ^ 2 = (c * q) ^ 2 := by
    have hcast : ((p ^ 2 : ℝ) : ℂ) = (((c * q) ^ 2 : ℝ) : ℂ) := by
      push_cast; linear_combination h
    exact_mod_cast hcast
  have hcq : 0 ≤ c * q := mul_nonneg hc hq
  calc p = Real.sqrt (p ^ 2) := (Real.sqrt_sq hp).symm
    _ = Real.sqrt ((c * q) ^ 2) := by rw [hr]
    _ = c * q := Real.sqrt_sq hcq

/-- The cosine square commutes with the target projection too. -/
theorem halmosCosineSq_commute_projection_right :
    Commute (halmosCosineSq U V) (projection V) := by
  rw [halmosCosineSq_symm U V]
  exact halmosCosineSq_commute_projection V U

/-- Vector form of the cosine square on the source subspace. -/
theorem halmosCosineSq_source_apply (x : H) (hx : x ∈ U) :
    halmosCosineSq U V x = projection U (projection V x) := by
  have hPU : projection U x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hPUc : complementaryProjection U x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[ℂ] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show complementaryProjection U x = Uᗮ.starProjection x from rfl, hx', hPU, sub_self]
  show (projection U * projection V * projection U
    + complementaryProjection U * complementaryProjection V
      * complementaryProjection U) x = _
  simp only [add_apply, mul_apply_eq_comp, hPU,
    hPUc, map_zero, add_zero]

/-- Vector form of the cosine square on the source complement. -/
theorem halmosCosineSq_source_compl_apply (x : H) (hx : x ∈ Uᗮ) :
    halmosCosineSq U V x
      = complementaryProjection U (complementaryProjection V x) := by
  have hPUc : complementaryProjection U x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hPU : projection U x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[ℂ] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show complementaryProjection U x = Uᗮ.starProjection x from rfl] at hPUc
    have hUeq : U.starProjection x = x - Uᗮ.starProjection x := by rw [hx']; abel
    rw [show projection U x = U.starProjection x from rfl, hUeq, hPUc, sub_self]
  show (projection U * projection V * projection U
    + complementaryProjection U * complementaryProjection V
      * complementaryProjection U) x = _
  simp only [add_apply, mul_apply_eq_comp, hPU,
    hPUc, map_zero, zero_add]

/-- Complementary projections preserve a subspace reducing the projection. -/
theorem complementaryProjection_mem_of_reduces {W M : Submodule ℂ H}
    [W.HasOrthogonalProjection] (hR : (projection W).Reduces M) {w : H}
    (hw : w ∈ M) : complementaryProjection W w ∈ M := by
  have hcompl : complementaryProjection W w = w - projection W w :=
    congrArg (fun T : H →L[ℂ] H => T w) (Submodule.starProjection_orthogonal' W)
  rw [hcompl]
  exact M.sub_mem hw (hR.1 w hw)

/-- The cosine square preserves a subspace reducing both projections. -/
theorem halmosCosineSq_mem_of_reduces {M : Submodule ℂ H}
    (hRU : (projection U).Reduces M) (hRV : (projection V).Reduces M)
    {w : H} (hw : w ∈ M) : halmosCosineSq U V w ∈ M := by
  have hval : halmosCosineSq U V w
      = projection U (projection V (projection U w))
        + complementaryProjection U (complementaryProjection V
            (complementaryProjection U w)) := by
    show (projection U * projection V * projection U
      + complementaryProjection U * complementaryProjection V
        * complementaryProjection U) w = _
    simp only [add_apply, mul_apply_eq_comp]
  rw [hval]
  refine M.add_mem (hRU.1 _ (hRV.1 _ (hRU.1 _ hw))) ?_
  exact complementaryProjection_mem_of_reduces hRU
    (complementaryProjection_mem_of_reduces hRV
      (complementaryProjection_mem_of_reduces hRU hw))

/-- Forward direction of Proposition 3.5: the fixed-cosine eigenspace reduces
both projections and every source, target, source-complement and
target-complement vector makes the fixed cosine `c`. -/
theorem fixedCosineSubspace_isFixedCosineReducing (c : ℝ) (hc0 : 0 < c) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c := by
  refine ⟨reduces_projection_of_commute U V c U (halmosCosineSq_commute_projection U V),
    reduces_projection_of_commute U V c V (halmosCosineSq_commute_projection_right U V),
    ?_, ?_, ?_, ?_⟩
  · intro x hxM hxU
    refine norm_eq_from_ofReal_sq (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source U V x hxU, (mem_fixedCosineSubspace U V c x).mp hxM,
      inner_smul_left, map_pow, Complex.conj_ofReal, inner_self_ofReal]
  · intro x hxM hxV
    refine norm_eq_from_ofReal_sq (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source V U x hxV, ← halmosCosineSq_symm U V,
      (mem_fixedCosineSubspace U V c x).mp hxM, inner_smul_left, map_pow,
      Complex.conj_ofReal, inner_self_ofReal]
  · intro x hxM hxU
    refine norm_eq_from_ofReal_sq (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source_compl U V x hxU, (mem_fixedCosineSubspace U V c x).mp hxM,
      inner_smul_left, map_pow, Complex.conj_ofReal, inner_self_ofReal]
  · intro x hxM hxV
    refine norm_eq_from_ofReal_sq (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source_compl V U x hxV, ← halmosCosineSq_symm U V,
      (mem_fixedCosineSubspace U V c x).mp hxM, inner_smul_left, map_pow,
      Complex.conj_ofReal, inner_self_ofReal]

/-- Maximality direction of Proposition 3.5: any subspace with constant
source-side cosine `c` lies in the fixed-cosine eigenspace. -/
theorem fixedCosineSubspace_maximal (c : ℝ) {M : Submodule ℂ H}
    (hRU : (projection U).Reduces M) (hRV : (projection V).Reduces M)
    (hU : ∀ x : H, x ∈ M → x ∈ U → ‖projection V x‖ = c * ‖x‖)
    (hUc : ∀ x : H, x ∈ M → x ∈ Uᗮ → ‖complementaryProjection V x‖ = c * ‖x‖) :
    M ≤ fixedCosineSubspace U V c := by
  have hEU : ∀ w ∈ M, w ∈ U → halmosCosineSq U V w = (c : ℂ) ^ 2 • w := by
    intro w hwM hwU
    have hclaim : (halmosCosineSq U V - (c : ℂ) ^ 2 • (1 : H →L[ℂ] H)) w = 0 := by
      refine eigen_of_reducing_quadratic (W := M ⊓ U) ?_ ?_
        (Submodule.mem_inf.mpr ⟨hwM, hwU⟩)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        simp only [sub_apply, smul_apply,
          one_apply_eq_self]
        refine Submodule.mem_inf.mpr
          ⟨M.sub_mem (halmosCosineSq_mem_of_reduces U V hRU hRV hyM) (M.smul_mem _ hyM), ?_⟩
        rw [halmosCosineSq_source_apply U V y hyU]
        exact U.sub_mem (U.starProjection_apply_mem _) (U.smul_mem _ hyU)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        rw [sub_apply, inner_sub_left,
          smul_apply, one_apply_eq_self,
          inner_halmosCosineSq_source U V y hyU, inner_smul_left, map_pow,
          Complex.conj_ofReal, inner_self_ofReal, hU y hyM hyU]
        push_cast; ring
    have heq : halmosCosineSq U V w - (c : ℂ) ^ 2 • w = 0 := by
      rwa [sub_apply, smul_apply,
        one_apply_eq_self] at hclaim
    exact sub_eq_zero.mp heq
  have hEUc : ∀ w ∈ M, w ∈ Uᗮ → halmosCosineSq U V w = (c : ℂ) ^ 2 • w := by
    intro w hwM hwU
    have hclaim : (halmosCosineSq U V - (c : ℂ) ^ 2 • (1 : H →L[ℂ] H)) w = 0 := by
      refine eigen_of_reducing_quadratic (W := M ⊓ Uᗮ) ?_ ?_
        (Submodule.mem_inf.mpr ⟨hwM, hwU⟩)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        simp only [sub_apply, smul_apply,
          one_apply_eq_self]
        refine Submodule.mem_inf.mpr
          ⟨M.sub_mem (halmosCosineSq_mem_of_reduces U V hRU hRV hyM) (M.smul_mem _ hyM), ?_⟩
        rw [halmosCosineSq_source_compl_apply U V y hyU]
        exact Uᗮ.sub_mem (Uᗮ.starProjection_apply_mem _) (Uᗮ.smul_mem _ hyU)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        rw [sub_apply, inner_sub_left,
          smul_apply, one_apply_eq_self,
          inner_halmosCosineSq_source_compl U V y hyU, inner_smul_left, map_pow,
          Complex.conj_ofReal, inner_self_ofReal, hUc y hyM hyU]
        push_cast; ring
    have heq : halmosCosineSq U V w - (c : ℂ) ^ 2 • w = 0 := by
      rwa [sub_apply, smul_apply,
        one_apply_eq_self] at hclaim
    exact sub_eq_zero.mp heq
  intro w hw
  rw [mem_fixedCosineSubspace]
  have hdecomp : w = projection U w + complementaryProjection U w := by
    have hcompl : complementaryProjection U w = w - projection U w :=
      congrArg (fun T : H →L[ℂ] H => T w) (Submodule.starProjection_orthogonal' U)
    rw [hcompl]; abel
  have e1 := hEU (projection U w) (hRU.1 w hw) (U.starProjection_apply_mem w)
  have e2 := hEUc (complementaryProjection U w)
    (complementaryProjection_mem_of_reduces hRU hw) (Uᗮ.starProjection_apply_mem w)
  conv_lhs => rw [hdecomp]
  conv_rhs => rw [hdecomp]
  rw [map_add, e1, e2, smul_add]

/-- Davis--Kahan 1970, Proposition 3.5: in the acute case each fixed-angle
eigenspace of the Halmos cosine square is the unique maximal reducing subspace
with that angle.

The maximality hypothesis carries the corrected `IsFixedCosineReducingSubspace`
predicate (see its docstring): the printed source predicate, constraining only
`M ∩ U` and `M ∩ V`, is refuted for `c < 1` by an exterior vector, and the
complement conditions restore the paper's *all nonzero vectors make the fixed
angle* clause.  The acuteness and `c ≤ 1` hypotheses are retained for source
correspondence; the proof needs only `0 < c`. -/
theorem proposition3_5_fixedAngle_maximal
    (hacute : IsAcute U V) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c ∧
      ∀ M : Submodule ℂ H,
        IsFixedCosineReducingSubspace U V M c →
          M ≤ fixedCosineSubspace U V c := by
  refine ⟨fixedCosineSubspace_isFixedCosineReducing U V c hc0, ?_⟩
  intro M hM
  obtain ⟨hRU, hRV, hUcond, _hVcond, hUperp, _hVperp⟩ := hM
  exact fixedCosineSubspace_maximal U V c hRU hRV hUcond hUperp

/-- Davis--Kahan 1970, Corollary 3.2: interchanging the subspaces preserves the
angle data and reverses the canonical quarter-turn. -/
theorem corollary3_2_reversal_source_form
    (hacute : IsAcute U V) :
    spectraDirectRotation V U
        (_root_.TauCeti.DavisKahan.IsAcute.symm hacute) =
      star (spectraDirectRotation U V hacute) :=
  MathAhead.Section3.corollary3_2_reversal_completed U V hacute

end OneSpace

section Classification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- Equality of the four elementary Halmos summands, expressed without a
finite-rank substitute. -/
structure SameHalmosTrivialDimensions : Prop where
  common : Nonempty
    (halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
  exterior : Nonempty
    (halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)

/-- The modern operator-level complete invariant: trivial dimensions plus the
unitary-equivalence class of the angle operator `cos²Θ`.

**The angle operator is read on the `U`-side, as the compression of `P_V` to
`U ⊓ generic`** — the `genericCosineBlock` of `Geometry/Halmos/GenericPosition`.
That is the operator whose spectral multiplicity function Davis and Kahan's
Theorem 3.1 uses.

This field used to record `genericHalmosCosineSq`, the compression of the
symmetrized `P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ`.  On the generic part that operator is
the cosine block on the `U`-half and `1 - D` on the `Uᗮ`-half, i.e. `A ⊕ A`
(`coe_genericHalmosCosineSq_of_mem_left` proves the `M` half).  Recovering `A`
from `A ⊕ A` up to unitary equivalence is multiplicity-halving — Hahn--Hellinger,
which Mathlib does not have — whereas the pair `(U, V)` is determined by `A`
alone by elementary means.  The symmetrized reading was a repository choice that
doubled the multiplicity and put multiplicity theory on the critical path for no
mathematical reason.  Changed 2026-08-04, which is what closes
`twoProjection_operator_classification`. -/
structure SameHalmosOperatorInvariant : Prop where
  trivial : SameHalmosTrivialDimensions U₁ V₁ U₂ V₂
  generic : BoundedOperatorsUnitaryEquivalent
    (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁)
    (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂)

/-- Forward direction of the operator-level Halmos classification: a unitary
equivalence of the ordered pairs induces the complete operator invariant.  The
restriction of the equivalence to each elementary Halmos summand is a linear
isometric equivalence, and on the generic remainder it intertwines the
cosine-square operator.  Proved axiom-clean in
`MathAhead.HiddenFoundations.sameHalmosInvariant_of_pairEquiv`. -/
theorem sameHalmosOperatorInvariant_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  obtain ⟨hc, hs, ht, he, _⟩ :=
    MathAhead.HiddenFoundations.sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
  exact ⟨⟨hc, hs, ht, he⟩,
    MathAhead.HiddenFoundations.exists_cosineBlockEquiv_of_pairEquiv U₁ V₁ U₂ V₂ h⟩

/-- **Operator-level Halmos classification, both directions.**  This is the
constructive spine of Davis--Kahan Theorem 3.1 and needs no direct-integral
presentation, no compactness, no finite dimension and no separability.

Grounded by `:=` on
`MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`,
so there is a single source of truth.  The forward direction restricts a
pair-equivalence to the `U`-half of the generic part; the converse is bricks (1)
and (2) — brick (1) reconstructs the generic-part unitary from the cosine block
alone (`Geometry/Halmos/GenericReconstruction`), brick (2) glues it to the four
elementary summand isometries (`Geometry/Halmos/Assembly`). -/
theorem twoProjection_operator_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  rw [MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant
    U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨hc, hs, ht, he, hg⟩
    exact ⟨⟨hc, hs, ht, he⟩, hg⟩
  · rintro ⟨⟨hc, hs, ht, he⟩, hg⟩
    exact ⟨hc, hs, ht, he, hg⟩

/-- **Davis--Kahan 1970, Theorem 3.1**, in the paper's own phrasing: the spectral multiplicity
data of the two angle operators, together with the elementary multiplicities, form a complete
invariant for ordered pairs of subspaces.

**The angle operator is `genericCosineBlock`, not `genericHalmosCosineSq`.**  The statement used
to compare the symmetrized block, which on the generic part is `A ⊕ A` -- doubled multiplicity --
and recovering `A` from `A ⊕ A` is multiplicity-halving, which this development does not have and
does not need.  The docstring at `SameHalmosOperatorInvariant` records the 2026-08-04 decision
that put the `U`-side cosine block into the operator invariant for exactly this reason; the same
correction was applied to Corollary 3.1 on 2026-08-06.  Davis and Kahan state Theorem 3.1 for the
angle operator on the `U`-side, so this is the paper-faithful reading.

**On separability.**  It is carried on `H₁` only, it is inherited by the generic left half, and
it is the paper's own standing convention.  It is needed for `→` alone -- producing a
multiplicity model requires the existence half of Hahn--Hellinger -- and the `←` direction is
separability-free.  Crucially, nothing already proved is weakened: the operator-level form
`twoProjection_operator_classification`, grounded on
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, remains stated with no
separability, no compactness and no finite dimension, and it is that theorem which carries the
classification content of Theorem 3.1.  What this statement adds is the *translation* of its
invariant into multiplicity data. -/
theorem theorem3_1_spectralMultiplicity_classification
    [TopologicalSpace.SeparableSpace H₁] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁)
        (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂) := by
  rw [twoProjection_operator_classification]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, sameSpectralMultiplicity_of_unitarilyEquivalent _ _ ?_ hgen⟩
    exact MathAhead.HiddenFoundations.isSelfAdjoint_genericCosineBlock U₁ V₁
  · rintro ⟨htriv, hmult⟩
    exact ⟨htriv, unitarilyEquivalent_of_sameSpectralMultiplicity _ _ hmult⟩

/-- Ordered eigenvalue data for a compact positive contraction: the
approximation-number sequence of `A`.

For a compact **positive** operator this is exactly the ordered eigenvalue list
*with multiplicity* — `aₙ(A)` is the `n`-th largest singular value, and singular
values coincide with eigenvalues when the operator is positive, so a repeated
eigenvalue is repeated in the sequence.  That is the implementation this
declaration's earlier `sorry` body was documented as wanting.

Note the definition is total: it is stated for every `A`, and only *means* the
angle eigenvalue list under the compactness and positivity hypotheses that the
consumers carry.  This mirrors `approximationNumber` itself, which is total in
the same way. -/
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (A : K →L[ℂ] K) : ℕ → ℝ :=
  fun n => A.approximationNumber n

/-- **Approximation numbers are a unitary invariant.**  Conjugating by a linear isometric
equivalence sandwiches the operator between two contractions in both directions, so no
approximation number can move. -/
theorem approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (h : BoundedOperatorsUnitaryEquivalent A B) (n : ℕ) :
    A.approximationNumber n = B.approximationNumber n := by
  obtain ⟨U, hU⟩ := h
  have hUapp : ∀ x, B (U x) = U (A x) := fun x => (hU x).symm
  have hUnorm : ‖(U : E →L[ℂ] F)‖ ≤ 1 :=
    U.toLinearIsometry.norm_toContinuousLinearMap_le
  have hUsnorm : ‖(U.symm : F →L[ℂ] E)‖ ≤ 1 :=
    U.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  have hBfact : B = (U : E →L[ℂ] F) ∘L A ∘L (U.symm : F →L[ℂ] E) := by
    ext y
    change B y = U (A (U.symm y))
    rw [← hUapp (U.symm y), U.apply_symm_apply]
  have hAfact : A = (U.symm : F →L[ℂ] E) ∘L B ∘L (U : E →L[ℂ] F) := by
    ext x
    change A x = U.symm (B (U x))
    rw [hUapp x, U.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [hAfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U.symm : F →L[ℂ] E) (U : E →L[ℂ] F) hUsnorm hUnorm n
  · conv_lhs => rw [hBfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U : E →L[ℂ] F) (U.symm : F →L[ℂ] E) hUnorm hUsnorm n

/-- Davis--Kahan 1970, Corollary 3.1: when the cross-projection is compact, the
angle eigenvalue lists and elementary multiplicities classify the pair. -/
theorem corollary3_1_compact_angleList_classification
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁) =
        compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂) := by
  have hpos₁ : ∀ x, 0 ≤ RCLike.re
      ⟪MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁ x, x⟫_ℂ := by
    intro x
    rw [MathAhead.HiddenFoundations.re_inner_genericCosineBlock]
    positivity
  have hpos₂ : ∀ x, 0 ≤ RCLike.re
      ⟪MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂ x, x⟫_ℂ := by
    intro x
    rw [MathAhead.HiddenFoundations.re_inner_genericCosineBlock]
    positivity
  rw [twoProjection_operator_classification U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, ?_⟩
    funext n
    exact approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent hgen n
  · rintro ⟨htriv, hlist⟩
    refine ⟨htriv, ?_⟩
    obtain ⟨W, hW⟩ :=
      TauCeti.exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq
        (MathAhead.HiddenFoundations.isCompactOperator_genericCosineBlock U₁ V₁ hcompact₁)
        (MathAhead.HiddenFoundations.isSelfAdjoint_genericCosineBlock U₁ V₁)
        hpos₁
        (MathAhead.HiddenFoundations.eigenspace_genericCosineBlock_zero U₁ V₁)
        (MathAhead.HiddenFoundations.isCompactOperator_genericCosineBlock U₂ V₂ hcompact₂)
        (MathAhead.HiddenFoundations.isSelfAdjoint_genericCosineBlock U₂ V₂)
        hpos₂
        (MathAhead.HiddenFoundations.eigenspace_genericCosineBlock_zero U₂ V₂)
        (fun n => congrFun hlist n)
    exact ⟨W, hW⟩

end Classification

end Section3
end Frontier
end Experimental
end DavisKahan
end TauCeti