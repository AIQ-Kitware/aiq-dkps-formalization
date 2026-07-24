/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import DavisKahan.Interop.Spectra.DirectRotation
-- supplies `spectraReflectionProduct` and `IsAcute.symm`
import DavisKahan.Interop.Spectra.DirectRotationSquare
-- supplies the completed nonacute construction and acute characterizations used
-- to ground the Proposition 3.2 and Corollary 3.2 source statements below.  The
-- construction depends on the polar and acute machinery under `MathAhead`, which
-- itself never imports this module, so the dependency is acyclic.
import DavisKahan.Experimental.MathAhead.HiddenFoundations.Section3Nonacute
-- supplies the forward direction of the operator-level Halmos classification
-- (`sameHalmosInvariant_of_pairEquiv`).  This module imports only Frontier/Core,
-- so the dependency is acyclic.
import DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosClassification

/-!
# Section 3 frontier: separation and classification of two subspaces

These declarations state the remaining source results and the reusable
classification bridges beneath them.  The first completion target is the
constructive nonacute direct-rotation criterion.  The spectral-multiplicity
formulation is separated from the operator-level Halmos classification so the
latter can be completed without inventing direct-integral infrastructure.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section3

open SpectraBridge

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
    rw [ContinuousLinearMap.add_apply, inner_add_left, map_add] at hy
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
    rw [ContinuousLinearMap.mul_apply, hRU, Submodule.reflectionOperator_apply, hQz]
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
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply]
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
        simpa [ContinuousLinearMap.mul_apply] using this
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
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      hTx, map_add, hQTPx, hQTPcx, add_zero, sub_self]
  -- final intertwining: X = 0
  have hXeq : T * projection U = projection V * T := by
    haveI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
    haveI : A.ker.HasOrthogonalProjection := inferInstance
    have hrangeLe : A.range ≤ (T * projection U - projection V * T).ker := by
      rintro y ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      have := congrArg (fun f : H →L[ℂ] H => f z) hXA
      simpa [ContinuousLinearMap.mul_apply] using this
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
      simp only [ContinuousLinearMap.mul_apply]
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
      simp only [ContinuousLinearMap.mul_apply]
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

/-- Davis--Kahan 1970, Proposition 3.4 in source form: under the half-angle
condition, the square of the direct rotation is the direct rotation between
the reflected source and target subspaces.

Open obligation, with a required hypothesis correction recorded here.  The
natural reflected pair is `Uref = U`, `Vref = reflectedSubspace V U`, for which
`spectraDirectRotation U V hacute` squared equals the ordered reflection product
`R_V R_U` (see `spectraDirectRotation_sq`).  Because every acute direct rotation
has nonnegative numerical real part, a necessary condition for the conclusion is
`0 ≤ re ⟪(R_V R_U) x, x⟫`.  Writing `2 S = 1 + R_V R_U` for the canonical
intertwiner `S` and using its normality identity `Re S = S⋆ S = |S| ^ 2`, one has
`re ⟪(R_V R_U) x, x⟫ = 2 * re ⟪(|S| ^ 2) x, x⟫ - ‖x‖ ^ 2`, and `|S| ^ 2` is the
Halmos cosine square.  Hence the correct threshold is on the cosine *square*,
`re ⟪halmosCosineSq x, x⟫ ≥ ‖x‖ ^ 2 / 2` (cosine `≥ 1 / √2`, angle `≤ π / 4`),
not on `|S|` itself: the printed bound `re ⟪|S| x, x⟫ ≥ ‖x‖ ^ 2 / 2` is strictly
weaker since `|S| ≤ 1`.  Moreover the reflected pair is acute only under a
uniform strict form of that bound (a boundary cosine of `1 / √2` gives a
double angle of exactly `π / 2`, hence gap `1`), so the field should carry a
uniform gap, not the pointwise nonstrict inequality below. -/
theorem proposition3_4_square_is_reflected_directRotation
    (hacute : IsAcute U V)
    (hhalf : ∀ x : H,
      0 ≤ RCLike.re
        ⟪x, (spectraOperatorAbsoluteValue
          (spectraCanonicalIntertwiner U V)) x⟫_ℂ - ‖x‖ ^ 2 / 2) :
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
  sorry

/-- A subspace on which both projections reduce and every nonzero source or
target vector has the same projection cosine. -/
def IsFixedCosineReducingSubspace
    (M : Submodule ℂ H) (c : ℝ) : Prop :=
  (projection U).Reduces M ∧
  (projection V).Reduces M ∧
  (∀ x : H, x ∈ M → x ∈ U → ‖projection V x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ V → ‖projection U x‖ = c * ‖x‖)

/-- The fixed-cosine spectral subspace on the generic Halmos summand.

The pair is bound explicitly rather than taken from the section: the body is
still an open obligation, so auto-inclusion would not fire and the subspace
would spuriously fail to depend on the pair it is defined from. -/
noncomputable def fixedCosineSubspace (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (c : ℝ) : Submodule ℂ H := by
  sorry

/-- Davis--Kahan 1970, Proposition 3.5: in the acute case each fixed-angle
spectral subspace is the unique maximal reducing subspace with that angle. -/
theorem proposition3_5_fixedAngle_maximal
    (hacute : IsAcute U V) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c ∧
      ∀ M : Submodule ℂ H,
        IsFixedCosineReducingSubspace U V M c →
          M ≤ fixedCosineSubspace U V c := by
  sorry

/-- Davis--Kahan 1970, Corollary 3.2: interchanging the subspaces preserves the
angle data and reverses the canonical quarter-turn. -/
theorem corollary3_2_reversal_source_form
    (hacute : IsAcute U V) :
    spectraDirectRotation V U
        (_root_.ForMathlib.DavisKahan.IsAcute.symm hacute) =
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
unitary-equivalence class of the generic cosine square. -/
structure SameHalmosOperatorInvariant : Prop where
  trivial : SameHalmosTrivialDimensions U₁ V₁ U₂ V₂
  generic : BoundedOperatorsUnitaryEquivalent
    (genericHalmosCosineSq U₁ V₁)
    (genericHalmosCosineSq U₂ V₂)

/-- Forward direction of the operator-level Halmos classification: a unitary
equivalence of the ordered pairs induces the complete operator invariant.  The
restriction of the equivalence to each elementary Halmos summand is a linear
isometric equivalence, and on the generic remainder it intertwines the
cosine-square operator.  Proved axiom-clean in
`MathAhead.HiddenFoundations.sameHalmosInvariant_of_pairEquiv`. -/
theorem sameHalmosOperatorInvariant_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  obtain ⟨hc, hs, ht, he, hg⟩ :=
    MathAhead.HiddenFoundations.sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
  exact ⟨⟨hc, hs, ht, he⟩, hg⟩

/-- Operator-level Halmos classification.  This is the constructive spine of
Davis--Kahan Theorem 3.1 and does not require a direct-integral presentation.

The forward direction is proved (`sameHalmosOperatorInvariant_of_pairEquiv`).
The converse — reconstructing a pair-equivalence from the operator invariant —
still needs two bricks, neither yet available: (1) the generic 2×2 Halmos model,
which upgrades a bare unitary equivalence of the two generic cosine-square
operators to a unitary of the generic subspaces intertwining *both* projections
(equivalently, the reconstruction of the reducing angle pair from `cos²Θ`); and
(2) the block-diagonal orthogonal assembly gluing the four elementary summand
isometries and the generic-part unitary into a global `H₁ ≃ₗᵢ[ℂ] H₂` carrying
`U₁, V₁` to `U₂, V₂`.  On the four elementary summands the assembled map
automatically intertwines both projections, so brick (2) reduces to a
Hilbert-sum gluing and brick (1) is the sole genuinely missing mathematics. -/
theorem twoProjection_operator_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  refine ⟨sameHalmosOperatorInvariant_of_pairEquiv U₁ V₁ U₂ V₂, ?_⟩
  intro _hinv
  sorry

/-- Davis--Kahan 1970, Theorem 3.1: spectral multiplicity data of the two angle
operators, together with the elementary multiplicities, form a complete
invariant. -/
theorem theorem3_1_spectralMultiplicity_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericHalmosCosineSq U₁ V₁)
        (genericHalmosCosineSq U₂ V₂) := by
  sorry

/-- Ordered eigenvalue data for a compact positive contraction.  The eventual
implementation should use approximation numbers or compact self-adjoint
spectral theory and record multiplicities. -/
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (A : K →L[ℂ] K) : ℕ → ℝ := by
  sorry

/-- Davis--Kahan 1970, Corollary 3.1: when the cross-projection is compact, the
angle eigenvalue lists and elementary multiplicities classify the pair. -/
theorem corollary3_1_compact_angleList_classification
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList (genericHalmosCosineSq U₁ V₁) =
        compactAngleEigenvalueList (genericHalmosCosineSq U₂ V₂) := by
  sorry

end Classification

end Section3
end Frontier
end Experimental
end DavisKahan
end ForMathlib
