/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Frontier.Core
import DavisKahan.Geometry.Polar.DirectRotation
-- supplies `spectraReflectionProduct` and `IsUniformlyAcute.symm`
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
import ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
-- supplies the continuous functional calculus over `ℝ` for bounded self-adjoint
-- operators on a real Hilbert space, in unrestricted dimension.  It is what
-- discharges the functional-calculus hypotheses of the Halmos spine at
-- `𝕜 = ℝ`, and so what makes the real-scalar section at the end of this file
-- inhabited rather than vacuous.
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
-- supplies `TauCeti.IsAcute` together with
-- `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`, the literal restatement of the
-- paper's Definition 3.2 as the vanishing of the two crossed intersections.
-- Proposition 3.2's nonuniqueness sentence is stated against that definition.
import DavisKahan.Geometry.Halmos.AngleSequenceRealization
-- supplies the diagonal angle datum of a prescribed decreasing sequence, which
-- is what Corollary 3.1's realization sentence asks for.  That module imports
-- only `Geometry/Halmos/Realization` and `ForTauCeti`, so it is acyclic.
import DavisKahan.Geometry.Halmos.Realization
-- supplies the realization half of Theorem 3.1: the explicit direct-rotation
-- construction attaining a prescribed admissible angle datum.  That module
-- imports only `Geometry/Halmos/TwoProjections` and Mathlib, so the dependency
-- is acyclic.

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

section BlockCalculus

/-! ### The `U`-block calculus of a unitary intertwiner

These four identities are what both Proposition 3.1 and Proposition 3.3 run on, and they need
no acuteness.  They were originally inlined in Proposition 3.1's proof; Proposition 3.3's
forward direction needs the same seventy-five lines, so they live here once. -/

variable (T : H →L[ℂ] H)

omit [CompleteSpace H] in
/-- **Block decomposition of an operator relative to `U ⊕ Uᗮ`.** -/
theorem eq_sum_blocks (A : H →L[ℂ] H) :
    A = projection U * A * projection U + projection U * A * complementaryProjection U
      + complementaryProjection U * A * projection U
      + complementaryProjection U * A * complementaryProjection U := by
  have hone : projection U + complementaryProjection U = 1 := by
    rw [show complementaryProjection U = 1 - projection U from
      Submodule.starProjection_orthogonal' U]
    abel
  calc A = (projection U + complementaryProjection U) * A
        * (projection U + complementaryProjection U) := by rw [hone, one_mul, mul_one]
    _ = _ := by noncomm_ring

/-- **The `U`-blocks of `star T`**, for an operator whose diagonal compressions are self-adjoint
and whose crossed blocks are skew: the diagonal blocks are fixed and the off-diagonal ones are
sign-flipped. -/
theorem star_blocks_eq
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U))
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)) :
    projection U * star T * projection U = projection U * T * projection U ∧
      complementaryProjection U * star T * complementaryProjection U
        = complementaryProjection U * T * complementaryProjection U ∧
      projection U * star T * complementaryProjection U
        = -(projection U * T * complementaryProjection U) ∧
      complementaryProjection U * star T * projection U
        = -(complementaryProjection U * T * projection U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hsource_sa.star_eq
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq, ← mul_assoc] at h
    exact h
  · have h := hcomplement_sa.star_eq
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    exact h
  · have h := congrArg star hcrossed
    rw [star_neg, star_star, star_mul, star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    exact h
  · have h := hcrossed
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    rw [h, neg_neg]

/-- **A direct rotation squares to the reflection product**, with no acuteness hypothesis.

The reflection through `U` conjugates `star T` back to `T` -- the diagonal blocks survive and the
off-diagonal ones are negated twice -- and the intertwining turns that into `T * T = J_V J_U`. -/
theorem sq_eq_spectraReflectionProduct
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U))
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)) :
    T * T = spectraReflectionProduct U V := by
  obtain ⟨e11, e22, e12, e21⟩ := star_blocks_eq U T hsource_sa hcomplement_sa hcrossed
  have hRsub : reflectionOperator U = projection U - complementaryProjection U := by
    rw [reflectionOperator_eq_projection_add_projection_sub_one U,
      show complementaryProjection U = 1 - projection U from
        Submodule.starProjection_orthogonal' U]
    abel
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
    conv_rhs => rw [eq_sum_blocks U T]
    abel
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
  have hexp : spectraReflectionProduct U V
      = T * (reflectionOperator U * star T * reflectionOperator U) := by
    change reflectionOperator V * reflectionOperator U = _
    rw [hRV]; noncomm_ring
  rw [hexp, hkey]

/-- **The Hermitian part of a direct rotation is twice its diagonal.**

The crossed blocks of `T` and of `star T` are negatives of one another, so they cancel in the
sum and only the diagonal survives, doubled. -/
theorem add_star_eq_two_diagonal
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U))
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)) :
    T + star T =
      projection U * T * projection U + projection U * T * projection U
        + (complementaryProjection U * T * complementaryProjection U
          + complementaryProjection U * T * complementaryProjection U) := by
  obtain ⟨e11, e22, e12, e21⟩ := star_blocks_eq U T hsource_sa hcomplement_sa hcrossed
  calc T + star T
      = (projection U * T * projection U + projection U * T * complementaryProjection U
            + complementaryProjection U * T * projection U
            + complementaryProjection U * T * complementaryProjection U)
          + (projection U * star T * projection U
            + projection U * star T * complementaryProjection U
            + complementaryProjection U * star T * projection U
            + complementaryProjection U * star T * complementaryProjection U) := by
        rw [← eq_sum_blocks U T, ← eq_sum_blocks U (star T)]
    _ = _ := by rw [e11, e12, e21, e22]; abel

end BlockCalculus

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
    (hacute : IsUniformlyAcute U V) (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPaperDirectRotation U V T ↔
      T = spectraDirectRotation U V hacute := by
  constructor
  · intro hT
    have hsq : T * T = spectraReflectionProduct U V :=
      sq_eq_spectraReflectionProduct U V T hunitary hintertwines hsource_sa
        hcomplement_sa hT.crossed_blocks
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
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunit
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
    have : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
    have : A.ker.HasOrthogonalProjection := inferInstance
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

/-! ### Proposition 3.3, forward direction

The converse above holds for an arbitrary pair, acute or not.  What was missing was the forward
half in the same generality: the printed proposition says *every* direct rotation is a principal
square root of the reflection product, and the compiled forward statements
(`complex_directRotation_sq`, `complex_directRotation_hermitianPart`) speak only about the
canonical acute one.

The block calculus below supplies it.  Three things have to be produced, and only the first two
cost anything:

* `T * T = J_V J_U`.  This is the argument already inside
  `proposition3_1_positivity_characterization`, extracted so that it is available without
  acuteness.
* spectrum in the closed right half-plane.  The Hermitian part of a direct rotation is *twice its
  diagonal*, the crossed blocks cancelling by `crossed_blocks`, so it is positive; for a normal
  operator that transfers to the spectrum through `cfc_nonneg_iff`.
* the crossed-intersection mapping condition.  This one is **free**: the converse takes it as a
  hypothesis, but in the forward direction it is a consequence.  Both crossed intersections sit
  inside the `-1` eigenspace of the reflection product, `T` and `star T` commute with that
  operator because `T * T` *is* it, and the intertwining moves `U` to `V` -- which pins the image
  down to the other crossed intersection.

The self-adjointness hypotheses on the diagonal compressions are the same two that
Proposition 3.1 needs, and for the same reason: `IsPaperDirectRotation` records the compressions
only through their numerical range, which does not by itself force `star T`'s diagonal blocks to
agree with `T`'s. -/

section PrincipalSquareRoot

variable (T : H →L[ℂ] H)

/-- **The Hermitian part of a direct rotation is a positive operator.** -/
theorem nonneg_add_star_of_isPaperDirectRotation (hT : IsPaperDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    (0 : H →L[ℂ] H) ≤ T + star T := by
  have hP : (0 : H →L[ℂ] H) ≤ projection U * T * projection U := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨hsource_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.source_compression_nonnegative x
  have hPc : (0 : H →L[ℂ] H)
      ≤ complementaryProjection U * T * complementaryProjection U := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨hcomplement_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.complement_compression_nonnegative x
  rw [add_star_eq_two_diagonal U T hsource_sa hcomplement_sa hT.crossed_blocks]
  exact add_nonneg (add_nonneg hP hP) (add_nonneg hPc hPc)

omit [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
open scoped ComplexOrder in
/-- **A unitary whose Hermitian part is positive has spectrum in the closed right half-plane.**

This is what the word "principal" means for a square root of a unitary: among the square roots,
the one whose spectral arc avoids the open left half-plane.  For a normal element the transfer
from operator positivity to the spectrum is `cfc_nonneg_iff`. -/
theorem spectrum_re_nonneg_of_nonneg_add_star
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hpos : (0 : H →L[ℂ] H) ≤ T + star T) :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re := by
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunitary
  have e2 : cfc (fun z : ℂ => star z) T = star T := by
    rw [cfc_star (R := ℂ) (fun z : ℂ => z) T, cfc_id' ℂ T]
  have e3 : T + star T = cfc (fun z : ℂ => z + star z) T := by
    rw [cfc_add (R := ℂ) T (fun z : ℂ => z) (fun z : ℂ => star z)
      continuous_id.continuousOn continuous_star.continuousOn, cfc_id' ℂ T, e2]
  rw [e3] at hpos
  have hz := (cfc_nonneg_iff (R := ℂ) (fun z : ℂ => z + star z) T
    (by fun_prop) hTnorm).mp hpos
  intro z hzmem
  have h := hz z hzmem
  rw [Complex.le_def] at h
  have hre : (0 : ℝ) ≤ (z + star z).re := h.1
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at hre
  linarith

/-! The two crossed intersections are exactly the part of the `-1` eigenspace of the reflection
product that lies in `U`, respectively in `V`.  That is the whole content of the crossed-mapping
condition in the forward direction. -/

omit [CompleteSpace H] in
/-- The reflection product acts as `-1` on the source crossed intersection. -/
theorem reflectionProduct_apply_eq_neg_of_mem_source {z : H}
    (hz : z ∈ halmosSourceDefect U V) : spectraReflectionProduct U V z = -z := by
  obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosSourceDefect hz
  have hRU : reflectionOperator U z = z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply, hQz]
  module

omit [CompleteSpace H] in
/-- The reflection product acts as `-1` on the target crossed intersection. -/
theorem reflectionProduct_apply_eq_neg_of_mem_target {z : H}
    (hz : z ∈ halmosTargetDefect U V) : spectraReflectionProduct U V z = -z := by
  obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosTargetDefect hz
  have hRU : reflectionOperator U z = -z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, map_neg, Submodule.reflectionOperator_apply, hQz]
  module

omit [CompleteSpace H] in
/-- Inside `U`, the `-1` eigenspace of the reflection product is the source crossed
intersection. -/
theorem mem_halmosSourceDefect_of_reflectionProduct_apply_eq_neg {z : H} (hzU : z ∈ U)
    (hz : spectraReflectionProduct U V z = -z) : z ∈ halmosSourceDefect U V := by
  have hPz : projection U z = z := U.starProjection_eq_self_iff.mpr hzU
  have hRU : reflectionOperator U z = z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply] at hz
  have h0 : (2 : ℂ) • projection V z = 0 := by
    have h := congrArg (fun w : H => w + z) hz
    simpa using h
  have hQz : projection V z = 0 := (smul_eq_zero.mp h0).resolve_left two_ne_zero
  exact Submodule.mem_inf.mpr ⟨hzU, (Submodule.starProjection_apply_eq_zero_iff V).mp hQz⟩

omit [CompleteSpace H] in
/-- Inside `V`, the `-1` eigenspace of the reflection product is the target crossed
intersection. -/
theorem mem_halmosTargetDefect_of_reflectionProduct_apply_eq_neg {z : H} (hzV : z ∈ V)
    (hz : spectraReflectionProduct U V z = -z) : z ∈ halmosTargetDefect U V := by
  have hQz : projection V z = z := V.starProjection_eq_self_iff.mpr hzV
  have hJV : reflectionOperator V z = z := by
    rw [Submodule.reflectionOperator_apply, hQz]; module
  have hinv := Submodule.reflectionOperator_involutive (𝕜 := ℂ) V
  have h1 : reflectionOperator V (reflectionOperator U z) = -z := by
    rw [← mul_apply_eq_comp]; exact hz
  have h2 : reflectionOperator V (reflectionOperator V (reflectionOperator U z))
      = reflectionOperator U z := by
    have h := congrArg (fun f : H →L[ℂ] H => f (reflectionOperator U z)) hinv
    simpa using h
  have hJU : reflectionOperator U z = -z := by
    rw [h1, map_neg, hJV] at h2
    exact h2.symm
  rw [Submodule.reflectionOperator_apply] at hJU
  have h0 : (2 : ℂ) • projection U z = 0 := by
    have h := congrArg (fun w : H => w + z) hJU
    simpa using h
  have hPz : projection U z = 0 := (smul_eq_zero.mp h0).resolve_left two_ne_zero
  exact Submodule.mem_inf.mpr ⟨(Submodule.starProjection_apply_eq_zero_iff U).mp hPz, hzV⟩

/-- **The crossed-intersection mapping condition is free.**

For *any* unitary that squares to the reflection product and intertwines the two
projections, the source crossed intersection is carried onto the target one.  Neither
positivity of the diagonal blocks nor acuteness enters: both crossed intersections sit
inside the `-1` eigenspace of the reflection product, `T` and `star T` commute with that
operator because `T * T` *is* it, and the intertwining moves `U` to `V`, which pins the
image down to the other crossed intersection.

Proposition 3.3's forward direction and printed Proposition 3.4 both consume this. -/
theorem crossedDefect_image_of_unitary_sq
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hsq : T * T = spectraReflectionProduct U V)
    (hintertwines : T * projection U = projection V * T) :
    T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunitary
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hunitary
  -- `T` and `star T` both commute with the reflection product, because it *is* `T * T`.
  have hRT : ∀ x : H,
      spectraReflectionProduct U V (T x) = T (spectraReflectionProduct U V x) := by
    intro x
    have h1 : spectraReflectionProduct U V * T = T * spectraReflectionProduct U V := by
      rw [← hsq]; noncomm_ring
    have h := congrArg (fun f : H →L[ℂ] H => f x) h1
    simpa [mul_apply_eq_comp] using h
  have hRsT : ∀ x : H,
      spectraReflectionProduct U V (star T x) = star T (spectraReflectionProduct U V x) := by
    intro x
    have h1 : spectraReflectionProduct U V * star T = star T * spectraReflectionProduct U V := by
      rw [← hsq]
      calc T * T * star T = T * (T * star T) := by noncomm_ring
        _ = T := by rw [hTsT, mul_one]
        _ = star T * T * T := by rw [hsTT, one_mul]
    have h := congrArg (fun f : H →L[ℂ] H => f x) h1
    simpa [mul_apply_eq_comp] using h
  -- The intertwining moves `U` to `V`, and its adjoint moves `V` back to `U`.
  have hTU : ∀ x ∈ U, T x ∈ V := by
    intro x hx
    have h := congrArg (fun f : H →L[ℂ] H => f x) hintertwines
    simp only [mul_apply_eq_comp] at h
    rw [U.starProjection_eq_self_iff.mpr hx] at h
    exact V.starProjection_eq_self_iff.mp h.symm
  have hstarInt : projection U * star T = star T * projection V := by
    have h := congrArg star hintertwines
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] at h
    exact h
  have hsTV : ∀ y ∈ V, star T y ∈ U := by
    intro y hy
    have h := congrArg (fun f : H →L[ℂ] H => f y) hstarInt
    simp only [mul_apply_eq_comp] at h
    rw [V.starProjection_eq_self_iff.mpr hy] at h
    exact U.starProjection_eq_self_iff.mp h
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_halmosTargetDefect_of_reflectionProduct_apply_eq_neg U V
      (hTU x (mem_halmosSourceDefect.mp hx).1) ?_
    rw [hRT x, reflectionProduct_apply_eq_neg_of_mem_source U V hx, map_neg]
  · intro y hy
    refine ⟨star T y, ?_, ?_⟩
    · refine mem_halmosSourceDefect_of_reflectionProduct_apply_eq_neg U V
        (hsTV y (mem_halmosTargetDefect.mp hy).2) ?_
      rw [hRsT y, reflectionProduct_apply_eq_neg_of_mem_target U V hy, map_neg]
    · have h := congrArg (fun f : H →L[ℂ] H => f y) hTsT
      simpa [mul_apply_eq_comp] using h

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction, with no acuteness hypothesis.**

Every direct rotation is a principal unitary square root of the reflection product, *and* it
carries the source crossed intersection onto the target one.  The second conclusion is the
mapping condition that the converse takes as a hypothesis; here it comes out rather than
going in (`crossedDefect_image_of_unitary_sq`). -/
theorem proposition3_3_principalSquareRoot_forward
    (hT : IsPaperDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
      T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hsq := sq_eq_spectraReflectionProduct U V T hT.unitary_mem hT.intertwines
    hsource_sa hcomplement_sa hT.crossed_blocks
  have hpos := nonneg_add_star_of_isPaperDirectRotation U V T hT hsource_sa hcomplement_sa
  have hspec := spectrum_re_nonneg_of_nonneg_add_star T hT.unitary_mem hpos
  exact ⟨⟨hT.unitary_mem, hsq, hspec⟩,
    crossedDefect_image_of_unitary_sq U V T hT.unitary_mem hsq hT.intertwines⟩

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction, from the printed hypotheses.**

The source says the direct rotation has **positive diagonal blocks**; this repository's
`IsPaperDirectRotation` records them only through their numerical range, which is strictly
weaker and is why `proposition3_3_principalSquareRoot_forward` has to ask for self-adjointness
separately.  Stated with operator positivity, as printed, no side hypothesis is needed at all:
a positive operator is self-adjoint and its numerical range is nonnegative, so both weaker
conditions come for free. -/
theorem proposition3_3_principalSquareRoot_forward_of_nonneg_blocks
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U))
    (hsource_pos : (0 : H →L[ℂ] H) ≤ projection U * T * projection U)
    (hcomplement_pos :
      (0 : H →L[ℂ] H) ≤ complementaryProjection U * T * complementaryProjection U) :
    IsPaperDirectRotation U V T ∧
      IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
      T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hsp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hsource_pos
  have hcp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hcomplement_pos
  have hT : IsPaperDirectRotation U V T :=
    { unitary_mem := hunitary
      intertwines := hintertwines
      source_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hsp.re_inner_nonneg_left x
      complement_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hcp.re_inner_nonneg_left x
      crossed_blocks := hcrossed }
  exact ⟨hT, proposition3_3_principalSquareRoot_forward U V T hT hsp.isSelfAdjoint
    hcp.isSelfAdjoint⟩

open scoped ComplexOrder in
/-- **Davis--Kahan 1970, Proposition 3.3, as a characterisation**, for an arbitrary pair of
subspaces.

A unitary whose diagonal `U`-compressions are self-adjoint is a direct rotation exactly when it
is a principal square root of the reflection product carrying one crossed intersection onto the
other.

The two hypotheses are needed only for the forward implication; the converse,
`proposition3_3_principalSquareRoot_converse`, holds for *every* principal square root with the
mapping property, and should be used directly when they are not available. -/
theorem proposition3_3_principalSquareRoot_iff
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPaperDirectRotation U V T ↔
      (IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
        T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H)) :=
  ⟨fun hT => proposition3_3_principalSquareRoot_forward U V T hT hsource_sa hcomplement_sa,
    fun h => proposition3_3_principalSquareRoot_converse U V T h.1 h.2⟩

end PrincipalSquareRoot

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

Second, acuteness of the reflected pair `IsUniformlyAcute U (reflectedSubspace V U)` is
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
    (hacute : IsUniformlyAcute U V)
    (hacuteReflected : IsUniformlyAcute U (reflectedSubspace V U))
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
      ∃ hacuteRef : IsUniformlyAcute Uref Vref,
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
/-- The Halmos cosine square is symmetric in the ordered pair: it is
`1 - (P_U - P_V) ^ 2`, invariant under swapping the projections. -/
theorem halmosCosineSq_symm :
    halmosCosineSq U V = halmosCosineSq V U := by
  rw [halmosCosineSq_eq_one_sub_projection_sub_sq U V,
    halmosCosineSq_eq_one_sub_projection_sub_sq V U]
  noncomm_ring

omit [CompleteSpace H] in
/-- Squared-norm quadratic form, with the real-to-complex coercion pinned to
`Complex.ofReal`. -/
theorem inner_self_ofReal (x : H) : ⟪x, x⟫_ℂ = (‖x‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K x

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
/-- Membership in the fixed-cosine subspace is the eigenvalue equation. -/
theorem mem_fixedCosineSubspace (c : ℝ) (w : H) :
    w ∈ fixedCosineSubspace U V c ↔ halmosCosineSq U V w = (c : ℂ) ^ 2 • w := by
  rw [fixedCosineSubspace, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, one_apply_eq_self]
  rw [sub_eq_zero]

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
/-- The cosine square commutes with the target projection too. -/
theorem halmosCosineSq_commute_projection_right :
    Commute (halmosCosineSq U V) (projection V) := by
  rw [halmosCosineSq_symm U V]
  exact halmosCosineSq_commute_projection V U

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
/-- Complementary projections preserve a subspace reducing the projection. -/
theorem complementaryProjection_mem_of_reduces {W M : Submodule ℂ H}
    [W.HasOrthogonalProjection] (hR : (projection W).Reduces M) {w : H}
    (hw : w ∈ M) : complementaryProjection W w ∈ M := by
  have hcompl : complementaryProjection W w = w - projection W w :=
    congrArg (fun T : H →L[ℂ] H => T w) (Submodule.starProjection_orthogonal' W)
  rw [hcompl]
  exact M.sub_mem hw (hR.1 w hw)

omit [CompleteSpace H] in
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
    (hacute : IsUniformlyAcute U V) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c ∧
      ∀ M : Submodule ℂ H,
        IsFixedCosineReducingSubspace U V M c →
          M ≤ fixedCosineSubspace U V c := by
  refine ⟨fixedCosineSubspace_isFixedCosineReducing U V c hc0, ?_⟩
  intro M hM
  obtain ⟨hRU, hRV, hUcond, _hVcond, hUperp, _hVperp⟩ := hM
  exact fixedCosineSubspace_maximal U V c hRU hRV hUcond hUperp

/-- Davis--Kahan 1970, Corollary 3.2, quarter-turn half: interchanging the subspaces
reverses the canonical quarter-turn. -/
theorem corollary3_2_reversal_source_form
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation V U
        (_root_.TauCeti.DavisKahan.IsUniformlyAcute.symm hacute) =
      star (spectraDirectRotation U V hacute) :=
  MathAhead.Section3.corollary3_2_reversal_completed U V hacute

/-- Davis--Kahan 1970, Corollary 3.2, angle half: interchanging the subspaces leaves the
angle operator unchanged.  The two projections enter the angle operator only through
their difference, and the absolute value is insensitive to its sign. -/
theorem corollary3_2_sinAngleOperator_symm :
    DavisKahanExt.sinAngleOperator V U = DavisKahanExt.sinAngleOperator U V := by
  rw [DavisKahanExt.sinAngleOperator, DavisKahanExt.sinAngleOperator,
    ← DavisKahanExt.operatorAbsoluteValue_neg]
  congr 1
  abel

/-- **Davis--Kahan 1970, Corollary 3.2**, both halves in one statement: swapping the pair
leaves the angle operator unchanged and reverses the quarter-turn. -/
theorem corollary3_2_reversal
    (hacute : IsUniformlyAcute U V) :
    DavisKahanExt.sinAngleOperator V U = DavisKahanExt.sinAngleOperator U V ∧
      spectraDirectRotation V U
          (_root_.TauCeti.DavisKahan.IsUniformlyAcute.symm hacute) =
        star (spectraDirectRotation U V hacute) :=
  ⟨corollary3_2_sinAngleOperator_symm U V, corollary3_2_reversal_source_form U V hacute⟩

/-! ### Proposition 3.4 at the printed scope

`proposition3_4_square_is_reflected_directRotation` above is true and axiom-clean, but it is
not the printed statement: it exhibits *an* unnamed acute pair, from a whole-space form bound,
under an extra acuteness hypothesis.  The printed statement names the pair `(Q₋ℋ, Qℋ)`, its
hypothesis is `C₀² ≥ ½` on `Pℋ` alone, and it assumes nothing about the reflected pair.  The
three declarations below close each of those gaps, and `proposition3_4_source` is the printed
sentence.
-/

/-- The source diagonal block of the canonical direct rotation is self-adjoint.

`IsPaperDirectRotation` records the diagonal compressions only through their numerical range,
so their self-adjointness -- which the `star`-block calculus needs -- has to be read off the
canonical construction, where the block *is* the positive Halmos cosine. -/
theorem isSelfAdjoint_source_block_spectraDirectRotation
    (hacute : IsUniformlyAcute U V) :
    IsSelfAdjoint (projection U * spectraDirectRotation U V hacute * projection U) := by
  have hC : IsSelfAdjoint
      (spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (spectraOperatorAbsoluteValue_nonneg _)).isSelfAdjoint
  have hcomm : Commute
      (spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)) (projection U) :=
    spectraCanonicalAbsoluteValue_commute_projection U V
  rw [projection_mul_spectraDirectRotation_mul_projection U V hacute]
  rw [IsSelfAdjoint, star_mul, (isSelfAdjoint_starProjection U).star_eq, hC.star_eq]
  exact hcomm.eq.symm

/-- The complementary diagonal block of the canonical direct rotation is self-adjoint. -/
theorem isSelfAdjoint_complement_block_spectraDirectRotation
    (hacute : IsUniformlyAcute U V) :
    IsSelfAdjoint (complementaryProjection U * spectraDirectRotation U V hacute *
      complementaryProjection U) := by
  have hC : IsSelfAdjoint
      (spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (spectraOperatorAbsoluteValue_nonneg _)).isSelfAdjoint
  have hcomm : Commute
      (spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V))
      (complementaryProjection U) := by
    have hcomp : complementaryProjection U = 1 - projection U :=
      Submodule.starProjection_orthogonal' U
    rw [commute_iff_eq, hcomp, mul_sub, mul_one, sub_mul, one_mul,
      (spectraCanonicalAbsoluteValue_commute_projection U V).eq]
  rw [complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection
    U V hacute]
  rw [IsSelfAdjoint, star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, hC.star_eq]
  exact hcomm.eq.symm

/-- **In the acute case a bound on one directed gap transfers to the other.**

The paper's `S₀` and `S₁` are the two crossed blocks of the direct rotation, and Definition
3.1(ii) says `S₁ = S₀⋆`; so they have the same norm, and each of the two directed gaps
`‖P_{Vᗮ} P_U‖`, `‖P_V P_{Uᗮ}‖` equals it.  This is what makes the printed hypothesis
`C₀² ≥ ½`, which constrains only the `Pℋ` block, force the companion bound `C₁² ≥ ½` on
`P̃ℋ` -- an implication that is **false** without a unitary intertwiner: `U ⊆ V` with
`dim V > dim U` has `C₀² = 1` and `C₁²` with `0` in its numerical range.  Equality of the two
directed gaps needs acuteness (`Submodule.projectionGap_eq_max_directedProjectionGap` gives
only the maximum), and this is the acute half of it. -/
theorem norm_projection_apply_le_of_forall_mem_source
    (hacute : IsUniformlyAcute U V) {r : ℝ} (hr : 0 ≤ r)
    (hsrc : ∀ x ∈ U, ‖complementaryProjection V x‖ ≤ r * ‖x‖)
    (w : H) (hw : w ∈ Uᗮ) : ‖projection V w‖ ≤ r * ‖w‖ := by
  set W := spectraDirectRotation U V hacute with hWdef
  have hcross : complementaryProjection U * W * projection U =
      -star (projection U * W * complementaryProjection U) :=
    MathAhead.Section3.spectraDirectRotation_crossed_blocks U V hacute
  obtain ⟨-, -, h12, h21⟩ :=
    star_blocks_eq U W (isSelfAdjoint_source_block_spectraDirectRotation U V hacute)
      (isSelfAdjoint_complement_block_spectraDirectRotation U V hacute) hcross
  set L : H →L[ℂ] H := projection U * W * complementaryProjection U with hLdef
  -- the crossed block of the adjoint is the adjoint of the crossed block
  have hstarL : complementaryProjection U * star W * projection U = star L := by
    rw [h21, hcross, neg_neg]
  have hisom : ∀ z : H, ‖W z‖ = ‖z‖ := norm_spectraDirectRotation_apply U V hacute
  have hconjc : ∀ z : H,
      complementaryProjection V z = W (complementaryProjection U (star W z)) := by
    intro z
    have h := congrArg (fun T : H →L[ℂ] H => T z)
      (spectraDirectRotation_conjugates_complementaryProjection U V hacute)
    simpa only [mul_apply_eq_comp] using h.symm
  have hconj : ∀ z : H, projection V z = W (projection U (star W z)) := by
    intro z
    have h := congrArg (fun T : H →L[ℂ] H => T z)
      (spectraDirectRotation_conjugates_projection U V hacute)
    simpa only [mul_apply_eq_comp] using h.symm
  -- the hypothesis bounds the adjoint crossed block
  have hstarLbound : ∀ y : H, ‖star L y‖ ≤ r * ‖y‖ := by
    intro y
    have hy : star L y = complementaryProjection U (star W (projection U y)) := by
      rw [← hstarL]
      simp only [mul_apply_eq_comp]
    have hval : ‖star L y‖ = ‖complementaryProjection V (projection U y)‖ := by
      rw [hy, hconjc (projection U y), hisom]
    rw [hval]
    refine le_trans (hsrc _ (U.starProjection_apply_mem y)) ?_
    exact mul_le_mul_of_nonneg_left (U.norm_starProjection_apply_le y) hr
  have hLnorm : ‖L‖ ≤ r := by
    rw [← norm_star L]
    exact ContinuousLinearMap.opNorm_le_bound _ hr hstarLbound
  -- and the other directed gap is read off the same block
  have hwc : complementaryProjection U w = w :=
    Submodule.starProjection_eq_self_iff.mpr hw
  have hval : projection V w = W (-(L w)) := by
    rw [hconj w]
    have hy : projection U (star W w) =
        (projection U * star W * complementaryProjection U) w := by
      simp only [mul_apply_eq_comp, hwc]
    rw [hy, h12]
    simp only [neg_apply]
  rw [hval, hisom, norm_neg]
  exact le_trans (L.le_opNorm w) (mul_le_mul_of_nonneg_right hLnorm (norm_nonneg w))

omit [CompleteSpace H] in
/-- The cosine-square quadratic form, block by block: `⟪x, cos²Θ x⟫` is
`‖P_V P_U x‖² + ‖P_{Vᗮ} P_{Uᗮ} x‖²`. -/
theorem re_inner_halmosCosineSq_self (x : H) :
    RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ =
      ‖projection V (projection U x)‖ ^ 2 +
        ‖complementaryProjection V (complementaryProjection U x)‖ ^ 2 := by
  have hval : halmosCosineSq U V x =
      projection U (projection V (projection U x)) +
        complementaryProjection U
          (complementaryProjection V (complementaryProjection U x)) := by
    show (projection U * projection V * projection U +
      complementaryProjection U * complementaryProjection V *
        complementaryProjection U) x = _
    simp only [add_apply, mul_apply_eq_comp]
  have hblock : ∀ (K : Submodule ℂ H) [K.HasOrthogonalProjection]
      (M : Submodule ℂ H) [M.HasOrthogonalProjection],
      RCLike.re ⟪x, projection K (projection M (projection K x))⟫_ℂ =
        ‖projection M (projection K x)‖ ^ 2 := by
    intro K _ M _
    have hsym : ⟪x, projection K (projection M (projection K x))⟫_ℂ =
        ⟪projection K x, projection M (projection K x)⟫_ℂ :=
      (K.starProjection_isSymmetric x (projection M (projection K x))).symm
    have hself : ⟪projection M (projection K x), projection K x⟫_ℂ =
        ((‖projection M (projection K x)‖ : ℝ) : ℂ) ^ 2 :=
      inner_starProjection_self_eq M (projection K x)
    rw [hsym, inner_re_symm, hself]
    norm_cast
  rw [hval, inner_add_right, map_add, hblock U V, hblock Uᗮ Vᗮ]

/-- **The printed half-angle hypothesis implies the whole-space form bound.**

Davis and Kahan write `C₀² ≥ ½`, an inequality between operators on `X(E₀) = Pℋ` -- by
equation (3.7), `C₀² = E₀⋆ Q E₀`, so its quadratic form at `x ∈ Pℋ` is `‖Qx‖²`, and the
printed inequality is exactly `hcos`.  What the accretivity argument needs is the same bound
for `cos²Θ` on all of `ℋ`, which adds the companion `C₁² ≥ ½` on `P̃ℋ`; that companion is
*not* a consequence of `hcos` for an arbitrary pair, and is one here because the acute case
supplies a unitary intertwiner whose two crossed blocks are adjoint
(`norm_projection_apply_le_of_forall_mem_source`). -/
theorem re_inner_halmosCosineSq_sub_half_nonneg_of_source
    (hacute : IsUniformlyAcute U V)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖projection V x‖ ^ 2) (x : H) :
    0 ≤ RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2 := by
  have hroot : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hrootsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h2]
    norm_num
  have hsrc : ∀ y ∈ U, ‖complementaryProjection V y‖ ≤ (Real.sqrt 2 / 2) * ‖y‖ := by
    intro y hy
    have hpy : ‖y‖ ^ 2 =
        ‖projection V y‖ ^ 2 + ‖complementaryProjection V y‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection y V
    have h1 := hcos y hy
    have hsq : ‖complementaryProjection V y‖ ^ 2 ≤ ((Real.sqrt 2 / 2) * ‖y‖) ^ 2 := by
      rw [mul_pow, hrootsq]
      linarith
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Real.sqrt 2 / 2) * ‖y‖)] at hle
  have htgt : ∀ w ∈ Uᗮ, ‖projection V w‖ ≤ (Real.sqrt 2 / 2) * ‖w‖ := fun w hw =>
    norm_projection_apply_le_of_forall_mem_source U V hacute hroot hsrc w hw
  have hx : ‖x‖ ^ 2 =
      ‖projection U x‖ ^ 2 + ‖complementaryProjection U x‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection x U
  have hU : ‖projection U x‖ ^ 2 / 2 ≤ ‖projection V (projection U x)‖ ^ 2 :=
    hcos _ (U.starProjection_apply_mem x)
  have hUc : ‖complementaryProjection U x‖ ^ 2 / 2 ≤
      ‖complementaryProjection V (complementaryProjection U x)‖ ^ 2 := by
    have hw := htgt _ (Uᗮ.starProjection_apply_mem x)
    have hpy : ‖complementaryProjection U x‖ ^ 2 =
        ‖projection V (complementaryProjection U x)‖ ^ 2 +
          ‖complementaryProjection V (complementaryProjection U x)‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection _ V
    have hsq : ‖projection V (complementaryProjection U x)‖ ^ 2 ≤
        1 / 2 * ‖complementaryProjection U x‖ ^ 2 := by
      have h := mul_self_le_mul_self (norm_nonneg
        (projection V (complementaryProjection U x))) hw
      rw [← pow_two, ← pow_two, mul_pow, hrootsq] at h
      exact h
    linarith
  rw [re_inner_halmosCosineSq_self U V x]
  linarith

omit [CompleteSpace H] in
/-- The reflection through a subspace fixes its own projection, on the left. -/
theorem reflectionOperator_mul_projection_self :
    reflectionOperator V * projection V = projection V := by
  rw [reflectionOperator_eq_projection_add_projection_sub_one V]
  have hPV2 := projection_sq V
  noncomm_ring [hPV2]

omit [CompleteSpace H] in
/-- The reflection through a subspace fixes its own projection, on the right. -/
theorem projection_mul_reflectionOperator_self :
    projection V * reflectionOperator V = projection V := by
  rw [reflectionOperator_eq_projection_add_projection_sub_one V]
  have hPV2 := projection_sq V
  noncomm_ring [hPV2]

/-- An operator whose numerical range is nonnegative has positive Hermitian part. -/
theorem nonneg_add_star_of_re_inner_nonneg (T : H →L[ℂ] H)
    (hre : ∀ x : H, 0 ≤ RCLike.re ⟪T x, x⟫_ℂ) :
    (0 : H →L[ℂ] H) ≤ T + star T := by
  refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun x => ?_⟩
  · rw [IsSelfAdjoint, star_add, star_star, add_comm]
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have hstar : RCLike.re ⟪star T x, x⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      exact inner_re_symm x (T x)
    have hsplit : RCLike.re ⟪(T + star T) x, x⟫_ℂ =
        RCLike.re ⟪T x, x⟫_ℂ + RCLike.re ⟪star T x, x⟫_ℂ := by
      rw [add_apply, inner_add_left, map_add]
    rw [hsplit, hstar]
    have := hre x
    linarith

/-- **Davis--Kahan 1970, Proposition 3.4, as printed.**

> If `C₀² ≥ ½`, then `U²` is the direct rotation of `Q₋ℋ` to `Qℋ`.

Every clause is the printed one.  `Q₋ = XQX` is the mirror image of the target in the source
(`reflectedSubspace U V`, whose projection is `R_U P_V R_U`); the conclusion is Definition 3.1
for the ordered pair `(Q₋ℋ, Qℋ)` -- the paper's own proof verifies exactly its clauses (i) and
(ii) plus the intertwining `U²Q₋ = QU²`; and `hcos` is `C₀² ≥ ½` read through equation (3.7),
`C₀² = E₀⋆ Q E₀`, so its quadratic form at `x ∈ Pℋ` is `‖Qx‖²`.

Three narrowings of `proposition3_4_square_is_reflected_directRotation` are removed.  That
statement exhibits an existential pair rather than the printed `(Q₋ℋ, Qℋ)`; assumes the
symmetrized whole-space form bound rather than the printed `Pℋ` one; and carries an extra
`IsUniformlyAcute U (reflectedSubspace V U)`.  The extra acuteness is genuinely not available
here -- at the boundary `C₀² = ½` the reflected pair has gap one -- and is not needed: the
crossed-intersection mapping condition of Proposition 3.3 holds for every unitary square root
of the reflection product that intertwines the projections
(`crossedDefect_image_of_unitary_sq`), so the nonacute converse applies unchanged.  Acuteness
of the *original* pair is retained because it is what `spectraDirectRotation U V` is indexed
by, and because the companion bound `C₁² ≥ ½` is false without an intertwiner.

Grounded by `:=` on `proposition3_3_principalSquareRoot_converse`, so no square-root branch
argument is duplicated. -/
theorem proposition3_4_source (hacute : IsUniformlyAcute U V)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖projection V x‖ ^ 2) :
    IsPaperDirectRotation (reflectedSubspace U V) V
      (spectraDirectRotation U V hacute * spectraDirectRotation U V hacute) := by
  set W := spectraDirectRotation U V hacute with hWdef
  have hWunit : W ∈ unitary (H →L[ℂ] H) := spectraDirectRotation_mem_unitary U V hacute
  have hTunit : W * W ∈ unitary (H →L[ℂ] H) := mul_mem hWunit hWunit
  have hWsq : W * W = reflectionOperator V * reflectionOperator U :=
    spectraDirectRotation_sq U V hacute
  have hrefl : reflectionOperator (reflectedSubspace U V)
      = reflectionOperator U * reflectionOperator V * reflectionOperator U :=
    reflectionOperator_reflectedSubspace V U
  have hRU : reflectionOperator U * reflectionOperator U = 1 :=
    reflectionOperator_mul_self_complex U
  have hsq : (W * W) * (W * W) = spectraReflectionProduct (reflectedSubspace U V) V := by
    show (W * W) * (W * W)
      = reflectionOperator V * reflectionOperator (reflectedSubspace U V)
    rw [hrefl, hWsq]
    noncomm_ring
  -- the printed `U²Q₋ = QU²`
  have hint : (W * W) * projection (reflectedSubspace U V)
      = projection V * (W * W) := by
    have hPref : projection (reflectedSubspace U V)
        = reflectionOperator U * projection V * reflectionOperator U :=
      starProjection_reflectedSubspace U V
    rw [hPref, hWsq]
    calc reflectionOperator V * reflectionOperator U *
          (reflectionOperator U * projection V * reflectionOperator U)
        = reflectionOperator V * (reflectionOperator U * reflectionOperator U) *
            (projection V * reflectionOperator U) := by noncomm_ring
      _ = reflectionOperator V * projection V * reflectionOperator U := by
            rw [hRU, mul_one, mul_assoc]
      _ = projection V * reflectionOperator U := by
            rw [reflectionOperator_mul_projection_self V]
      _ = (projection V * reflectionOperator V) * reflectionOperator U := by
            rw [projection_mul_reflectionOperator_self V]
      _ = projection V * (reflectionOperator V * reflectionOperator U) := by
            rw [mul_assoc]
  have hre : ∀ x : H, 0 ≤ RCLike.re ⟪(W * W) x, x⟫_ℂ := by
    intro x
    rw [hWsq]
    exact re_inner_reflectionProduct_nonneg U V
      (re_inner_halmosCosineSq_sub_half_nonneg_of_source U V hacute hcos) x
  have hspec := spectrum_re_nonneg_of_nonneg_add_star (W * W) hTunit
    (nonneg_add_star_of_re_inner_nonneg (W * W) hre)
  exact proposition3_3_principalSquareRoot_converse (reflectedSubspace U V) V (W * W)
    ⟨hTunit, hsq, hspec⟩
    (crossedDefect_image_of_unitary_sq (reflectedSubspace U V) V (W * W) hTunit hsq hint)

/-- **Proposition 3.4 with the printed definite article.**

"*the* direct rotation" presupposes uniqueness, which Proposition 3.1 supplies exactly when
the reflected pair is acute.  Under that additional hypothesis the square is the canonical
direct rotation of `(Q₋ℋ, Qℋ)` on the nose.  Without it `proposition3_4_source` still holds:
the square satisfies Definition 3.1, and by Proposition 3.2 it is then one of possibly
several direct rotations. -/
theorem proposition3_4_source_eq_directRotation (hacute : IsUniformlyAcute U V)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖projection V x‖ ^ 2)
    (hacuteRef : IsUniformlyAcute (reflectedSubspace U V) V) :
    spectraDirectRotation U V hacute * spectraDirectRotation U V hacute
      = spectraDirectRotation (reflectedSubspace U V) V hacuteRef := by
  set W := spectraDirectRotation U V hacute with hWdef
  have hWunit : W ∈ unitary (H →L[ℂ] H) := spectraDirectRotation_mem_unitary U V hacute
  have hTunit : W * W ∈ unitary (H →L[ℂ] H) := mul_mem hWunit hWunit
  have hWsq : W * W = reflectionOperator V * reflectionOperator U :=
    spectraDirectRotation_sq U V hacute
  have hrefl : reflectionOperator (reflectedSubspace U V)
      = reflectionOperator U * reflectionOperator V * reflectionOperator U :=
    reflectionOperator_reflectedSubspace V U
  have hsq : (W * W) * (W * W) = spectraReflectionProduct (reflectedSubspace U V) V := by
    show (W * W) * (W * W)
      = reflectionOperator V * reflectionOperator (reflectedSubspace U V)
    rw [hrefl, hWsq]
    noncomm_ring
  refine spectraDirectRotation_unique_of_sq (reflectedSubspace U V) V hacuteRef
    (W * W) hTunit hsq ?_
  intro x
  rw [hWsq]
  exact re_inner_reflectionProduct_nonneg U V
    (re_inner_halmosCosineSq_sub_half_nonneg_of_source U V hacute hcos) x

end OneSpace

/-! ## Proposition 3.2, the nonacute existence criterion

Stated over an arbitrary `RCLike` field.  Nothing in the nonacute construction
is complex-specific: the crossed-defect quarter turn is built out of the polar
factor of `Q P + Qᗮ Pᗮ`, and the only field-dependent ingredient is the
continuous functional calculus that the modulus runs on, carried here as a
hypothesis exactly as `ForTauCeti`'s modulus API carries it.  Typeclass
inference discharges it at `𝕜 = ℂ` and, through
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, at
`𝕜 = ℝ`.

These statements used to live in `section OneSpace` above, over `ℂ`.  They were
moved rather than duplicated: `section OneSpace` also carries Propositions 3.3
and 3.5, whose square-root branch selection is genuinely complex
(`spectrum ℂ T` and `ComplexOrder`), so the two groups cannot share one variable
block. -/

section NonacuteExistence

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

/-- Davis--Kahan 1970, Proposition 3.2: a nonacute direct rotation exists
exactly when the crossed defect spaces have equal Hilbert dimension, expressed
constructively by a linear isometric equivalence. -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent :
    (∃ T : H →L[𝕜] H, IsPaperDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V :=
  MathAhead.HiddenFoundations.proposition3_2_completed U V

/-- Explicit parameterization of the freedom in Proposition 3.2.  Distinct
unitaries between the crossed defect spaces must produce distinct direct
rotations. -/
theorem proposition3_2_parameterized_nonuniqueness
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) →
          (H →L[𝕜] H),
      (∀ J, IsPaperDirectRotation U V (build J)) ∧
      Function.Injective build :=
  MathAhead.HiddenFoundations.proposition3_2_parameterization_completed U V hdefect

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **In the nonacute case the crossed defect spaces are nonzero.**

The paper's Definition 3.2 declares the pair acute exactly when both crossed
intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` vanish, so failing to be acute makes at
least one of them nonzero; the isometry supplied by (3.5) then transports that
to the source defect. -/
theorem halmosSourceDefect_ne_bot_of_not_isAcute
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    halmosSourceDefect U V ≠ ⊥ := by
  obtain ⟨J⟩ := hdefect
  intro hbot
  refine hnonacute (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mpr ⟨hbot, ?_⟩)
  refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
  have hzero : ((J.symm ⟨y, hy⟩ : halmosSourceDefect U V) : H) = 0 :=
    (Submodule.eq_bot_iff _).mp hbot _ (J.symm ⟨y, hy⟩).2
  have hsymm : (J.symm ⟨y, hy⟩ : halmosSourceDefect U V) = 0 := Subtype.ext hzero
  have htarget : (⟨y, hy⟩ : halmosTargetDefect U V) = 0 := by
    have h := congrArg J hsymm
    rwa [J.apply_symm_apply, map_zero] at h
  exact congrArg Subtype.val htarget

/-- **Davis--Kahan 1970, Proposition 3.2, second printed sentence: "It is not
unique."**

In the nonacute case a direct rotation, once it exists, is never unique.  The
witnesses are produced by feeding an isometry `J` of the crossed defect spaces
and its negation `-J` through the injective parameterization
`proposition3_2_parameterized_nonuniqueness`.  Over a field of characteristic
zero `J ≠ -J` requires a nonzero defect space, and that is supplied by the
nonacute hypothesis rather than assumed separately: the paper's acute case is
precisely the vanishing of both crossed intersections.

This is the paper's own reason for the nonuniqueness -- "This extension is not
unique (even if `dim Null(C₀) = 1`), and the nonuniqueness will survive" -- with
the arbitrary unitary extension replaced by the single sign change, which is
enough to refute uniqueness. -/
theorem proposition3_2_not_unique
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ∃ T₁ T₂ : H →L[𝕜] H,
      IsPaperDirectRotation U V T₁ ∧ IsPaperDirectRotation U V T₂ ∧ T₁ ≠ T₂ := by
  obtain ⟨build, hbuild, hinj⟩ :=
    proposition3_2_parameterized_nonuniqueness U V hdefect
  obtain ⟨J⟩ := hdefect
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.ne_bot_iff _ |>.mp
      (halmosSourceDefect_ne_bot_of_not_isAcute U V ⟨J⟩ hnonacute)
  refine ⟨build J, build (J.trans (LinearIsometryEquiv.neg 𝕜)), hbuild _, hbuild _, ?_⟩
  intro hEq
  have hJJ : J = J.trans (LinearIsometryEquiv.neg 𝕜) := hinj hEq
  have hval : J ⟨x, hxmem⟩ = -J ⟨x, hxmem⟩ :=
    congrArg (fun e : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V =>
      e ⟨x, hxmem⟩) hJJ
  have hsrc : (⟨x, hxmem⟩ : halmosSourceDefect U V) = -⟨x, hxmem⟩ := by
    refine J.injective ?_
    rw [map_neg]
    exact hval
  have htwo : (2 : 𝕜) • (⟨x, hxmem⟩ : halmosSourceDefect U V) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hsrc
  rcases smul_eq_zero.mp htwo with h2 | hx0
  · exact absurd h2 two_ne_zero
  · exact hxne (congrArg Subtype.val hx0)

/-- **Proposition 3.2's nonuniqueness in literal `∃!` form.** -/
theorem proposition3_2_not_existsUnique
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ¬ ∃! T : H →L[𝕜] H, IsPaperDirectRotation U V T := by
  rintro ⟨T, _, huniq⟩
  obtain ⟨T₁, T₂, h₁, h₂, hne⟩ := proposition3_2_not_unique U V hdefect hnonacute
  exact hne ((huniq T₁ h₁).trans (huniq T₂ h₂).symm)
end NonacuteExistence

/-! ## Theorem 3.1, the operator-level classification

Stated over an arbitrary `RCLike` field.  Nothing in the Halmos spine is
complex-specific; the only field-dependent ingredient is the continuous
functional calculus used by the polar decomposition of the cross block, and it
is carried as a hypothesis exactly as `ForTauCeti`'s modulus API carries it. -/

section OperatorClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- Equality of the four elementary Halmos summands, expressed without a
finite-rank substitute. -/
structure SameHalmosTrivialDimensions : Prop where
  common : Nonempty
    (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty
    (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)

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

/-! ### Corollary 3.1 with the printed compactness hypothesis

Davis and Kahan assume `P tilde(Q) P = P (I - Q) P` compact -- the *defect*
(sine-square) block -- not `P Q P`.  In infinite dimension the two are
incomparable: `P(I-Q)P` compact says the principal angles accumulate only at
`0`, while `PQP` compact says they accumulate only at `pi/2`, and neither
implies the other unless `P` itself is compact.

The repair is exact rather than approximate, because `P (I - Q) P = P P_{Vᗮ} P`:
the defect block of the pair `(U, V)` *is* the cosine block of the pair
`(U, Vᗮ)`.  So the printed corollary is the compiled one applied to
`(U, Vᗮ)`, once one knows that complementing the second subspace preserves
pair-equivalence and merely permutes the four elementary Halmos summands.
-/

variable {U₁ V₁ U₂ V₂}

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] in
/-- Complementing the second subspace of each pair preserves unitary
equivalence of ordered pairs. -/
theorem pairOfSubspacesUnitaryEquivalent_orthogonal_right
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ᗮ U₂ V₂ᗮ := by
  obtain ⟨e, hU, hV⟩ := h
  refine ⟨e, hU, ?_⟩
  have hmap : V₁ᗮ.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) =
      (V₁.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂))ᗮ :=
    Submodule.map_orthogonal_equiv V₁ e
  have hcoe : (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) = e.toLinearMap := rfl
  rw [hcoe] at hmap
  rw [hmap, hV]

variable (U₁ V₁ U₂ V₂)

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [U₂.HasOrthogonalProjection] in
theorem pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ᗮ U₂ V₂ᗮ ↔
      PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ := by
  refine ⟨fun h => ?_, pairOfSubspacesUnitaryEquivalent_orthogonal_right⟩
  have h' := pairOfSubspacesUnitaryEquivalent_orthogonal_right h
  rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at h'

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Transport a nonempty isometric equivalence of submodules along equalities
of those submodules.  Needed because the two summand families below are equal
as submodules but the `≃ₗᵢ` type former does not rewrite. -/
private theorem nonempty_linearIsometryEquiv_congr
    {X X' : Submodule 𝕜 H₁} {Y Y' : Submodule 𝕜 H₂}
    (hX : X = X') (hY : Y = Y') (h : Nonempty (X ≃ₗᵢ[𝕜] Y)) :
    Nonempty (X' ≃ₗᵢ[𝕜] Y') :=
  h.map fun f =>
    ((LinearIsometryEquiv.ofEq X' X hX.symm).trans f).trans
      (LinearIsometryEquiv.ofEq Y Y' hY)

omit [U₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection] [CompleteSpace H₁]
  [CompleteSpace H₂] in
/-- Complementing the second subspace permutes the four elementary Halmos
summands: `U ⊓ V` swaps with `U ⊓ Vᗮ`, and `Uᗮ ⊓ V` with `Uᗮ ⊓ Vᗮ`. -/
theorem sameHalmosTrivialDimensions_orthogonal_right_iff :
    SameHalmosTrivialDimensions U₁ V₁ᗮ U₂ V₂ᗮ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ := by
  have hVV1 : V₁ᗮᗮ = V₁ := Submodule.orthogonal_orthogonal V₁
  have hVV2 : V₂ᗮᗮ = V₂ := Submodule.orthogonal_orthogonal V₂
  have e1 : U₁ ⊓ V₁ᗮᗮ = U₁ ⊓ V₁ := by rw [hVV1]
  have e2 : U₂ ⊓ V₂ᗮᗮ = U₂ ⊓ V₂ := by rw [hVV2]
  have e3 : U₁ᗮ ⊓ V₁ᗮᗮ = U₁ᗮ ⊓ V₁ := by rw [hVV1]
  have e4 : U₂ᗮ ⊓ V₂ᗮᗮ = U₂ᗮ ⊓ V₂ := by rw [hVV2]
  constructor
  · rintro ⟨hc, hs, ht, he⟩
    exact ⟨nonempty_linearIsometryEquiv_congr e1 e2 hs, hc,
      nonempty_linearIsometryEquiv_congr e3 e4 he, ht⟩
  · rintro ⟨hc, hs, ht, he⟩
    exact ⟨hs, nonempty_linearIsometryEquiv_congr e1.symm e2.symm hc,
      he, nonempty_linearIsometryEquiv_congr e3.symm e4.symm ht⟩

/-! The converse direction reconstructs the pair from the cosine block through the
polar decomposition of the Halmos cross block, so it carries the functional-calculus
hypotheses of `Geometry/Halmos/GenericReconstruction.lean`.  They are found by typeclass
inference at `𝕜 = ℂ` and at `𝕜 = ℝ` alike. -/

variable [Algebra ℝ (MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁)]
  [IsScalarTower ℝ 𝕜 (MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁)]
  [ContinuousFunctionalCalculus ℝ
    (MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ →L[𝕜]
      MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁) IsSelfAdjoint]
variable [Algebra ℝ (MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂)]
  [IsScalarTower ℝ 𝕜 (MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂)]
  [ContinuousFunctionalCalculus ℝ
    (MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ →L[𝕜]
      MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂) IsSelfAdjoint]

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

/-! ### Corollary 3.1, the decreasing eigenvalue list

The paper's Corollary 3.1 replaces the operator invariant of Theorem 3.1 by the
*decreasing eigenvalue list* of the angle operator.  Everything here is stated
over an arbitrary `RCLike` field, exactly like the operator-level spine above:
the eigenvalues of a compact positive self-adjoint operator are real, so the
list is `ℝ`-valued whatever the scalar field is, and only the embedding of an
eigenvalue back into the field changes with `𝕜`. -/

/-- Ordered eigenvalue data for a compact positive contraction: the
approximation-number sequence of `A`.

For a compact **positive** operator this is exactly the ordered eigenvalue list
*with multiplicity* — `aₙ(A)` is the `n`-th largest singular value, and singular
values coincide with eigenvalues when the operator is positive, so a repeated
eigenvalue is repeated in the sequence.  That is the implementation this
declaration's earlier open body was documented as wanting.

The list is `ℝ`-valued over every scalar field, because the eigenvalues of a
compact positive self-adjoint operator are real.

Note the definition is total: it is stated for every `A`, and only *means* the
angle eigenvalue list under the compactness and positivity hypotheses that the
consumers carry.  This mirrors `approximationNumber` itself, which is total in
the same way. -/
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] (A : K →L[𝕜] K) : ℕ → ℝ :=
  fun n => A.approximationNumber n

/-- **Approximation numbers are a unitary invariant.**  Conjugating by a linear isometric
equivalence sandwiches the operator between two contractions in both directions, so no
approximation number can move. -/
theorem approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (h : BoundedOperatorsUnitaryEquivalent A B) (n : ℕ) :
    A.approximationNumber n = B.approximationNumber n := by
  obtain ⟨U, hU⟩ := h
  have hUapp : ∀ x, B (U x) = U (A x) := fun x => (hU x).symm
  have hUnorm : ‖(U : E →L[𝕜] F)‖ ≤ 1 :=
    U.toLinearIsometry.norm_toContinuousLinearMap_le
  have hUsnorm : ‖(U.symm : F →L[𝕜] E)‖ ≤ 1 :=
    U.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  have hBfact : B = (U : E →L[𝕜] F) ∘L A ∘L (U.symm : F →L[𝕜] E) := by
    ext y
    change B y = U (A (U.symm y))
    rw [← hUapp (U.symm y), U.apply_symm_apply]
  have hAfact : A = (U.symm : F →L[𝕜] E) ∘L B ∘L (U : E →L[𝕜] F) := by
    ext x
    change A x = U.symm (B (U x))
    rw [hUapp x, U.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [hAfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U.symm : F →L[𝕜] E) (U : E →L[𝕜] F) hUsnorm hUnorm n
  · conv_lhs => rw [hBfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U : E →L[𝕜] F) (U.symm : F →L[𝕜] E) hUnorm hUsnorm n

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
      ⟪MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁ x, x⟫_𝕜 := by
    intro x
    rw [MathAhead.HiddenFoundations.re_inner_genericCosineBlock]
    positivity
  have hpos₂ : ∀ x, 0 ≤ RCLike.re
      ⟪MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂ x, x⟫_𝕜 := by
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

end OperatorClassification

/-! ## Corollary 3.1 with the printed compactness hypothesis, over an arbitrary field

The defect-block form of Corollary 3.1 is the cosine-block form applied to `(U, Vᗮ)`, so it
is field-generic exactly as that form is.  It is separated from `section
OperatorClassification` only because the reconstruction functional calculus it needs is the
one on the generic left half of `(U, Vᗮ)`, while that section's calculus variables are
pinned to `(U, V)`; carrying both would attach four hypotheses that this statement never
uses. -/

section DefectBlockClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

variable [Algebra ℝ (MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ᗮ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ᗮ)]
  [IsScalarTower ℝ 𝕜 (MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ᗮ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ᗮ)]
  [ContinuousFunctionalCalculus ℝ
    (MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ᗮ →L[𝕜]
      MathAhead.HiddenFoundations.genericLeftHalf U₁ V₁ᗮ) IsSelfAdjoint]
variable [Algebra ℝ (MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ᗮ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ᗮ)]
  [IsScalarTower ℝ 𝕜 (MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ᗮ →L[𝕜]
    MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ᗮ)]
  [ContinuousFunctionalCalculus ℝ
    (MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ᗮ →L[𝕜]
      MathAhead.HiddenFoundations.genericLeftHalf U₂ V₂ᗮ) IsSelfAdjoint]

/-- **Davis--Kahan 1970, Corollary 3.1, with the printed hypothesis.**

The compactness assumption is on the *defect* block `P (I - Q) P`, as printed,
and the classifying list is the eigenvalue list of the corresponding
sine-square angle operator. -/
theorem corollary3_1_compact_defectBlock_angleList_classification
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L
        (ContinuousLinearMap.id 𝕜 H₁ - projection V₁) ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L
        (ContinuousLinearMap.id 𝕜 H₂ - projection V₂) ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂ᗮ) := by
  have hperp₁ : projection V₁ᗮ =
      ContinuousLinearMap.id 𝕜 H₁ - projection V₁ := by
    show V₁ᗮ.starProjection = ContinuousLinearMap.id 𝕜 H₁ - V₁.starProjection
    rw [Submodule.starProjection_orthogonal' V₁]
    rfl
  have hperp₂ : projection V₂ᗮ =
      ContinuousLinearMap.id 𝕜 H₂ - projection V₂ := by
    show V₂ᗮ.starProjection = ContinuousLinearMap.id 𝕜 H₂ - V₂.starProjection
    rw [Submodule.starProjection_orthogonal' V₂]
    rfl
  have h₁ : IsCompactOperator (projection U₁ ∘L projection V₁ᗮ ∘L projection U₁) := by
    rwa [hperp₁]
  have h₂ : IsCompactOperator (projection U₂ ∘L projection V₂ᗮ ∘L projection U₂) := by
    rwa [hperp₂]
  rw [← pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff U₁ V₁ U₂ V₂,
    ← sameHalmosTrivialDimensions_orthogonal_right_iff U₁ V₁ U₂ V₂]
  exact corollary3_1_compact_angleList_classification U₁ V₁ᗮ U₂ V₂ᗮ h₁ h₂

end DefectBlockClassification


/-! ## From the generic cosine block to the ambient block

Corollary 3.1's classifying invariant is the eigenvalue list of the *generic* cosine
block `genericCosineBlock U V`, an operator on the `U`-half of the generic part, while a
realization is naturally computed for the *ambient* block `P_U P_V P_U` on the whole
space.  When the four elementary Halmos summands are trivial the two carry the same
eigenvalue list, because the generic part is then everything and the ambient block is the
extension of the generic block by zero off `U`. -/

section GenericAmbientBridge

open MathAhead.HiddenFoundations

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- With the four elementary Halmos summands trivial, the generic part is everything and
the `U`-half of it is `U` itself. -/
theorem genericLeftHalf_eq_of_halmosTrivialPart_eq_bot
    (h : halmosTrivialPart U V = ⊥) : genericLeftHalf U V = U := by
  have hgen : halmosGenericPart U V = ⊤ := by
    show (halmosTrivialPart U V)ᗮ = ⊤
    rw [h]
    exact Submodule.bot_orthogonal_eq_top
  show U ⊓ halmosGenericPart U V = U
  rw [hgen, inf_top_eq]

/-- The orthogonal projection onto the `U`-half of the generic part is the projection onto
`U` when the four elementary Halmos summands are trivial. -/
theorem starProjection_genericLeftHalf_eq_of_halmosTrivialPart_eq_bot
    (h : halmosTrivialPart U V = ⊥) (x : H) :
    (genericLeftHalf U V).starProjection x = U.starProjection x :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h).ge (U.starProjection_apply_mem x))
    fun w hw =>
      Submodule.starProjection_inner_eq_zero x w
        ((genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h).le hw)

/-- **The ambient block is the generic cosine block extended by zero.**

`genericCosineBlock U V` is the compression of `P_V` to the `U`-half of the generic part;
when the four elementary Halmos summands are trivial that half is `U`, and transporting the
block back to the ambient space by the inclusion and the orthogonal projection reproduces
`P_U P_V P_U` exactly. -/
theorem subtypeL_comp_genericCosineBlock_comp_orthogonalProjectionOnto
    (h : halmosTrivialPart U V = ⊥) :
    (genericLeftHalf U V).subtypeL ∘L genericCosineBlock U V ∘L
        (genericLeftHalf U V).orthogonalProjectionOnto =
      U.starProjection ∘L V.starProjection ∘L U.starProjection := by
  have hproj := starProjection_genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h
  refine ContinuousLinearMap.ext fun x => ?_
  have hcoe : ∀ m : genericLeftHalf U V,
      ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
        (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := fun m => by
    simp [genericCosineBlock, DavisKahanExt.compressOperator]
  calc ((genericLeftHalf U V).subtypeL ∘L genericCosineBlock U V ∘L
          (genericLeftHalf U V).orthogonalProjectionOnto) x
      = (genericLeftHalf U V).starProjection
          (V.starProjection ((genericLeftHalf U V).starProjection x)) :=
        hcoe ((genericLeftHalf U V).orthogonalProjectionOnto x)
    _ = U.starProjection (V.starProjection (U.starProjection x)) := by
        rw [hproj, hproj]
    _ = (U.starProjection ∘L V.starProjection ∘L U.starProjection) x := rfl

/-- **The bridge between Corollary 3.1's two cosine blocks.**

The generic cosine block and the ambient block `P_U P_V P_U` have the same
approximation-number sequence — hence the same `compactAngleEigenvalueList` — whenever the
four elementary Halmos summands are trivial.

Mathematically this is "extension by zero preserves approximation numbers": off the generic
part the ambient block vanishes, so the two operators carry the same nonzero singular data.
The general fact is
`TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto`;
nothing about angles is reproved here. -/
theorem approximationNumber_genericCosineBlock_eq_ambient
    (h : halmosTrivialPart U V = ⊥) (n : ℕ) :
    (genericCosineBlock U V).approximationNumber n =
      (U.starProjection ∘L V.starProjection ∘L U.starProjection).approximationNumber n := by
  rw [← subtypeL_comp_genericCosineBlock_comp_orthogonalProjectionOnto U V h,
    TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto
      (genericLeftHalf U V) (genericCosineBlock U V) n]

/-- The `compactAngleEigenvalueList` form of
`approximationNumber_genericCosineBlock_eq_ambient`. -/
theorem compactAngleEigenvalueList_genericCosineBlock_eq_ambient
    (h : halmosTrivialPart U V = ⊥) :
    compactAngleEigenvalueList (genericCosineBlock U V) =
      compactAngleEigenvalueList
        (U.starProjection ∘L V.starProjection ∘L U.starProjection) :=
  funext fun n => approximationNumber_genericCosineBlock_eq_ambient U V h n

end GenericAmbientBridge

section Classification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-! Instantiating the field-generic Halmos classification at `𝕜 = ℂ` asks typeclass
inference for `ContinuousFunctionalCalculus ℝ (M →L[ℂ] M) IsSelfAdjoint` with `M` the
`U`-half of the generic part.  Mathlib supplies it through the C⋆-algebra structure on
bounded operators, but reaching it from a subspace coercion needs one more level of
pending synthesis than the default allows; the instance is found at depth `3`. -/
set_option maxSynthPendingDepth 3

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
it is one of the paper's **standing assumptions**, taken from the Introduction and Sections 1--2
and so governing Section 3; see `prose/distilled_literature/DavisKahan1970_part_III.tex`,
*Standing assumptions from the transcription*.  It is needed for `→` alone -- producing a
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

/-- **Davis--Kahan 1970, Corollary 3.1 with the printed hypothesis, over a complex Hilbert
space.**

The `𝕜 = ℂ` instance of `corollary3_1_compact_defectBlock_angleList_classification`,
grounded on it by `:=`, with no added hypothesis.

It is recorded separately because the generic form *carries* the reconstruction functional
calculus on `↥(genericLeftHalf U Vᗮ)` as a hypothesis, and typeclass inference finds that
instance for an arbitrary pair but not at every concrete one.  A consumer that instantiates
the corollary at a specific pair therefore goes through this form, where the instance was
already discharged. -/
theorem corollary3_1_compact_defectBlock_angleList_classification_complex
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L
        (ContinuousLinearMap.id ℂ H₁ - projection V₁) ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L
        (ContinuousLinearMap.id ℂ H₂ - projection V₂) ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂ᗮ) :=
  corollary3_1_compact_defectBlock_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂


end Classification

/-! ## Theorem 3.1, the realization half -/

section Realization

open MathAhead.HiddenFoundations

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Davis--Kahan 1970, Theorem 3.1, the realization half — the paper's sentence
(ii).**

The classification half (`twoProjection_operator_classification`,
`theorem3_1_spectralMultiplicity_classification`) says that the angle datum
determines the pair.  This says the converse of the *existence* kind: every
admissible angle datum is *attained*.  Given `cos Θ₀, sin Θ₀` on `E`,
`cos Θ₁, sin Θ₁` on `F` and the intertwiner `J₀` that matches their spectral
multiplicities away from the angle `0`, the two subspaces

`U = E`-factor,  `V = W₀ E` with `W₀ x = (cos Θ₀ x, J₀ sin Θ₀ x)`

of `E ⊕₂ F` satisfy, in order:

1. the compression of `P_V` to `U` is `cos² Θ₀`;
2. the compression of `P_Vᗮ` to `Uᗮ` is `cos² Θ₁`;
3. `U ⊓ V` is the angle-`0` eigenspace on the `P`-side;
4. `Uᗮ ⊓ Vᗮ` is the angle-`0` eigenspace on the `Pᗮ`-side;
5. `U ⊓ Vᗮ` is the angle-`π/2` eigenspace on the `P`-side;
6. `Uᗮ ⊓ V` is the angle-`π/2` eigenspace on the `Pᗮ`-side;
7. the two crossed defects are isometric.

Items 3--7 are the mathematical content of the theorem's hypothesis: the
`π/2` multiplicities are *forced* to agree, because `J₀` restricts to a linear
isometric equivalence between them, while the `0` multiplicities are the two
kernels of `sin Θ₀` and `sin Θ₁`, which `J₀` never sees.  That the latter are
genuinely unconstrained is witnessed by
`theorem3_1_realization_zeroAngle_unconstrained`.

Grounded by `:=` on `Geometry/Halmos/Realization.lean`, so there is a single
source of truth.  The block matrix behind item 1 and item 2 is
`starProjection_targetSubspace_apply`, which reproduces equation (3.7) of the
source, both off-diagonal entries positive. -/
theorem theorem3_1_realization (d : HalmosAngleDatum 𝕜 E F) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        (d.targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (d.cos₀ (d.cos₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        ((d.targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (d.cos₁ (d.cos₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₀ : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₁ : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace)) :=
  ⟨d.compress_source_eq, d.compress_sourceOrthogonal_eq, d.halmosCommonPart_eq,
    d.halmosExteriorPart_eq, d.halmosSourceDefect_eq, d.halmosTargetDefect_eq,
    d.nonempty_halmosSourceDefect_equiv_targetDefect⟩

section OfAngles

variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
  [Algebra ℝ (F →L[𝕜] F)] [IsScalarTower ℝ 𝕜 (F →L[𝕜] F)]
  [ContinuousFunctionalCalculus ℝ (F →L[𝕜] F) IsSelfAdjoint]

/-- **Davis--Kahan 1970, Theorem 3.1, sentence (ii), in the printed shape: stated
from the angle operators rather than from a packaged datum.**

`theorem3_1_realization` consumes a `HalmosAngleDatum`, which carries
`cos Θ₀, sin Θ₀, cos Θ₁, sin Θ₁` and the intertwiner as five independent fields.
The paper does not.  It says "given such `Θⱼ` acting on spaces `Hⱼ`", where
"such" refers to the theorem's own sentence "these are arbitrary Hermitian
operators satisfying the following conditions: `0 ≤ Θⱼ ≤ π/2`; ... and the
spectral multiplicity functions of the `Θⱼ` are the same except for a possible
difference in the multiplicity of `{0}`", and then extracts from that last
condition "some isometry `J₀` of `closure (ran Θ₀)` onto `closure (ran Θ₁)` such
that `J₀ Θ₀ J₀⁻¹` agrees on its domain with `Θ₁`".  So the printed data are two
Hermitian operators and one intertwining partial isometry — and that is this
statement's hypothesis list.  The datum is built inside the proof by
`MathAhead.HiddenFoundations.HalmosAngleDatum.ofIntertwinedAngles`, and each
`cos Θⱼ`, `sin Θⱼ` in the conclusion is the continuous functional calculus of
`Θⱼ` rather than an opaque field, so the seven conjuncts of
`theorem3_1_realization` are read here directly off `Θ₀`, `Θ₁` and `J`.

**The two partial-isometry hypotheses are the paper's, not an artifact.**
`hisom` and `hcoisom` say that `J` is isometric on `ran sin Θ₀` and co-isometric
onto `ran sin Θ₁`; that is the content of the printed `J₀`, and it is a
multiplicity statement, invisible to a functional calculus of one operator at a
time.  Everything else the datum needs is derived.

**On the spectral confinement.**  `_hspec₀` and `_hspec₁` are the printed
`0 ≤ Θⱼ ≤ π/2`.  They are taken as hypotheses here and are deliberately unused in
the proof, hence the underscores.  They belong here rather than on the
constructor: `HalmosAngleDatum` records no nonnegativity, and none of the ten
fields `ofIntertwinedAngles` derives needs one — `cos² + sin² = 1` and
`J f(Θ₀) = f(Θ₁) J` hold over all of `ℝ` — so assuming confinement there would
narrow the constructor for nothing.  What confinement buys is that the statement
*reads* as the printed sentence: on `[0, π/2]` one has `sin t = 0 ↔ t = 0` and
`cos t = 0 ↔ t = π/2`, so conjuncts 3--4 exhibit the two angle-`0` spaces and
conjuncts 5--6 the two angle-`π/2` spaces, which is what Davis and Kahan mean by
calling the `Θⱼ` angle operators.  Dropping the two hypotheses would leave the
same theorem with the same proof and a weaker reading; keeping them costs
nothing, so they are kept.

`RCLike`-generic.  The real case is therefore an instantiation and not a second
theorem: `theorem3_1_realization_ofAngles_real`. -/
theorem theorem3_1_realization_ofAngles
    {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (_hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (_hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : E →L[𝕜] F) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        ((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (cfc Real.cos Θ₀ (cfc Real.cos Θ₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        (((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (cfc Real.cos Θ₁ (cfc Real.cos Θ₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)) :=
  theorem3_1_realization (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom)

end OfAngles

/-- **The multiplicity at angle `0` is genuinely unconstrained.**

The all-`0` datum over an arbitrary pair `(E, F)` of Hilbert spaces
realizes `U = V`, whose angle-`0` spaces are the whole of `E` on the `P`-side and
the whole of `F` on the `Pᗮ`-side.  `E` and `F` are unrelated, so no admissibility
condition at angle `0` can be imposed — in contrast to the angle `π/2`, where
item 7 of `theorem3_1_realization` forces the two multiplicities to agree.
Together the two statements are why Davis and Kahan's hypothesis is asymmetric
between `0` and `π/2`. -/
theorem theorem3_1_realization_zeroAngle_unconstrained
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (F : Type v) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    halmosCommonPart (sourceSubspace 𝕜 E F) (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        sourceSubspace 𝕜 E F ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F)) ⊤ :=
  ⟨trivial_halmosCommonPart_eq 𝕜 E F, trivial_halmosExteriorPart_eq 𝕜 E F⟩

/-- **Davis--Kahan 1970, Corollary 3.1, the realization sentence.**

The classification half says that the compactness hypothesis plus the angle
eigenvalue list determines the pair.  This is the sentence that says the list is
otherwise *arbitrary*: given any

`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`,

the pair

`U = ` the `E`-factor of `ℓ²(ℕ, 𝕜) ⊕₂ ℓ²(ℕ, 𝕜)`,  `V = (angleSequenceDatum 𝕜 θ).targetSubspace`

realizes it.  The witness is exhibited rather than asserted to exist: `V` is the
image of `U` under the direct rotation built from the diagonal operators
`cos Θ = diag (cos θₙ)` and `sin Θ = diag (sin θₙ)`, so the whole construction is
`theorem3_1_realization` applied to a datum, not a new geometric argument.

The four conclusions are, in order:

1. **the printed compactness hypothesis holds** — what is proved compact is the
   *defect* block `P (1 - Q) P`, which is `sin² Θ` on the `E`-factor, and
   `θₙ → 0` makes its coefficients vanish.  Corollary 3.1 as printed assumes
   exactly this block, and the census records that it is incomparable with
   `P Q P` in infinite dimension, so the choice is stated rather than left
   implicit.  (`P Q P` is `cos² Θ` here, with coefficients tending to `1`; that
   this makes it non-compact is not asserted as proved.);
2. **the angle list is the prescribed one**: the classifying list of the defect
   block, in the sense of `compactAngleEigenvalueList`, is `n ↦ sin² θₙ`.  The
   map `θ ↦ sin² θ` is strictly monotone on `[0, π/2]`, so this carries exactly
   the information of the printed decreasing sequence `θ`;
3. and 4. **the angle-`0` multiplicities**, on the two sides, are the kernels of
   `sin Θ` — here equal, because the datum puts the same diagonal on both sides.

This witness realizes the two sides' angle-`0` multiplicities *equal*, and
realizes only the multiplicities the sequence `θ` itself produces.  An arbitrary
and independently prescribed pair of angle-`0` multiplicities is
`corollary3_1_realization_zeroMultiplicity`, which adds
`trivialHalmosAngleDatum` on two further spaces by `HalmosAngleDatum.prod`. -/
theorem corollary3_1_realization (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
          (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
            (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
            (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
              (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          (angleSequenceDatum 𝕜 θ).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) :
            AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceAmbient 𝕜)
          (LinearMap.ker (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          (angleSequenceDatum 𝕜 θ).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) :
            AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceAmbient 𝕜)
          (LinearMap.ker (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜)) :=
  ⟨isCompactOperator_angleSequenceDefectBlock hlim,
    funext fun n => approximationNumber_angleSequenceDefectBlock hθ0 hθ2 hanti n,
    (angleSequenceDatum 𝕜 θ).halmosCommonPart_eq,
    (angleSequenceDatum 𝕜 θ).halmosExteriorPart_eq⟩

/-- **Davis--Kahan 1970, Corollary 3.1, the realization sentence with prescribed
angle-`0` multiplicities.**

The paper's sentence is: the eigenvalues of `Θ₀` are an arbitrary sequence
`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0` *together with a possible eigenvalue `0`*, and those of
`Θ₁` are the same except perhaps for the multiplicity of `0`.  Here `Z₀` and `Z₁`
are that eigenvalue's two multiplicities: arbitrary Hilbert spaces, chosen
independently of each other and of `θ`.

The pair is again exhibited rather than asserted to exist.  It is
`theorem3_1_realization` applied to
`(angleSequenceDatum 𝕜 θ).prod (trivialHalmosAngleDatum 𝕜 Z₀ Z₁)`: the sequence
on one summand and the all-`0` datum on the other.  The four conclusions are the
printed compactness hypothesis on the *defect* block `P (1 - Q) P` (not on
`P Q P` — see `corollary3_1_realization`), the prescribed angle list, and the two
angle-`0` eigenspaces, which come out as the prescribed `Z₀` and `Z₁`.

`hne` — no prescribed angle is itself `0` — is used only by the last two
conclusions, and is the paper's own reading: the angle `0` is carried by `Z₀` and
`Z₁`, separately from the sequence.  The first two conclusions hold without it. -/
theorem corollary3_1_realization_zeroMultiplicity (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (Z₀ : Type*) [NormedAddCommGroup Z₀] [InnerProductSpace 𝕜 Z₀] [CompleteSpace Z₀]
    (Z₁ : Type*) [NormedAddCommGroup Z₁] [InnerProductSpace 𝕜 Z₁] [CompleteSpace Z₁]
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) (hne : ∀ n, θ n ≠ 0) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
          (ContinuousLinearMap.id 𝕜
              (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
            (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
            (ContinuousLinearMap.id 𝕜
                (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                  WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
              (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₀ :
              Z₀ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₀)) ⊤) ∧
      halmosExteriorPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₁) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₁ :
              Z₁ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) ⊤) := by
  refine ⟨isCompactOperator_angleSequenceZeroDefectBlock 𝕜 θ Z₀ Z₁ hlim,
    funext fun n =>
      approximationNumber_angleSequenceZeroDefectBlock 𝕜 θ Z₀ Z₁ hθ0 hθ2 hanti n,
    ?_, ?_⟩
  · refine (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).halmosCommonPart_eq.trans ?_
    rw [angleSequenceZeroDatum_sin₀, ker_blockMap_angleSinOp 𝕜 θ hθ0 hθ2 hne Z₀]
  · refine (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).halmosExteriorPart_eq.trans ?_
    rw [angleSequenceZeroDatum_sin₁, ker_blockMap_angleSinOp 𝕜 θ hθ0 hθ2 hne Z₁]

end Realization

/-! ## Corollary 3.1: realization composed with classification

The realization sentence computes the angle list of the *ambient* defect block
`P (1 - Q) P`, while the classification sentence's invariant is the eigenvalue list of the
*generic* cosine block of the pair `(U, Vᗮ)`.  The realized pair puts no mass on any of the
four elementary Halmos summands once no prescribed angle is `0` or `π/2`, so
`approximationNumber_genericCosineBlock_eq_ambient` identifies the two lists and the two
halves compose.

**Which compact object.**  Both halves here are on the *defect* block `P (1 - Q) P`, as
printed.  Nothing below compares `P (1 - Q) P` with `P Q P`; the census's record that the
two compactness hypotheses are incomparable in infinite dimension is untouched.

**Recorded narrowing.**  The printed sentence allows `π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`, that is,
angles equal to `π/2` and a possible eigenvalue `0`.  The statements below assume
`0 < θₙ < π/2` strictly.  This is a *narrowing* of the source hypothesis, and it is the
exact hypothesis that makes the four elementary summands vanish, so that the generic
invariant and the ambient list coincide.  The angle-`0` multiplicities are realized
separately and unconstrained by `corollary3_1_realization_zeroMultiplicity`, and the angle
`π/2` is the elementary summand `U ⊓ Vᗮ`, so neither is lost from the paper's picture —
they are carried by `SameHalmosTrivialDimensions` rather than by the list. -/

section RealizationClassification

open MathAhead.HiddenFoundations

/-- **The realized pair's generic invariant is the prescribed angle list.**

The classifying invariant of Corollary 3.1's defect-block form, evaluated on the pair
realized by `angleSequenceDatum`, is `n ↦ sin² θₙ`.  Grounded by `:=` on the realization
sentence's approximation-number computation and on
`approximationNumber_genericCosineBlock_eq_ambient`; no angle mathematics is redone. -/
theorem compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum
    (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ) :
    compactAngleEigenvalueList
        (genericCosineBlock
          (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          ((angleSequenceDatum 𝕜 θ).targetSubspace)ᗮ) =
      fun n => Real.sin (θ n) ^ 2 := by
  have hθ0' : ∀ n, 0 ≤ θ n := fun n => (hθ0 n).le
  have hθ2' : ∀ n, θ n ≤ Real.pi / 2 := fun n => (hθ2 n).le
  have hne : ∀ n, θ n ≠ 0 := fun n => (hθ0 n).ne'
  have hsin : LinearMap.ker
      ((angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜) :
        AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ :=
    ker_angleSinOp_eq_bot 𝕜 θ hθ0' hθ2' hne
  have hcos : LinearMap.ker
      ((angleCosOp 𝕜 θ : AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜) :
        AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ :=
    ker_angleCosOp_eq_bot 𝕜 θ hθ0' hθ2
  -- The four elementary Halmos summands of the realized pair are trivial.
  have hcommon : halmosCommonPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosCommonPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosCommonPart_eq,
      angleSequenceDatum_sin₀, hsin, Submodule.map_bot]
  have hsource : halmosSourceDefect
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosSourceDefect
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosSourceDefect_eq,
      angleSequenceDatum_cos₀, hcos, Submodule.map_bot]
  have htarget : halmosTargetDefect
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosTargetDefect
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosTargetDefect_eq,
      angleSequenceDatum_cos₁, hcos, Submodule.map_bot]
  have hexterior : halmosExteriorPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosExteriorPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosExteriorPart_eq,
      angleSequenceDatum_sin₁, hsin, Submodule.map_bot]
  have htriv : halmosTrivialPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      ((angleSequenceDatum 𝕜 θ).targetSubspace)ᗮ = ⊥ := by
    rw [halmosTrivialPart_orthogonal_right, show halmosTrivialPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace =
      (halmosCommonPart _ _ ⊔ halmosSourceDefect _ _) ⊔
        (halmosTargetDefect _ _ ⊔ halmosExteriorPart _ _) from rfl,
      hcommon, hsource, htarget, hexterior, bot_sup_eq, bot_sup_eq]
  -- The bridge, then the realization's own computation of the ambient list.
  rw [compactAngleEigenvalueList_genericCosineBlock_eq_ambient _ _ htriv,
    Submodule.starProjection_orthogonal (angleSequenceDatum 𝕜 θ).targetSubspace]
  exact funext fun n =>
    approximationNumber_angleSequenceDefectBlock hθ0' hθ2' hanti n

/-- **Davis--Kahan 1970, Corollary 3.1: the realization sentence composed with the
classification sentence.**

Given a prescribed angle sequence `π/2 > θ₁ ≥ θ₂ ≥ ⋯ → 0` with every `θₙ` strictly between
`0` and `π/2`, an arbitrary pair `(U₂, V₂)` with the printed compact defect block is
unitarily equivalent to the realized pair exactly when its four elementary Halmos
multiplicities are trivial and its angle list is `n ↦ sin² θₙ`.

This is the statement the two halves of Corollary 3.1 were built to meet.  Both hypotheses
and both conclusions are on the *defect* block `P (1 - Q) P`, as printed.  The strict
inequalities `0 < θₙ < π/2` are a recorded narrowing of the printed sequence bound; see the
section note above. -/
theorem corollary3_1_prescribedAngleSequence_classification (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℂ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℂ (AngleSequenceSpace ℂ) (AngleSequenceSpace ℂ))
        (angleSequenceDatum ℂ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℂ (AngleSequenceSpace ℂ) (AngleSequenceSpace ℂ))
        (angleSequenceDatum ℂ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_complex _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℂ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm

end RealizationClassification

/-! ## Section 3 over a real Hilbert space

The statements above are field-generic, so the real forms are instantiations
rather than new theorems.  They are recorded by name because the census tracks
the paper's results at the paper's scope, and because they are the machine
check that the `𝕜 = ℝ` instantiation really is inhabited: each one forces
typeclass inference to find
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`.

Davis and Kahan work on a Hilbert space over `ℝ` or `ℂ` throughout, so the real
scope is the source scope, not an extension of it. -/

section RealScalars

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Theorem 3.1, the operator-level classification, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `twoProjection_operator_classification`.  No
compactness, no finite dimension, no separability. -/
theorem twoProjection_operator_classification_real :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ :=
  twoProjection_operator_classification U₁ V₁ U₂ V₂

/-! ### Theorem 3.1, sentence (ii), over a real Hilbert space

`theorem3_1_realization_ofAngles` is `RCLike`-generic, so its real form is an
instantiation and not a theorem.  It is recorded as an `example` rather than by
name deliberately: it adds no declaration, and it fails loudly if the `𝕜 = ℝ`
hypothesis block ever stops being inhabited.  That block is the only thing that
could have made the real case cost something — the wrapper needs
`ContinuousFunctionalCalculus ℝ (Hⱼ →L[ℝ] Hⱼ) IsSelfAdjoint` on *both* spaces to
form `cos Θⱼ` and `sin Θⱼ`, and instance search supplies it from
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, in
unrestricted dimension.  Two of the seven conjuncts are read off below: the
angle-`π/2` space on the `P`-side, and the isometry between the two crossed
defects that forces the two `π/2` multiplicities to agree. -/

open MathAhead.HiddenFoundations in
example {Θ₀ : H₁ →L[ℝ] H₁} {Θ₁ : H₂ →L[ℝ] H₂}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : H₁ →L[ℝ] H₂) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
      Submodule.map (modelInl ℝ H₁ H₂ : H₁ →ₗ[ℝ] WithLp 2 (H₁ × H₂))
        (LinearMap.ker ((cfc Real.cos Θ₀ : H₁ →L[ℝ] H₁) : H₁ →ₗ[ℝ] H₁)) ∧
    Nonempty (↥(halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace) ≃ₗᵢ[ℝ]
      ↥(halmosTargetDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace)) :=
  ⟨(theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.1,
    (theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.2.2⟩

/-- **Davis--Kahan 1970, Corollary 3.1, over a real Hilbert space.**

The `𝕜 = ℝ` instance of
`MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`:
with `P_U P_V P_U` compact on both sides, the four elementary Halmos
multiplicities together with the multiplicity of every angle are a complete
invariant. -/
theorem corollary3_1_compact_classification_real
    (hc₁ : IsCompactOperator (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hc₂ : IsCompactOperator (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      MathAhead.HiddenFoundations.SameCompactAngleData U₁ V₁ U₂ V₂ :=
  MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    U₁ V₁ U₂ V₂ hc₁ hc₂

/-- **Davis--Kahan 1970, Corollary 3.1 in the paper's decreasing eigenvalue-list
phrasing, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `corollary3_1_compact_angleList_classification`.

**The angle list stays `ℝ`-valued.**  `compactAngleEigenvalueList` has codomain
`ℕ → ℝ` over every scalar field, because the eigenvalues of a compact positive
self-adjoint operator are real; passing to real scalars changes only how such an
eigenvalue is embedded back into the field, never what the list records.

**The compactness hypothesis is the generic theorem's.**  It is
`P_U P_V P_U` compact, not the printed defect block `P (I - Q) P`.  Those two are
incomparable in infinite dimension; that is a pre-existing question recorded on
this source row, and the real form inherits it unchanged.  The printed
hypothesis is carried by
`corollary3_1_compact_defectBlock_angleList_classification`, which is the same
theorem applied to `(U, Vᗮ)`. -/
theorem corollary3_1_compact_angleList_classification_real
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁) =
        compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂) :=
  corollary3_1_compact_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂

/-- **Davis--Kahan 1970, Corollary 3.1 with the printed hypothesis, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of `corollary3_1_compact_defectBlock_angleList_classification`,
grounded on it by `:=`, with no added hypothesis: the compactness is of the *defect* block
`P (I - Q) P`, as printed, and the classifying list is the eigenvalue list of the
corresponding sine-square angle operator.

The reconstruction functional calculus that the generic form carries is synthesized here at
`ℝ`, not assumed.  As over `ℂ`, the `PQP` versus `P (I - Q) P` question recorded on this
source row is untouched: this is the printed object on both sides. -/
theorem corollary3_1_compact_defectBlock_angleList_classification_real
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L
        (ContinuousLinearMap.id ℝ H₁ - projection V₁) ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L
        (ContinuousLinearMap.id ℝ H₂ - projection V₂) ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (MathAhead.HiddenFoundations.genericCosineBlock U₂ V₂ᗮ) :=
  corollary3_1_compact_defectBlock_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂

open MathAhead.HiddenFoundations in
/-- **Davis--Kahan 1970, Corollary 3.1: the realization sentence composed with the
classification sentence, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `corollary3_1_prescribedAngleSequence_classification`, assembled
from the same two halves: the realization `corollary3_1_realization` is already
`RCLike`-generic, and the classification half is now
`corollary3_1_compact_defectBlock_angleList_classification_real`.

Both hypotheses and both conclusions are on the *defect* block `P (1 - Q) P`, as printed.
The strict inequalities `0 < θₙ < π/2` are the same **recorded narrowing** of the printed
sequence bound `π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0` that the complex form carries, and for the same
reason: strictness is exactly what makes the four elementary Halmos summands vanish, so
that the generic invariant and the ambient list coincide.  The angle-`0` and angle-`π/2`
data are not lost — they are the elementary summands, carried by
`SameHalmosTrivialDimensions`. -/
theorem corollary3_1_prescribedAngleSequence_classification_real (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℝ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_real _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℝ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm

/-! ### Proposition 3.2 over a real Hilbert space

The three statements below are the `𝕜 = ℝ` instances of the generic
`section NonacuteExistence` theorems, each grounded by `:=` on the generic
theorem and each carrying exactly the generic theorem's hypotheses.  In
particular the real forms assume no finite dimension, no separability and no
compactness, and they do **not** add a nondegeneracy hypothesis on the crossed
defects: `¬ TauCeti.IsAcute U₁ V₁` already forces one of them to be nonzero,
by `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`.

They are *not* obtained by descending the complex theorem.  That route is
refuted -- transporting the forward direction produces an isometry of the
complexified defect spaces, and nothing recovers a real one from it -- so the
whole polar and direct-rotation stack under `DavisKahan/Geometry/Polar/` was
made `RCLike`-generic instead, which is what these instances read off. -/

/-- **Davis--Kahan 1970, Proposition 3.2, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `proposition3_2_exists_iff_crossedDefectsEquivalent`: a
direct rotation of the pair exists exactly when the two crossed intersections
admit a linear isometric equivalence, which is the cardinal-free form of the
paper's equal-dimension condition (3.5). -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent_real :
    (∃ T : H₁ →L[ℝ] H₁, IsPaperDirectRotation U₁ V₁ T) ↔
      CrossedDefectsEquivalent U₁ V₁ :=
  proposition3_2_exists_iff_crossedDefectsEquivalent U₁ V₁

/-- **Davis--Kahan 1970, Proposition 3.2, the injective parameterization, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `proposition3_2_parameterized_nonuniqueness`. -/
theorem proposition3_2_parameterized_nonuniqueness_real
    (hdefect : CrossedDefectsEquivalent U₁ V₁) :
    ∃ build :
        (halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℝ] halmosTargetDefect U₁ V₁) →
          (H₁ →L[ℝ] H₁),
      (∀ J, IsPaperDirectRotation U₁ V₁ (build J)) ∧
      Function.Injective build :=
  proposition3_2_parameterized_nonuniqueness U₁ V₁ hdefect

/-- **Davis--Kahan 1970, Proposition 3.2, second printed sentence, over a real
Hilbert space: "It is not unique."**

The `𝕜 = ℝ` instance of `proposition3_2_not_unique`.  Over `ℝ` the two witnesses
are still `build J` and `build (-J)`; the sign change is available because the
scalar field has characteristic zero, which `RCLike` supplies. -/
theorem proposition3_2_not_unique_real
    (hdefect : CrossedDefectsEquivalent U₁ V₁)
    (hnonacute : ¬ TauCeti.IsAcute U₁ V₁) :
    ∃ T₁ T₂ : H₁ →L[ℝ] H₁,
      IsPaperDirectRotation U₁ V₁ T₁ ∧ IsPaperDirectRotation U₁ V₁ T₂ ∧
        T₁ ≠ T₂ :=
  proposition3_2_not_unique U₁ V₁ hdefect hnonacute

/-- **Proposition 3.2's nonuniqueness in literal `∃!` form, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of `proposition3_2_not_existsUnique`. -/
theorem proposition3_2_not_existsUnique_real
    (hdefect : CrossedDefectsEquivalent U₁ V₁)
    (hnonacute : ¬ TauCeti.IsAcute U₁ V₁) :
    ¬ ∃! T : H₁ →L[ℝ] H₁, IsPaperDirectRotation U₁ V₁ T :=
  proposition3_2_not_existsUnique U₁ V₁ hdefect hnonacute

end RealScalars

end Section3
end Frontier
end Experimental
end DavisKahan
end TauCeti