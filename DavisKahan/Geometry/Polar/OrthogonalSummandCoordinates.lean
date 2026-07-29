/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Interop.Spectra.HalmosTwoProjections
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Orthogonal-summand coordinates

This file packages the elementary coordinate map associated with an
orthogonally complemented closed subspace.  It is the reusable assembly layer
needed by the nonacute two-projection classification: once isometries have been
constructed on mutually orthogonal summands, they can be joined into one
ambient unitary without repeating projection algebra.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Coordinates of a vector relative to `K ⊕ Kᗮ`. -/
noncomputable def orthogonalCoordinates
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    H →ₗ[ℂ] WithLp 2 (K × Kᗮ) where
  toFun x := WithLp.toLp 2
    (⟨K.starProjection x, K.starProjection_apply_mem x⟩,
      ⟨Kᗮ.starProjection x, (Kᗮ).starProjection_apply_mem x⟩)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext <;> simp <;> abel
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext <;> simp

/-- Reassemble orthogonal coordinates by adding their ambient values. -/
noncomputable def orthogonalCoordinatesInv
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    WithLp 2 (K × Kᗮ) →ₗ[ℂ] H where
  toFun z := ((WithLp.fst z : K) : H) + ((WithLp.snd z : Kᗮ) : H)
  map_add' x y := by
    simp only [WithLp.add_fst, WithLp.add_snd, Submodule.coe_add]
    abel
  map_smul' c x := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, Submodule.coe_smul,
      RingHom.id_apply]
    module

omit [CompleteSpace H] in
/-- The inverse coordinate map recombines the two summands. -/
@[simp] theorem orthogonalCoordinatesInv_apply
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (z : WithLp 2 (K × Kᗮ)) :
    orthogonalCoordinatesInv K z =
      ((WithLp.fst z : K) : H) + ((WithLp.snd z : Kᗮ) : H) := rfl

omit [CompleteSpace H] in
/-- Recombining the coordinates of a vector returns it. -/
@[simp] theorem orthogonalCoordinatesInv_coordinates
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (x : H) :
    orthogonalCoordinatesInv K (orthogonalCoordinates K x) = x := by
  change K.starProjection x + Kᗮ.starProjection x = x
  exact K.starProjection_add_starProjection_orthogonal x

omit [CompleteSpace H] in
/-- Taking coordinates of a recombined pair returns the pair. -/
@[simp] theorem orthogonalCoordinates_coordinatesInv
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (z : WithLp 2 (K × Kᗮ)) :
    orthogonalCoordinates K (orthogonalCoordinatesInv K z) = z := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply Subtype.ext
    change K.starProjection
      (((WithLp.fst z : K) : H) + ((WithLp.snd z : Kᗮ) : H)) =
        ((WithLp.fst z : K) : H)
    rw [map_add, K.starProjection_eq_self_iff.mpr (WithLp.fst z).property,
      K.starProjection_apply_eq_zero_iff.mpr (WithLp.snd z).property]
    exact add_zero _
  · apply Subtype.ext
    change Kᗮ.starProjection
      (((WithLp.fst z : K) : H) + ((WithLp.snd z : Kᗮ) : H)) =
        ((WithLp.snd z : Kᗮ) : H)
    have hfst : ((WithLp.fst z : K) : H) ∈ (Kᗮ)ᗮ := by
      simpa using (WithLp.fst z).property
    rw [map_add, (Kᗮ).starProjection_apply_eq_zero_iff.mpr hfst,
      (Kᗮ).starProjection_eq_self_iff.mpr (WithLp.snd z).property,
      zero_add]

omit [CompleteSpace H] in
/-- Pythagoras for the coordinate map. -/
theorem norm_sq_orthogonalCoordinates
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (x : H) :
    ‖WithLp.fst (orthogonalCoordinates K x)‖ ^ 2 +
        ‖WithLp.snd (orthogonalCoordinates K x)‖ ^ 2 = ‖x‖ ^ 2 := by
  change ‖K.starProjection x‖ ^ 2 + ‖Kᗮ.starProjection x‖ ^ 2 = ‖x‖ ^ 2
  exact (K.norm_sq_eq_add_norm_sq_starProjection x).symm

omit [CompleteSpace H] in
/-- The coordinate map is norm preserving. -/
theorem norm_orthogonalCoordinates
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (x : H) :
    ‖orthogonalCoordinates K x‖ = ‖x‖ := by
  have hs := norm_sq_orthogonalCoordinates K x
  have hpair : ‖orthogonalCoordinates K x‖ ^ 2 =
      ‖WithLp.fst (orthogonalCoordinates K x)‖ ^ 2 +
        ‖WithLp.snd (orthogonalCoordinates K x)‖ ^ 2 := by
    exact WithLp.prod_norm_sq_eq_of_L2 _
  have hsq : ‖orthogonalCoordinates K x‖ ^ 2 = ‖x‖ ^ 2 := hpair.trans hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Canonical unitary coordinates for `H = K ⊕ Kᗮ`. -/
noncomputable def orthogonalDecompositionEquiv
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    H ≃ₗᵢ[ℂ] WithLp 2 (K × Kᗮ) where
  toLinearEquiv :=
    { toLinearMap := orthogonalCoordinates K
      invFun := orthogonalCoordinatesInv K
      left_inv := orthogonalCoordinatesInv_coordinates K
      right_inv := orthogonalCoordinates_coordinatesInv K }
  norm_map' := norm_orthogonalCoordinates K

omit [CompleteSpace H] in
/-- The decomposition isometry acts by taking coordinates. -/
@[simp] theorem orthogonalDecompositionEquiv_apply
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (x : H) :
    orthogonalDecompositionEquiv K x = orthogonalCoordinates K x := rfl

omit [CompleteSpace H] in
/-- Its inverse acts by recombining them. -/
@[simp] theorem orthogonalDecompositionEquiv_symm_apply
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (z : WithLp 2 (K × Kᗮ)) :
    (orthogonalDecompositionEquiv K).symm z = orthogonalCoordinatesInv K z := rfl

/-- Join two isometries acting on complementary orthogonal summands. -/
noncomputable def orthogonalSumEquiv
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ) :
    H ≃ₗᵢ[ℂ] H :=
  (orthogonalDecompositionEquiv K).trans
    (LinearIsometryEquiv.withLpProdCongr 2 eK ePerp) |>.trans
      (orthogonalDecompositionEquiv L).symm

omit [CompleteSpace H] in
/-- On the first summand the joined isometry acts by the first factor. -/
@[simp] theorem orthogonalSumEquiv_apply_mem
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ)
    (x : K) :
    orthogonalSumEquiv K L eK ePerp (x : H) = (eK x : H) := by
  have hfix : K.starProjection (x : H) = (x : H) :=
    K.starProjection_eq_self_iff.mpr x.2
  have hperp : Kᗮ.starProjection (x : H) = 0 := by
    rw [K.starProjection_orthogonal_apply, hfix, sub_self]
  simp [orthogonalSumEquiv, LinearIsometryEquiv.trans_apply,
    orthogonalCoordinates, orthogonalCoordinatesInv,
    hfix, hperp, Subtype.coe_eta]

omit [CompleteSpace H] in
/-- On the orthogonal complement it acts by the second factor.  With the previous lemma this
pins the joined isometry down summand-wise. -/
@[simp] theorem orthogonalSumEquiv_apply_mem_orthogonal
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ)
    (x : Kᗮ) :
    orthogonalSumEquiv K L eK ePerp (x : H) = (ePerp x : H) := by
  have hfix : Kᗮ.starProjection (x : H) = (x : H) :=
    Kᗮ.starProjection_eq_self_iff.mpr x.2
  have hK : K.starProjection (x : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff K).mpr x.2
  simp [orthogonalSumEquiv, LinearIsometryEquiv.trans_apply,
    orthogonalCoordinates, orthogonalCoordinatesInv,
    hfix, hK, Subtype.coe_eta]

omit [CompleteSpace H] in
/-- The joined equivalence conjugates the first orthogonal projection. -/
theorem orthogonalSumEquiv_intertwines_projection
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ) :
    (orthogonalSumEquiv K L eK ePerp : H →L[ℂ] H) ∘L K.starProjection =
      L.starProjection ∘L
        (orthogonalSumEquiv K L eK ePerp : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  have hxK : K.starProjection x ∈ K := K.starProjection_apply_mem x
  have hxP : Kᗮ.starProjection x ∈ Kᗮ := Kᗮ.starProjection_apply_mem x
  have hmemK : orthogonalSumEquiv K L eK ePerp (K.starProjection x)
      = (eK ⟨K.starProjection x, hxK⟩ : H) :=
    orthogonalSumEquiv_apply_mem K L eK ePerp ⟨K.starProjection x, hxK⟩
  have hmemP : orthogonalSumEquiv K L eK ePerp (Kᗮ.starProjection x)
      = (ePerp ⟨Kᗮ.starProjection x, hxP⟩ : H) :=
    orthogonalSumEquiv_apply_mem_orthogonal K L eK ePerp ⟨Kᗮ.starProjection x, hxP⟩
  have hsum : orthogonalSumEquiv K L eK ePerp x
      = (eK ⟨K.starProjection x, hxK⟩ : H)
        + (ePerp ⟨Kᗮ.starProjection x, hxP⟩ : H) := by
    conv_lhs => rw [← K.starProjection_add_starProjection_orthogonal x]
    rw [map_add, hmemK, hmemP]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe]
  rw [hmemK, hsum, map_add,
    L.starProjection_eq_self_iff.mpr (eK ⟨K.starProjection x, hxK⟩).2,
    (Submodule.starProjection_apply_eq_zero_iff L).mpr
      (ePerp ⟨Kᗮ.starProjection x, hxP⟩).2,
    add_zero]

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti