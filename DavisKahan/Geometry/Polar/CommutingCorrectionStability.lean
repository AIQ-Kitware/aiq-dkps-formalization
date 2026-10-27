/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.CanonicalStability
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryCorrection
public import ForTauCeti.Analysis.InnerProductSpace.Projection.BlockNorm

/-!
# Stability of canonical commuting-unitary correction

The block-diagonal part of an input unitary has the canonical correction
as its positive polar factor. Its coercivity is controlled by the
commutator norm. Contractivity of orthogonal pinching and the classical
polar perturbation mechanism give a dimension-free input-error bound.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual diagonal block of a unitary is the canonical image/source
intertwiner followed by the input unitary. -/
theorem diagBlock_unitary_eq_canonicalIntertwiner_mul
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E) :
    K.diagBlock (A : E →L[ℂ] E) =
      spectraCanonicalIntertwiner (K.map A.toLinearMap) K * (A : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  have hmap : L.starProjection * (A : E →L[ℂ] E) = (A : E →L[ℂ] E) * K.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change (K.map A.toLinearMap).starProjection (A x) = A (K.starProjection x)
    rw [Submodule.starProjection_map_apply, A.symm_apply_apply]
  have hmapc : Lᗮ.starProjection * (A : E →L[ℂ] E) = (A : E →L[ℂ] E) * Kᗮ.starProjection := by
    rw [Submodule.starProjection_orthogonal', Submodule.starProjection_orthogonal',
      sub_mul, mul_sub, one_mul, mul_one, hmap]
  rw [Submodule.diagBlock_def]
  change K.starProjection * (A : E →L[ℂ] E) * K.starProjection +
      Kᗮ.starProjection * (A : E →L[ℂ] E) * Kᗮ.starProjection =
    (K.starProjection * L.starProjection + Kᗮ.starProjection * Lᗮ.starProjection) * (A : E →L[ℂ] E)
  simp only [add_mul, mul_assoc, hmap, hmapc]

/-- The positive factor of the actual commuting correction has the
cosine lower bound dictated by its input's commutator. -/
theorem exists_positive_factor_diagBlock_of_canonical_correction
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : (C : E →L[ℂ] E) =
      spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L (A : E →L[ℂ] E))
    (a : ℝ) (ha : 0 ≤ a)
    (hgap : a ^ 2 + ‖(A : E →L[ℂ] E) * K.starProjection -
      K.starProjection * (A : E →L[ℂ] E)‖ ^ 2 ≤ 1) :
    ∃ H : E →L[ℂ] E, K.diagBlock (A : E →L[ℂ] E) = (C : E →L[ℂ] E) * H ∧
      H.IsPositive ∧ ∀ x, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪H x, x⟫_ℂ := by
  let L := K.map A.toLinearMap
  let S := spectraCanonicalIntertwiner L K
  let H := (A.symm : E →L[ℂ] E) * S.modulus * (A : E →L[ℂ] E)
  have hpos : H.IsPositive := by
    have h := S.isPositive_modulus.adjoint_conj (A : E →L[ℂ] E)
    rw [A.adjoint_eq_symm] at h
    exact h
  have hAA : (A : E →L[ℂ] E) * (A.symm : E →L[ℂ] E) = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    exact A.apply_symm_apply x
  have hfactor : K.diagBlock (A : E →L[ℂ] E) = (C : E →L[ℂ] E) * H := by
    rw [hC, diagBlock_unitary_eq_canonicalIntertwiner_mul]
    change S * (A : E →L[ℂ] E) =
      (spectraCanonicalPolarFactor L K * (A : E →L[ℂ] E)) *
        ((A.symm : E →L[ℂ] E) * S.modulus * (A : E →L[ℂ] E))
    rw [mul_assoc, ← mul_assoc (A : E →L[ℂ] E), ← mul_assoc (A : E →L[ℂ] E),
      hAA, one_mul, ← mul_assoc]
    exact congrArg (fun T : E →L[ℂ] E => T * (A : E →L[ℂ] E))
      (spectraCanonicalPolarFactor_decomposition L K).symm
  refine ⟨H, hfactor, hpos, ?_⟩
  intro x
  have hbudget : a ^ 2 + L.projectionGap K ^ 2 ≤ 1 := by
    dsimp only [L]
    rw [Submodule.projectionGap_def, K.norm_projection_image_sub_eq_commutator A]
    exact hgap
  have h := canonical_modulus_coercive_of_gap_sq_add_le_one L K a ha hbudget (A x)
  rw [A.norm_map] at h
  have hinner : ⟪H x, x⟫_ℂ = ⟪S.modulus (A x), A x⟫_ℂ := by
    have hh := A.inner_map_map (A.symm (S.modulus (A x))) x
    rw [A.apply_symm_apply] at hh
    exact hh.symm
  rw [hinner]
  exact h

/-- The canonical correction is exactly the accepted canonical factor
of the actual diagonal block through its modulus. -/
theorem canonical_correction_eq_diagBlock_factorThru_modulus
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : (C : E →L[ℂ] E) =
      spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L (A : E →L[ℂ] E))
    (a : ℝ) (ha : 0 < a)
    (hgap : a ^ 2 + ‖(A : E →L[ℂ] E) * K.starProjection -
      K.starProjection * (A : E →L[ℂ] E)‖ ^ 2 ≤ 1) :
    (C : E →L[ℂ] E) = (K.diagBlock (A : E →L[ℂ] E)).factorThru
      (K.diagBlock (A : E →L[ℂ] E)).modulus := by
  obtain ⟨H, hH, hpos, hcoerc⟩ :=
    exists_positive_factor_diagBlock_of_canonical_correction K A C hC a ha.le hgap
  exact ContinuousLinearMap.eq_factorThru_modulus_of_unitary_factorization_of_coercive
    _ H C hH hpos a ha hcoerc

/-- Two-endpoint input stability for canonical commuting corrections.
The two commutator bounds may be different; neither input must be a
compact or finite-rank perturbation of a commuting unitary. -/
theorem add_mul_norm_canonical_corrections_sub_le_two_mul_norm_sub
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A B C D : E ≃ₗᵢ[ℂ] E)
    (hC : (C : E →L[ℂ] E) =
      spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L (A : E →L[ℂ] E))
    (hD : (D : E →L[ℂ] E) =
      spectraCanonicalPolarFactor (K.map B.toLinearMap) K ∘L (B : E →L[ℂ] E))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a ^ 2 + ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ^ 2 ≤ 1)
    (hB : b ^ 2 + ‖(B : E →L[ℂ] E) * K.starProjection - K.starProjection * (B : E →L[ℂ] E)‖ ^ 2 ≤ 1) :
    (a + b) * ‖(C : E →L[ℂ] E) - (D : E →L[ℂ] E)‖ ≤
      2 * ‖(A : E →L[ℂ] E) - (B : E →L[ℂ] E)‖ := by
  obtain ⟨H, hH, hHpos, hHcoerc⟩ := exists_positive_factor_diagBlock_of_canonical_correction K A C hC a ha hA
  obtain ⟨J, hJ, hJpos, hJcoerc⟩ := exists_positive_factor_diagBlock_of_canonical_correction K B D hD b hb hB
  have h := ContinuousLinearMap.add_mul_norm_sub_unitary_le_two_mul_norm_sub
    _ _ H J C D hH hJ hHpos.isSelfAdjoint hJpos.isSelfAdjoint a b hHcoerc hJcoerc
  exact h.trans (mul_le_mul_of_nonneg_left (K.norm_diagBlock_sub_le _ _) (by norm_num))

/-- Uniform input-error bound on a closed commutator ball of radius
less than one, independent of Hilbert dimension. -/
theorem norm_canonical_corrections_sub_le_of_commutator_norm_le
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A B C D : E ≃ₗᵢ[ℂ] E)
    (hC : (C : E →L[ℂ] E) =
      spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L (A : E →L[ℂ] E))
    (hD : (D : E →L[ℂ] E) =
      spectraCanonicalPolarFactor (K.map B.toLinearMap) K ∘L (B : E →L[ℂ] E))
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hA : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤ gamma)
    (hB : ‖(B : E →L[ℂ] E) * K.starProjection - K.starProjection * (B : E →L[ℂ] E)‖ ≤ gamma) :
    ‖(C : E →L[ℂ] E) - (D : E →L[ℂ] E)‖ ≤
      ‖(A : E →L[ℂ] E) - (B : E →L[ℂ] E)‖ / Real.sqrt (1 - gamma ^ 2) := by
  have hpos : 0 < 1 - gamma ^ 2 := by nlinarith
  have hcos : 0 < Real.sqrt (1 - gamma ^ 2) := Real.sqrt_pos.mpr hpos
  have hAsq := mul_self_le_mul_self (norm_nonneg _) hA
  have hBsq := mul_self_le_mul_self (norm_nonneg _) hB
  have h := add_mul_norm_canonical_corrections_sub_le_two_mul_norm_sub K A B C D hC hD _ _ hcos.le hcos.le
    (by nlinarith [Real.sq_sqrt hpos.le]) (by nlinarith [Real.sq_sqrt hpos.le])
  apply (le_div_iff₀ hcos).mpr
  nlinarith

end TauCeti.DavisKahan
