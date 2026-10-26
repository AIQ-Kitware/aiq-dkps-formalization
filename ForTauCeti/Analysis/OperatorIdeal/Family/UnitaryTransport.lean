/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Projection transport lower bounds for operator ideals

The displacement of any unitary transporting one orthogonal projection
to another dominates their difference in every operator-ideal gauge.
No compactness, dimension or separability hypothesis is needed. The
proof averages two isometric translates using the source reflection.

## Provenance

Classical unitary invariance and the triangle inequality, implemented
here for the DKPS infinite-dimensional transport extension using the
accepted Tau Ceti operator-ideal family. No separate priority claim is
made for this inequality or its isometry-invariance lemmas.
-/

public section

namespace TauCeti.OperatorIdealFamily

open scoped ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Isometric changes of codomain preserve every operator-ideal gauge. -/
theorem gauge_comp_linearIsometryEquiv_left (A : E →L[𝕜] F) (V : F ≃ₗᵢ[𝕜] G) :
    Φ.gauge ((V : F →L[𝕜] G) ∘L A) = Φ.gauge A := by
  apply le_antisymm (Φ.gauge_comp_left_le_self V.toLinearIsometry.norm_toContinuousLinearMap_le A)
  have h := Φ.gauge_comp_left_le_self
    V.symm.toLinearIsometry.norm_toContinuousLinearMap_le ((V : F →L[𝕜] G) ∘L A)
  change Φ.gauge ((V.symm : G →L[𝕜] F) ∘L ((V : F →L[𝕜] G) ∘L A)) ≤ _ at h
  have heq : (V.symm : G →L[𝕜] F) ∘L ((V : F →L[𝕜] G) ∘L A) = A := by
    ext x
    exact V.symm_apply_apply (A x)
  rwa [heq] at h

/-- Isometric changes of domain preserve every operator-ideal gauge. -/
theorem gauge_comp_linearIsometryEquiv_right (A : E →L[𝕜] F) (V : G ≃ₗᵢ[𝕜] E) :
    Φ.gauge (A ∘L (V : G →L[𝕜] E)) = Φ.gauge A := by
  apply le_antisymm (Φ.gauge_comp_right_le_self A V.toLinearIsometry.norm_toContinuousLinearMap_le)
  have h := Φ.gauge_comp_right_le_self (A ∘L (V : G →L[𝕜] E))
    V.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  change Φ.gauge ((A ∘L (V : G →L[𝕜] E)) ∘L (V.symm : E →L[𝕜] G)) ≤ _ at h
  have heq : (A ∘L (V : G →L[𝕜] E)) ∘L (V.symm : E →L[𝕜] G) = A := by
    ext x
    exact congrArg A (V.apply_symm_apply x)
  rwa [heq] at h

/-- Every ambient unitary transporting `K` onto `L` has displacement
gauge at least that of the difference of their orthogonal projections.
The extended inequality also includes competitors of infinite gauge. -/
theorem gauge_projection_sub_le_unitary_displacement
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : K.map W.toLinearMap = L) :
    Φ.gauge (K.starProjection - L.starProjection) ≤ Φ.gauge (1 - (W : E →L[𝕜] E)) := by
  let R : E ≃ₗᵢ[𝕜] E := K.reflection
  let A : E →L[𝕜] E := 1 - (W : E →L[𝕜] E)
  have href : (W : E →L[𝕜] E) ∘L (R : E →L[𝕜] E) ∘L
      (W.symm : E →L[𝕜] E) = (L.reflection : E →L[𝕜] E) := by
    ext x
    have h := Submodule.reflection_map_apply W K x
    change W (K.reflection (W.symm x)) = L.reflection x
    simpa only [hmap] using h.symm
  have hid : (2 : 𝕜) • (K.starProjection - L.starProjection) =
      A ∘L (R : E →L[𝕜] E) -
        (W : E →L[𝕜] E) ∘L ((R : E →L[𝕜] E) ∘L A) ∘L
          (W.symm : E →L[𝕜] E) := by
    calc
      _ = (R : E →L[𝕜] E) - (L.reflection : E →L[𝕜] E) := by
        dsimp only [R]
        rw [Submodule.coe_reflection K, Submodule.coe_reflection L]
        simp only [two_smul]
        module
      _ = (R : E →L[𝕜] E) -
          (W : E →L[𝕜] E) ∘L (R : E →L[𝕜] E) ∘L (W.symm : E →L[𝕜] E) := by
        rw [href]
      _ = _ := by
        ext x
        change R x - W (R (W.symm x)) =
          (R x - W (R x)) - W (R (W.symm x - W (W.symm x)))
        simp only [map_sub, W.apply_symm_apply]
        abel
  have htwo : (2 : ℝ≥0∞) * Φ.gauge (K.starProjection - L.starProjection) ≤
      2 * Φ.gauge A := by
    have h := Φ.gauge_add_le (A ∘L (R : E →L[𝕜] E))
      (-((W : E →L[𝕜] E) ∘L ((R : E →L[𝕜] E) ∘L A) ∘L
        (W.symm : E →L[𝕜] E)))
    rw [← sub_eq_add_neg, ← hid, Φ.gauge_smul, Φ.gauge_neg,
      Φ.gauge_comp_linearIsometryEquiv_right A R,
      Φ.gauge_comp_linearIsometryEquiv_left _ W,
      Φ.gauge_comp_linearIsometryEquiv_right _ W.symm,
      Φ.gauge_comp_linearIsometryEquiv_left A R] at h
    simpa only [enorm_eq_nnnorm, RCLike.nnnorm_ofNat, ENNReal.coe_ofNat, two_mul] using h
  have h := mul_le_mul_left htwo ((2 : ℝ≥0∞)⁻¹)
  have hcancel (b : ℝ≥0∞) : (2 * b) * (2 : ℝ≥0∞)⁻¹ = b := by
    calc
      _ = ((2 : ℝ≥0∞)⁻¹ * 2) * b := by ac_rfl
      _ = b := by
        rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]
  simpa only [hcancel] using h

end TauCeti.OperatorIdealFamily
