/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.DirectRotationIdeal
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryCorrection

/-!
# Certified commuting correction in every operator ideal

The actual commutator is a lower certificate for every commuting-unitary
correction. A completed canonical transport back from the image subspace
constructs a correction costing at most `sqrt 2` times that certificate.
Both fields, arbitrary Hilbert dimension and extended costs are included.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Certified projection-commuting unitary rounding.** An isometric
identification of the image/source crossed defects gives an actual
commuting correction whose ideal distance lies between the commutator
cost and `sqrt 2` times that cost. Every competing commuting unitary
satisfies the same lower certificate. -/
theorem exists_commuting_unitary_with_ideal_certificate
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] (A : H ≃ₗᵢ[𝕜] H)
    (J : halmosSourceDefect (K.map A.toLinearMap) K ≃ₗᵢ[𝕜]
      halmosTargetDefect (K.map A.toLinearMap) K) :
    ∃ C : H ≃ₗᵢ[𝕜] H, Commute (C : H →L[𝕜] H) K.starProjection ∧
      Φ.gauge ((A : H →L[𝕜] H) * K.starProjection - K.starProjection * (A : H →L[𝕜] H)) ≤
        Φ.gauge ((A : H →L[𝕜] H) - (C : H →L[𝕜] H)) ∧
      Φ.gauge ((A : H →L[𝕜] H) - (C : H →L[𝕜] H)) ≤
        ENNReal.ofReal (Real.sqrt 2) * Φ.gauge
          ((A : H →L[𝕜] H) * K.starProjection - K.starProjection * (A : H →L[𝕜] H)) := by
  let L := K.map A.toLinearMap
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation L K J, nonacuteDirectRotation_mem_unitary L K J⟩ :
      unitary (H →L[𝕜] H))
  let C := A.trans R
  have hRmap : L.map R.toLinearMap = K := by
    apply (Submodule.map_eq_iff_intertwines_reflection L K R).mpr
    exact nonacuteDirectRotation_reflection_intertwines L K J
  have hrel : A.symm.trans C = R := by ext x; simp [C]
  have hC : Commute (C : H →L[𝕜] H) K.starProjection := by
    apply (K.map_eq_self_iff_commute_starProjection C).mp
    rw [← K.map_correction_transport A C, hrel]
    exact hRmap
  refine ⟨C, hC, Φ.gauge_commutator_le_unitary_correction K A C hC, ?_⟩
  rw [Φ.gauge_unitary_sub_eq_displacement A C, hrel,
    ← Φ.gauge_projection_image_sub_eq_commutator K A]
  exact gauge_nonacuteDirectRotation_le_sqrt_two_mul_projection_sub Φ L K J

end TauCeti.DavisKahan
