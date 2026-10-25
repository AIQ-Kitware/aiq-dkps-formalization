/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.Geometry.Angle.Proposition35Nonacute
import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Geometry of the right-angle cosine kernel

The kernel of the principal cosine is the actual crossed-defect sum.
Source and target reflections are opposite there. A cosine-preserving
transporter consequently anticommutes with source reflection on this
kernel, also in infinite dimension. These are geometric reductions for
assembling exceptional optimizer blocks; no ideal attainment is asserted.
-/

noncomputable section

namespace TauCeti.DavisKahan.Proposition35

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The right-angle space is exactly the sum of the two crossed defects. -/
theorem ker_section3CosAngleOperator_eq_crossedDefectSum
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (section3CosAngleOperator K L).ker = crossedDefectSum K L := by
  rw [section3CosAngleOperator_eq_canonicalAbsoluteValue, ContinuousLinearMap.ker_modulus]
  exact ker_canonicalIntertwiner_eq_crossedDefectSum K L

/-- The two reflections are opposite on the whole right-angle space,
without a choice of pairing between the defect spaces. -/
theorem reflection_eq_neg_on_cosine_kernel
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (x : H) (hx : section3CosAngleOperator K L x = 0) :
    L.reflection x = -K.reflection x := by
  have hxmem : x ∈ (section3CosAngleOperator K L).ker := hx
  rw [ker_section3CosAngleOperator_eq_crossedDefectSum] at hxmem
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hxmem
  obtain ⟨huK, huL⟩ := mem_halmosSourceDefect.mp hu
  obtain ⟨hvK, hvL⟩ := mem_halmosTargetDefect.mp hv
  rw [map_add, map_add,
    Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg huL,
    Submodule.reflection_mem_subspace_eq_self hvL,
    Submodule.reflection_mem_subspace_eq_self huK,
    Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hvK]
  abel

/-- A transporter preserving the principal cosine anticommutes with
source reflection on its right-angle kernel. This is the actual ambient
transporter, without a supplied block decomposition. -/
theorem transport_anticommutes_reflection_on_cosine_kernel
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (T : H ≃ₗᵢ[𝕜] H) (hT : K.map T.toLinearMap = L)
    (hTC : Commute (T : H →L[𝕜] H) (section3CosAngleOperator K L))
    (x : H) (hx : section3CosAngleOperator K L x = 0) :
    T (K.reflection x) = -K.reflection (T x) := by
  have hker : section3CosAngleOperator K L (T x) = 0 := by
    have h := DFunLike.congr_fun hTC.eq x
    change T (section3CosAngleOperator K L x) = section3CosAngleOperator K L (T x) at h
    rw [hx, map_zero] at h
    exact h.symm
  rw [(K.map_eq_iff_intertwines_reflection L T).mp hT x]
  exact reflection_eq_neg_on_cosine_kernel K L (T x) hker

end TauCeti.DavisKahan.Proposition35
