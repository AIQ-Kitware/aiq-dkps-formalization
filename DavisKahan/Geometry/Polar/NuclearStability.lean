/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearOptimizerCertificate
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Isometry

/-!
# Nuclear stability on the common fixed sector

For any finite-cost transporter, half its squared Hilbert–Schmidt
displacement on the projection-agreement sector is bounded by the
excess over the exact global nuclear minimum. The common sector may
be infinite dimensional, and no principal-plane restriction is imposed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Fixed-sector stability for every ambient transporter.** The
squared Hilbert–Schmidt motion on the full common sector is at most
twice the excess nuclear cost. Finite native costs are explicit; neither
finite rank nor separability nor angle-block preservation is required. -/
theorem nuclear_transport_fixed_sector_gap_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hfinite : (1 - (T : E →L[ℂ] E)).nuclearENorm ≠ ∞) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    ((1 - (T : E →L[ℂ] E)) * B.ker.starProjection).hilbertSchmidtNorm ^ 2 ≤
      2 * ((1 - (T : E →L[ℂ] E)).nuclearENorm.toReal -
        (K.starProjection - L.starProjection).nuclearENorm.toReal) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  let Z := R.trans T.symm
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  let G := (1 - (Z : E →L[ℂ] E)) * Q
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  have hnorm (A : E →L[ℂ] E) : Φ.gauge A = A.nuclearENorm := by
    simp only [Φ, OperatorIdealFamily.gauge_schatten, one_div_one,
      ENNReal.rpow_one, ContinuousLinearMap.nuclearENorm_def]
  have hRref (x : E) : R (K.reflection x) = L.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines K L D x
  have hTref := (K.map_eq_iff_intertwines_reflection L T).mp hT
  have hZ (x : E) : Z (K.reflection x) = K.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (K.reflection x))) = T (K.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hfactor : nonacuteDirectRotation K L D - (Z : E →L[ℂ] E) =
      ((T : E →L[ℂ] E) - 1) * (Z : E →L[ℂ] E) := by
    ext x
    change R x - T.symm (R x) = T (T.symm (R x)) - T.symm (R x)
    rw [T.apply_symm_apply]
  have hN : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm =
      (1 - (T : E →L[ℂ] E)).nuclearENorm := by
    rw [← hnorm _, hfactor]
    change Φ.gauge (((T : E →L[ℂ] E) - 1) ∘L (Z : E →L[ℂ] E)) = _
    rw [Φ.gauge_comp_linearIsometryEquiv_right]
    rw [show (T : E →L[ℂ] E) - 1 = -(1 - (T : E →L[ℂ] E)) from (neg_sub _ _).symm,
      Φ.gauge_neg, hnorm]
  have hXfinite : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm ≠ ∞ := by
    rwa [hN]
  have hgap := nuclearTransportDual_fixed_sector_gap_complex K L D Z hZ hΔ hXfinite
  dsimp only at hgap
  rw [hN] at hgap
  have hTG : (T : E →L[ℂ] E) ∘L G = -((1 - (T : E →L[ℂ] E)) * Q) := by
    ext x
    have hx := B.ker.starProjection_apply_mem x
    change Q x ∈ B.ker at hx
    rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
    change K.starProjection (Q x) - L.starProjection (Q x) = 0 at hx
    have hR : R (Q x) = Q x :=
      nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _ (sub_eq_zero.mp hx)
    change T (Q x - T.symm (R (Q x))) = -(Q x - T (Q x))
    rw [map_sub, T.apply_symm_apply, hR]
    abel
  have hHS := ContinuousLinearMap.hilbertSchmidtNorm_isometry_comp
    (T : E →L[ℂ] E) T.norm_map G
  rw [hTG, show -((1 - (T : E →L[ℂ] E)) * Q) =
    (-1 : ℂ) • ((1 - (T : E →L[ℂ] E)) * Q) from (neg_one_smul ℂ _).symm,
    ContinuousLinearMap.hilbertSchmidtNorm_smul, norm_neg, norm_one, one_mul] at hHS
  change G.hilbertSchmidtNorm ^ 2 ≤ _ at hgap
  change ((1 - (T : E →L[ℂ] E)) * Q).hilbertSchmidtNorm ^ 2 ≤ _
  rwa [← hHS] at hgap

end TauCeti.DavisKahan
