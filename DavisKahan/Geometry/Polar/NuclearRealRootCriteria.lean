/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootSpectralFactors
public import ForTauCeti.Analysis.InnerProductSpace.RealSpectralSignObstruction

/-!
# Real signed-root feasibility on compact Hilbert pairs

The spectral product criterion is exact over the reals. On every
strictly acute positive sine eigenspace, existence forces its full real
dimension to be divisible by four. This is an obstruction to roots
attaining the projection lower bound, not to existence of real ambient
minimizers with a larger cost. Zero and right-angle sectors are exempt.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Infinite-rank real spectral obstruction.** Every nonzero strictly
acute sine eigenspace must have real dimension divisible by four if a
real signed root exists. Compactness makes each such eigenspace finite;
the ambient pair may have infinite rank and arbitrary fixed directions. -/
theorem nuclearSignedSineParameters_four_dvd_sine_eigenspace_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (hroot : (nuclearSignedSineParameters K L D).Nonempty)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    4 ∣ Module.finrank ℝ (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s) := by
  let S := K.sinAngleOperator L
  let G := (nuclearTransportDual K L D : E →L[ℝ] E) *
    Proposition35.section3CosAngleOperator K L
  let J : E →L[ℝ] E := K.reflection
  let N := Module.End.eigenspace S.toLinearMap s
  have hSc : IsCompactOperator S := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hsv : S.singularValue = (K.starProjection - L.starProjection).singularValue := by
      funext n
      rw [show S = (K.starProjection - L.starProjection).modulus from K.sinAngleOperator_def L,
        ContinuousLinearMap.singularValue_modulus]
    rw [hsv]
    exact hcompact.tendsto_singularValue
  let : FiniteDimensional ℝ N :=
    ContinuousLinearMap.finite_dimensional_eigenspace hSc s hs0.ne'
  let g : N →L[ℝ] N := G.restrict
    (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G
      (nuclear_spectral_symmetries_comm_sine K L D).1 s)
  let j : N →L[ℝ] N := J.restrict
    (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J
      (nuclear_spectral_symmetries_comm_sine K L D).2 s)
  obtain ⟨P, hP⟩ :=
    (nuclearSignedSineParameters_nonempty_iff_spectral_factors K L D hcompact).mp hroot ⟨s, hs0.ne'⟩
  change IsStarProjection P ∧ Commute P g ∧ P * j + j * P = j at hP
  let c := Real.sqrt (1 - s * s)
  have hsmall : 0 < 1 - s * s := by nlinarith
  have hc : c ≠ 0 := (Real.sqrt_pos.mpr hsmall).ne'
  have hcsq : c * c = 1 - s * s := Real.mul_self_sqrt hsmall.le
  have hgsq : g * g = -(c * c) • 1 := by
    ext x
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change S (x : E) = s • (x : E) at hx
    have h := nuclear_spectral_phase_square K L D s hs0.ne' (x : E) hx
    change G (G (x : E)) = (s * s - 1) • (x : E) at h
    change G (G (x : E)) = -(c * c) • (x : E)
    rw [h, hcsq]
    module
  have hjsq : j * j = 1 := by
    ext x
    exact K.reflection_reflection (x : E)
  exact four_dvd_finrank_of_spectral_sign_projection_real g j P c hc hgsq hjsq
    hP.1 hP.2.1 hP.2.2

/-- A single compact strictly acute sine block of dimension not divisible
by four rules out every real signed root, regardless of the other blocks. -/
theorem not_nonempty_nuclearSignedSineParameters_of_sine_dimension_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : ¬4 ∣ Module.finrank ℝ
      (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s)) :
    ¬(nuclearSignedSineParameters K L D).Nonempty := by
  intro hroot
  exact hdim (nuclearSignedSineParameters_four_dvd_sine_eigenspace_real
    K L D hcompact hroot s hs0 hs1)

end TauCeti.DavisKahan
