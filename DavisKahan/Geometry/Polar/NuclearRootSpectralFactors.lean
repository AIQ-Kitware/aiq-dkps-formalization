/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootCompactness
public import ForTauCeti.Analysis.InnerProductSpace.CompactModulusSymmetryFactors

/-!
# Complete independent spectral factors for Hilbert nuclear optimizers

Each nonzero sine eigenspace has a free orthogonal projection subject
only to two local equations: commute with the restricted dual times
cosine, and be exchanged with its complement by the source reflection.
All such independent choices assemble, including zero-cosine defect
blocks. The common fixed kernel has no free factor.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The two symmetry coefficients preserve every intrinsic sine eigenspace.
In particular no inverse cosine, or exclusion of right angles, is used. -/
theorem nuclear_spectral_symmetries_comm_sine
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Commute ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L) (K.sinAngleOperator L) ∧
      Commute (K.reflection : E →L[𝕜] E) (K.sinAngleOperator L) := by
  have hV := Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
    K L (nuclearTransportDual K L D) (nuclearTransportDual_comm_cosine K L D)
  have hC := Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
    K L (Proposition35.section3CosAngleOperator K L)
      (Commute.refl (Proposition35.section3CosAngleOperator K L))
  exact ⟨hV.mul_left hC, K.commute_reflection_iff.mpr (K.commute_starProjection_sinAngleOperator L)⟩

/-- On a nonzero sine eigenspace the dual-times-cosine coefficient has
square `(mu^2-1) I`. This is the strictly acute real complex structure;
it degenerates to zero square at a right angle. -/
theorem nuclear_spectral_phase_square
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (μ : 𝕜) (hμ : μ ≠ 0) (x : E) (hx : K.sinAngleOperator L x = μ • x) :
    let G := (nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L
    (G * G) x = (μ * μ - 1) • x := by
  let S := K.sinAngleOperator L
  let C := Proposition35.section3CosAngleOperator K L
  let V : E →L[𝕜] E := nuclearTransportDual K L D
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  change S x = μ • x at hx
  have hBmod : B.modulus = S :=
    (Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D).trans
      (by rw [Proposition35.section3SinAngleOperator]; exact (K.sinAngleOperator_def L).symm)
  have hSQ : S * Q = 0 := by
    ext y
    apply norm_eq_zero.mp
    change ‖S (Q y)‖ = 0
    rw [← hBmod, B.norm_modulus_apply]
    have hy : B (Q y) = 0 := B.ker.starProjection_apply_mem y
    rw [hy, norm_zero]
  have hQS : Q * S = 0 := by
    have h := congrArg star hSQ
    have hQsa : star Q = Q := (isSelfAdjoint_starProjection B.ker).star_eq
    have hSsa : star S = S := (K.isPositive_sinAngleOperator L).isSelfAdjoint.star_eq
    simpa only [star_mul, hQsa, hSsa, star_zero] using h
  have hQx : Q x = 0 := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hQS
    change Q (S x) = 0 at h
    rw [hx, map_smul] at h
    exact (smul_eq_zero.mp h).resolve_left hμ
  have hVQ : V * Q = Q := nuclearTransportDual_mul_skew_ker_projection K L D
  have hVm : V ∈ unitary (E →L[𝕜] E) :=
    (Unitary.linearIsometryEquiv.symm (nuclearTransportDual K L D)).property
  have hVsq : V * V = Q + Q - 1 := by
    have h := congrArg (fun T : E →L[𝕜] E => V * T)
      (nuclearTransportDual_add_star K L D)
    change V * (V + star V) = V * (Q + Q) at h
    rw [mul_add, Unitary.mul_star_self_of_mem hVm, mul_add, hVQ] at h
    exact eq_sub_of_add_eq h
  have hVxx : V (V x) = -x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hVsq
    change V (V x) = Q x + Q x - x at h
    simpa only [hQx, zero_add, zero_sub] using h
  have hCCx : C (C x) = (1 - μ * μ) • x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x)
      (Proposition35.section3CosAngleOperator_sq_add_sinAngleOperator_sq K L)
    change C (C x) + S (S x) = x at h
    rw [hx, map_smul, hx, smul_smul] at h
    calc
      _ = x - (μ * μ) • x := eq_sub_of_add_eq h
      _ = _ := by module
  have hCV : C (V (C x)) = V (C (C x)) :=
    (congrArg (fun T : E →L[𝕜] E => T (C x))
      (nuclearTransportDual_comm_cosine K L D).eq).symm
  change V (C (V (C x))) = _
  rw [hCV, hCCx, map_smul, map_smul, hVxx]
  module

/-- Independent local projection parameters for nuclear transport. These
are linear-algebraic spectral conditions, with no hidden transporter
or minimization predicate. -/
@[expose] def nuclearSignedSineSpectralFactors
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (μ : {μ : 𝕜 // μ ≠ 0}) :
    Set (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap μ.val →L[𝕜]
      Module.End.eigenspace (K.sinAngleOperator L).toLinearMap μ.val) :=
  spectralSignProjectionFactors (K.sinAngleOperator L)
    ((nuclearTransportDual K L D : E →L[𝕜] E) * Proposition35.section3CosAngleOperator K L)
    K.reflection (nuclear_spectral_symmetries_comm_sine K L D).1
    (nuclear_spectral_symmetries_comm_sine K L D).2 μ

/-- Oddness under source-reflection conjugation is exactly the zero
anticommutator equation. This retains every fixed ambient direction. -/
theorem reflection_conj_eq_neg_iff_anticommutator_zero
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    K.reflection.conjStarAlgEquiv A = -A ↔
      A * (K.reflection : E →L[𝕜] E) + (K.reflection : E →L[𝕜] E) * A = 0 := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun B : E →L[𝕜] E => B (K.reflection x)) h
    change K.reflection (A (K.reflection.symm (K.reflection x))) = -A (K.reflection x) at hx
    rw [K.reflection.symm_apply_apply] at hx
    change A (K.reflection x) + K.reflection (A x) = 0
    rw [hx, add_neg_cancel]
  · intro h
    ext x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, K.reflection_symm]
    have hx := congrArg (fun B : E →L[𝕜] E => B (K.reflection x)) h
    change A (K.reflection (K.reflection x)) + K.reflection (A (K.reflection x)) = 0 at hx
    rw [K.reflection_reflection] at hx
    exact eq_neg_of_add_eq_zero_right hx

/-- **All spectral root factors, independently and topologically.**
Repeated-angle mixing is precisely the freedom in the local projection
factor. The zero sine eigenspace has no factor. Zero cosine is allowed,
so the right-angle block is governed only by its reflection equation. -/
theorem exists_nuclearSignedSine_spectral_homeomorph
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    ∃ e : (∀ μ, nuclearSignedSineSpectralFactors K L D μ) ≃ₜ
        nuclearSignedSineParameters K L D,
      ∀ Q (μ : {μ : 𝕜 // μ ≠ 0})
        (x : Module.End.eigenspace (K.sinAngleOperator L).toLinearMap μ.val),
        (e Q).val x = μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := by
  let S := K.sinAngleOperator L
  let G := (nuclearTransportDual K L D : E →L[𝕜] E) * Proposition35.section3CosAngleOperator K L
  let J : E →L[𝕜] E := K.reflection
  have hSc : IsCompactOperator S := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hsv : S.singularValue = (K.starProjection - L.starProjection).singularValue := by
      funext n
      rw [show S = (K.starProjection - L.starProjection).modulus from K.sinAngleOperator_def L,
        ContinuousLinearMap.singularValue_modulus]
    rw [hsv]
    exact hcompact.tendsto_singularValue
  obtain ⟨e, he⟩ := exists_compact_modulus_symmetry_spectral_homeomorph S
    (K.isPositive_sinAngleOperator L) hSc G J
    (nuclear_spectral_symmetries_comm_sine K L D).1
    (nuclear_spectral_symmetries_comm_sine K L D).2
  have hsets : {A : E →L[𝕜] E | IsSelfAdjoint A ∧ A.modulus = S ∧
      Commute A G ∧ A * J + J * A = 0} = nuclearSignedSineParameters K L D := by
    ext A
    simp only [Set.mem_ofPred_eq, mem_nuclearSignedSineParameters,
      reflection_conj_eq_neg_iff_anticommutator_zero, S, G, J]
  exact ⟨e.trans (Homeomorph.setCongr hsets), he⟩

/-- **Exact spectral solvability criterion for signed roots.** Every
nonzero sine block must admit its indicated local projection, and those
local choices suffice jointly. This criterion is valid over the reals
as well as the complexes; it does not identify real roots with every
real optimizer when the real minimum exceeds the projection bound. -/
theorem nuclearSignedSineParameters_nonempty_iff_spectral_factors
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    (nuclearSignedSineParameters K L D).Nonempty ↔
      ∀ μ, (nuclearSignedSineSpectralFactors K L D μ).Nonempty := by
  classical
  obtain ⟨e, _⟩ := exists_nuclearSignedSine_spectral_homeomorph K L D hcompact
  constructor
  · rintro ⟨A, hA⟩ μ
    exact ⟨(e.symm ⟨A, hA⟩ μ).val, (e.symm ⟨A, hA⟩ μ).property⟩
  · intro h
    let Q : ∀ μ, nuclearSignedSineSpectralFactors K L D μ := fun μ =>
      ⟨(h μ).choose, (h μ).choose_spec⟩
    exact ⟨(e Q).val, (e Q).property⟩

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Every ambient complex nuclear optimizer has independent spectral
projection factors.** This is a homeomorphism onto the entire optimizer
set, not just a family of constructed competitors. Its hypotheses allow
infinite rank, nonseparable fixed directions and right-angle defects. -/
theorem exists_nuclear_optimizer_spectral_homeomorph_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    Nonempty ((∀ μ, nuclearSignedSineSpectralFactors K L D μ) ≃ₜ
      nuclearTransportOptimizers K L) := by
  have hcompact := ContinuousLinearMap.isCompactOperator_of_nuclearENorm_ne_top hΔ
  obtain ⟨s, _⟩ := exists_nuclearSignedSine_spectral_homeomorph K L D hcompact
  let : CompactSpace (nuclearSignedSineParameters K L D) :=
    isCompact_iff_compactSpace.mp (isCompact_nuclearSignedSineParameters K L D hcompact)
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  have hc : Continuous (fun A : nuclearSignedSineParameters K L D =>
      ((e A).val : F →L[ℂ] F)) :=
    (nuclearSignedSineEquivOptimizers_isometry_complex K L D hΔ).continuous
  have hcu : Continuous (fun A : nuclearSignedSineParameters K L D => (e A).val) :=
    LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.isInducing.continuous_iff.mpr hc
  have hce : Continuous e := hcu.subtype_mk _
  exact ⟨s.trans (e.toHomeomorphOfContinuousClosed hce hce.isClosedMap)⟩

end Complex

end TauCeti.DavisKahan
