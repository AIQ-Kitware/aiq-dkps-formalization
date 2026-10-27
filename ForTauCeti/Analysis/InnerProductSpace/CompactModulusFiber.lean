/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact self-adjoint fibers of a compact modulus

For a positive compact operator S on any complete real or complex
Hilbert space, the self-adjoint operators of modulus S form a compact
set in operator norm. Finite spectral compressions of S approximate
the whole fiber uniformly; no separability is assumed.

## Provenance

Developed in the DKPS repository to prove compactness of the nuclear
transport optimizer family. The proof uses existing compact spectral
cutoffs, modulus norm identities, and finite-dimensional compact balls.
This is new local proof code, not copied from Spectra or an external
source. No historical priority or accepted roadmap ownership is asserted.
-/

public section

noncomputable section

namespace TauCeti

attribute [local instance] _root_.ContinuousLinearMap.realAlgebra
  _root_.ContinuousLinearMap.realIsScalarTower

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

private theorem exists_compact_approximation_modulus_fiber
    (S : E →L[𝕜] E) (hS : S.IsPositive) (hSc : IsCompactOperator S)
    (c : ℝ) (hc : 0 < c) :
    ∃ K : Set (E →L[𝕜] E), IsCompact K ∧ ∀ A : E →L[𝕜] E,
      IsSelfAdjoint A → A.modulus = S → ∃ B ∈ K, ‖A - B‖ ≤ 2 * c := by
  let M := eigenSpan S (Set.Ioi c)
  let : FiniteDimensional 𝕜 M :=
    finiteDimensional_eigenSpan hSc hS.isSelfAdjoint hc (fun _ hs => hs.le)
  let : CompleteSpace M := inferInstance
  let P := M.starProjection
  let extend (B : M →L[𝕜] M) : E →L[𝕜] E := M.subtypeL ∘L B ∘L M.orthogonalProjectionOnto
  let : ProperSpace (M →L[𝕜] M) := FiniteDimensional.proper 𝕜 _
  have hext : Continuous extend := by fun_prop
  let K := extend '' Metric.closedBall (0 : M →L[𝕜] M) ‖S‖
  have hK : IsCompact K := (isCompact_closedBall (0 : M →L[𝕜] M) ‖S‖).image hext
  have htailS : ‖S ∘L Mᗮ.subtypeL‖ ≤ c :=
    norm_comp_orthogonal_eigenSpan_le hSc hS.isSelfAdjoint
      hS.re_inner_nonneg_left hc.le (fun _ hs => hs)
  refine ⟨K, hK, ?_⟩
  intro A hA hmod
  let B : M →L[𝕜] M := M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL
  have hAnorm : ‖A‖ = ‖S‖ := A.norm_modulus.symm.trans (congrArg norm hmod)
  have hBnorm : ‖B‖ ≤ ‖S‖ := by
    apply B.opNorm_le_bound (norm_nonneg S)
    intro x
    calc
      _ ≤ ‖A (x : E)‖ := M.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ ‖A‖ * ‖x‖ := A.le_opNorm _
      _ = _ := by rw [hAnorm]
  have hBmem : extend B ∈ K :=
    ⟨B, by simpa only [Metric.mem_closedBall, dist_zero_right] using hBnorm, rfl⟩
  have hextB : extend B = P * A * P := by ext x; rfl
  have htailA : ‖A ∘L Mᗮ.subtypeL‖ ≤ c := by
    rw [← ContinuousLinearMap.norm_modulus_comp A, hmod]
    exact htailS
  have hright : ‖A * (1 - P)‖ ≤ c := by
    have hperp : 1 - P = Mᗮ.starProjection := (Submodule.starProjection_orthogonal' M).symm
    rw [hperp]
    apply ContinuousLinearMap.opNorm_le_bound _ hc.le
    intro x
    change ‖A (Mᗮ.starProjection x)‖ ≤ c * ‖x‖
    calc
      _ = ‖(A ∘L Mᗮ.subtypeL) (Mᗮ.orthogonalProjectionOnto x)‖ := rfl
      _ ≤ ‖A ∘L Mᗮ.subtypeL‖ * ‖Mᗮ.orthogonalProjectionOnto x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖Mᗮ.orthogonalProjectionOnto x‖ := mul_le_mul_of_nonneg_right htailA (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Mᗮ.norm_orthogonalProjectionOnto_apply_le x) hc.le
  have hP : IsSelfAdjoint P := isSelfAdjoint_starProjection M
  have hleft : ‖(1 - P) * A‖ = ‖A * (1 - P)‖ := by
    calc
      _ = ‖star ((1 - P) * A)‖ := (ContinuousLinearMap.adjoint.norm_map _).symm
      _ = _ := by rw [star_mul, hA.star_eq, star_sub, star_one, hP.star_eq]
  have hleftP : ‖((1 - P) * A) * P‖ ≤ c := by
    calc
      _ ≤ ‖(1 - P) * A‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖(1 - P) * A‖ * 1 := mul_le_mul_of_nonneg_left
        (IsStarProjection.norm_le P (isStarProjection_starProjection (U := M))) (norm_nonneg _)
      _ = ‖A * (1 - P)‖ := by rw [mul_one, hleft]
      _ ≤ c := hright
  refine ⟨extend B, hBmem, ?_⟩
  rw [hextB]
  have hdiff : A - P * A * P = A * (1 - P) + ((1 - P) * A) * P := by noncomm_ring
  rw [hdiff]
  exact (norm_add_le _ _).trans (by linarith)

/-- Self-adjoint operators with a prescribed positive modulus form
a closed set in operator norm. Compactness of the modulus is not needed. -/
theorem isClosed_setOf_isSelfAdjoint_modulus_eq (S : E →L[𝕜] E) (hS : S.IsPositive) :
    IsClosed {A : E →L[𝕜] E | IsSelfAdjoint A ∧ A.modulus = S} := by
  have heq : {A : E →L[𝕜] E | IsSelfAdjoint A ∧ A.modulus = S} =
      {A : E →L[𝕜] E | star A = A ∧ star A * A = S * S} := by
    ext A
    constructor
    · rintro ⟨hA, hmod⟩
      refine ⟨hA.star_eq, ?_⟩
      have h := A.modulus_comp_modulus
      change A.modulus * A.modulus = star A * A at h
      rw [hmod] at h
      exact h.symm
    · rintro ⟨hA, hgram⟩
      refine ⟨hA, ?_⟩
      exact ((ContinuousLinearMap.eq_modulus_iff).mpr
        ⟨hS, by change S * S = star A * A; exact hgram.symm⟩).symm
  rw [heq]
  exact (isClosed_eq continuous_star continuous_id).inter
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const)

/-- **Compactness of a self-adjoint fixed-modulus fiber.** The entire
fiber is norm compact whenever the prescribed positive modulus is
compact, even on a nonseparable Hilbert space. -/
theorem isCompact_setOf_isSelfAdjoint_modulus_eq
    (S : E →L[𝕜] E) (hS : S.IsPositive) (hSc : IsCompactOperator S) :
    IsCompact {A : E →L[𝕜] E | IsSelfAdjoint A ∧ A.modulus = S} := by
  have htb : TotallyBounded {A : E →L[𝕜] E | IsSelfAdjoint A ∧ A.modulus = S} := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨K, hK, happrox⟩ :=
      exists_compact_approximation_modulus_fiber S hS hSc (ε / 4) (by positivity)
    obtain ⟨t, htfinite, htcover⟩ :=
      Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 4) (by positivity)
    refine ⟨t, htfinite, ?_⟩
    intro A hA
    obtain ⟨B, hBK, hAB⟩ := happrox A hA.1 hA.2
    have hBc : ∃ y ∈ t, dist B y < ε / 4 := by
      simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using htcover hBK
    obtain ⟨y, hyt, hBy⟩ := hBc
    have hAy : dist A y < ε := by
      have hab : dist A B ≤ 2 * (ε / 4) := by rwa [dist_eq_norm]
      have htri := dist_triangle A B y
      linarith
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using ⟨y, hyt, hAy⟩
  exact htb.isCompact_of_isClosed (isClosed_setOf_isSelfAdjoint_modulus_eq S hS)

end TauCeti
