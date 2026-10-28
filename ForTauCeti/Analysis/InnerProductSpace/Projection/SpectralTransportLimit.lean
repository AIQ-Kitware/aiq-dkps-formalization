/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteSpectralTrace
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# A common spectral transport lower-bound lift

A finite complex angle-sum lower bound lifts to arbitrary Hilbert dimension
when the displacement penalty is increasing, finite cost forces compact
unitary displacement, and the angle penalty is continuous. Spectral unitary
truncations decrease every displacement singular value and converge in norm.
Their targets move; fixed-fiber compression is not assumed.

This proof abstracts `CharbonnierGlobalLowerBound` and its Schatten analogue.
The approximation, singular-value continuity and finite reducing-section
ingredients are classical formalized mathematics. The constrained transport
lifting principle is a derived extension; exact historical priority remains
unresolved in the maintained unification/provenance note.
-/

public section
noncomputable section

namespace TauCeti

open Set Filter
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Finite-to-Hilbert spectral transport principle.** The finite
hypothesis is imposed only on actual finite sections. The conclusion covers
every ambient unitary transporter, including divergent extended costs. -/
theorem tsum_angle_penalty_le_displacement_of_finite_transport_bound
    (f : ℝ≥0 → ℝ≥0∞) (hf : Monotone f)
    (m : ℝ → ℝ≥0∞) (hm0 : m 0 = 0) (hm : ContinuousOn m (Icc 0 (Real.pi / 2)))
    (hcompact : ∀ U : E ≃ₗᵢ[ℂ] E,
      (∑' j, f ((1 - (U : E →L[ℂ] E)).singularValue j)) ≠ ∞ →
        IsCompactOperator (((U : E →L[ℂ] E) - 1) : E →L[ℂ] E))
    (hfinite : ∀ (M : Submodule ℂ E) [FiniteDimensional ℂ M]
      (K L : Submodule ℂ M) (U : M ≃ₗᵢ[ℂ] M), K.map U.toLinearMap = L →
        (∑ i : Fin (Module.finrank ℂ K), m (K.principalAngles L i)) ≤
          ∑' j, f ((1 - (U : M →L[ℂ] M)).singularValue j))
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (∑' j, m (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ≤
      ∑' j, f ((1 - (U : E →L[ℂ] E)).singularValue j) := by
  have hfinite_rank (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
      (V : E ≃ₗᵢ[ℂ] E) (hVmap : K.map V.toLinearMap = L)
      (n : ℕ) (hV : (1 - V.toLinearMap).rank ≤ n) :
      (∑' j, m (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ≤
        ∑' j, f ((1 - (V : E →L[ℂ] E)).singularValue j) := by
    obtain ⟨M, hM, _, W, _, hlocal, hK, hL, heq, hdisp⟩ :=
      K.exists_finite_transport_section L ⊥ V hVmap n hV
    let : FiniteDimensional ℂ M := hM
    rw [Submodule.tsum_sine_penalty_eq_principalAngle_sum_of_finite_core K L M hK hL heq m hm0,
      hdisp]
    simp_rw [ContinuousLinearMap.singularValue_orthogonal_extension]
    exact hfinite M (K.comap M.subtype) (L.comap M.subtype) W hlocal
  by_cases hU : (∑' j, f ((1 - (U : E →L[ℂ] E)).singularValue j)) = ∞
  · rw [hU]
    exact le_top
  obtain ⟨V, N, hN, hlim, _, _, hdom, _⟩ :=
    exists_finite_unitary_approximation_sequence U (hcompact U hU)
  let S (A : E →L[ℂ] E) := (1 - A * K.starProjection * star A) * K.starProjection
  have hS : Continuous S := by dsimp only [S]; fun_prop
  have hsin (W : E ≃ₗᵢ[ℂ] E) : K.sinThetaMap (K.map W.toLinearMap) = S (W : E →L[ℂ] E) := by
    have hproj := (K.map_eq_iff_conjugate_starProjection (K.map W.toLinearMap) W).mp rfl
    rw [Submodule.sinThetaMap_def, Submodule.starProjection_orthogonal, ← hproj]
    rfl
  have hterm (j : ℕ) :
      Continuous (fun A : E →L[ℂ] E => m (Real.arcsin (A.singularValue j : ℝ))) := by
    have hangle : Continuous (fun A : E →L[ℂ] E => Real.arcsin (A.singularValue j : ℝ)) :=
      Real.continuous_arcsin.comp (NNReal.continuous_coe.comp
        (ContinuousLinearMap.continuous_singularValue j))
    exact hm.comp_continuous hangle (fun A =>
      ⟨Real.arcsin_nonneg.mpr (NNReal.coe_nonneg _), Real.arcsin_le_pi_div_two _⟩)
  suffices (∑' j, m (Real.arcsin ((S (U : E →L[ℂ] E)).singularValue j : ℝ))) ≤
      ∑' j, f ((1 - (U : E →L[ℂ] E)).singularValue j) by
    simpa only [← hsin, hmap] using this
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hterms (j : ℕ) := (((hterm j).comp hS).tendsto (U : E →L[ℂ] E)).comp hlim
  apply le_of_tendsto' (tendsto_finsetSum s (fun j _ => hterms j))
  intro n
  calc
    _ ≤ ∑' j, m (Real.arcsin ((S (V n : E →L[ℂ] E)).singularValue j : ℝ)) :=
      ENNReal.sum_le_tsum s
    _ = ∑' j, m (Real.arcsin ((K.sinThetaMap (K.map (V n).toLinearMap)).singularValue j : ℝ)) := by
      rw [← hsin]
    _ ≤ ∑' j, f ((1 - (V n : E →L[ℂ] E)).singularValue j) :=
      hfinite_rank K (K.map (V n).toLinearMap) (V n) rfl (N n) (hN n)
    _ ≤ _ := ENNReal.tsum_le_tsum (fun j => hf (hdom n j))

end TauCeti
