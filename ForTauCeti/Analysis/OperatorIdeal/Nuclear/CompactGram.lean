/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.CompactSpectralTrace
public import TauCeti.Analysis.OperatorIdeal.Nuclear.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# The compact Gram trace identity over both scalar fields

The nuclear gauge of a compact Gram operator is the Hilbert--Schmidt
energy of its factor. The proof uses the compact spectral theorem and
the existing exact positive-eigenvalue multiplicity formula. Arbitrary
kernel dimension and infinite energy are retained. This is a classical
trace/ideal identity, not a mathematical novelty claim; it supplies the
real-field analytic ingredient for the transport equality certificate.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open TauCeti
open scoped InnerProductSpace ENNReal NNReal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The nuclear gauge of a compact Gram operator equals its factor's
Hilbert--Schmidt energy in any Hilbert basis, over either field. -/
theorem nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_of_compact
    (T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hc : IsCompactOperator (T.adjoint ∘L T)) :
    (T.adjoint ∘L T).nuclearENorm = T.hilbertSchmidtEnergy b := by
  classical
  let S := T.adjoint ∘L T
  have hS : S.IsPositive := isPositive_adjoint_comp_self T
  let N := fun μ : ℝ≥0 => Module.End.eigenspace S.toLinearMap ((μ : ℝ) : 𝕜)
  let (μ : ℝ≥0) : CompleteSpace (N μ) :=
    (isClosed_eigenspace S ((μ : ℝ) : 𝕜)).completeSpace_coe
  choose I e he using fun μ : ℝ≥0 => exists_hilbertBasis 𝕜 (N μ)
  let v : (Σ μ : ℝ≥0, I μ) → E := fun a => (e a.1 a.2 : E)
  have hortho : OrthogonalFamily 𝕜 (fun μ : ℝ≥0 => N μ) (fun μ => (N μ).subtypeₗᵢ) :=
    (orthogonalFamily_eigenspace_real hS.isSelfAdjoint).comp NNReal.coe_injective
  have hv : Orthonormal 𝕜 v :=
    hortho.orthonormal_sigma_orthonormal (fun μ => (e μ).orthonormal)
  let M := Submodule.span 𝕜 (Set.range v)
  have hNM (μ : ℝ≥0) : N μ ≤ M.topologicalClosure := by
    have hlocal : (Submodule.span 𝕜 (Set.range (e μ))).map (N μ).subtype ≤ M := by
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩
    have h := (Submodule.span 𝕜 (Set.range (e μ))).topologicalClosure_map (N μ).subtypeL
    rw [(e μ).dense_span, Submodule.map_top] at h
    change (N μ).subtype.range ≤
      ((Submodule.span 𝕜 (Set.range (e μ))).map (N μ).subtype).topologicalClosure at h
    rw [Submodule.range_subtype] at h
    exact h.trans (Submodule.topologicalClosure_mono hlocal)
  have hall : (⨆ μ : 𝕜, Module.End.eigenspace S.toLinearMap μ) ≤ M.topologicalClosure := by
    refine iSup_le fun μ => ?_
    by_cases hz : Module.End.eigenspace S.toLinearMap μ = ⊥
    · rw [hz]; exact bot_le
    obtain ⟨hreal, hnonneg⟩ := eq_ofReal_re_of_eigenspace_ne_bot
      hS.isSelfAdjoint hS.re_inner_nonneg_left hz
    rw [hreal]
    exact hNM ⟨RCLike.re μ, hnonneg⟩
  have htotal : ⊤ ≤ M.topologicalClosure := by
    have h := Submodule.topologicalClosure_minimal _ hall (Submodule.isClosed_topologicalClosure M)
    rw [Submodule.topologicalClosure_eq_top_iff.mpr
      (orthogonalComplement_iSup_eigenspaces_eq_bot hc hS.isSymmetric)] at h
    exact h
  let c : HilbertBasis (Σ μ : ℝ≥0, I μ) 𝕜 E := HilbertBasis.mk hv htotal
  have hcval (a : Σ μ : ℝ≥0, I μ) : c a = (e a.1 a.2 : E) := by
    exact congrFun (HilbertBasis.coe_mk hv htotal) a
  have hnorm (a : Σ μ : ℝ≥0, I μ) : ‖T (c a)‖ ^ 2 = (a.1 : ℝ) := by
    have hx := Module.End.mem_eigenspace_iff.mp (e a.1 a.2).property
    change S (e a.1 a.2 : E) = ((a.1 : ℝ) : 𝕜) • (e a.1 a.2 : E) at hx
    have hn : ‖(e a.1 a.2 : E)‖ = 1 := (N a.1).subtypeₗᵢ.norm_map _ |>.trans
      ((e a.1).orthonormal.1 a.2)
    have hinner := T.adjoint_inner_right (c a) (T (c a))
    change ⟪c a, S (c a)⟫_𝕜 = ⟪T (c a), T (c a)⟫_𝕜 at hinner
    rw [hcval, hx, inner_smul_right, inner_self_eq_norm_sq_to_K, hn] at hinner
    have h := congrArg RCLike.re hinner
    simpa only [hcval, one_pow, RCLike.ofReal_one, mul_one, RCLike.ofReal_re,
      inner_self_eq_norm_sq] using h.symm
  rw [T.hilbertSchmidtEnergy_indep b c, hilbertSchmidtEnergy_def]
  have hdiag (a : Σ μ : ℝ≥0, I μ) : ‖T (c a)‖ₑ ^ 2 = (a.1 : ℝ≥0∞) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hnorm]
    exact ENNReal.ofReal_coe_nnreal
  simp_rw [hdiag]
  trans ∑' μ : ℝ≥0, ∑' _i : I μ, (μ : ℝ≥0∞)
  · change S.nuclearENorm = _
    rw [nuclearENorm_def,
      tsum_singularValue_penalty_eq_tsum_eigenspace S hc hS (fun μ => (μ : ℝ≥0∞)) (by simp)]
    apply tsum_congr
    intro μ
    by_cases hz : μ = 0
    · simp [hz]
    let : FiniteDimensional 𝕜 (N μ) := finite_dimensional_eigenspace hc _
      (by exact_mod_cast hz)
    let : Finite (I μ) := (e μ).orthonormal.linearIndependent.finite
    let : Fintype (I μ) := Fintype.ofFinite _
    have hcard : Module.finrank 𝕜 (N μ) = Fintype.card (I μ) :=
      Module.finrank_eq_card_basis (e μ).toOrthonormalBasis.toBasis
    rw [hcard, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · exact (ENNReal.tsum_sigma (fun (μ : ℝ≥0) (_ : I μ) => (μ : ℝ≥0∞))).symm

end ContinuousLinearMap
