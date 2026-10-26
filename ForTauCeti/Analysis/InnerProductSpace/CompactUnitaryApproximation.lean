/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryTruncation
public import ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus
public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining

/-!
# Compact unitary perturbations admit cost-decreasing finite truncations

Spectral cutoffs of the displacement modulus are finite invariant
subspaces. Keeping the unitary on those subspaces and replacing it by
identity on their complements gives operator-norm approximation without
increasing any accepted operator-ideal gauge of the displacement.

## Provenance

Classical compact spectral truncation, implemented here for the DKPS
infinite-dimensional optimization argument. This formulation needs no
separability, eigenbasis choice for the kernel, or Schatten-norm density
assumption. No independent historical-priority claim is made.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter
open scoped InnerProductSpace Topology

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every operator commuting with `A` preserves every real eigenvalue
band span of `A`, without a dimension or self-adjointness assumption. -/
theorem eigenSpan_invariant_of_commute (A B : E →L[𝕜] E) (h : Commute B A) (S : Set ℝ) :
    ∀ x ∈ eigenSpan A S, B x ∈ eigenSpan A S := by
  have hle : eigenSpan A S ≤ Submodule.comap B.toLinearMap (eigenSpan A S) := by
    refine eigenSpan_le A fun s hs x hx => ?_
    apply eigenspace_le_eigenSpan A hs
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change A x = (s : 𝕜) • x at hx
    calc
      A (B x) = B (A x) := (congrArg (fun T : E →L[𝕜] E => T x) h.eq).symm
      _ = (s : 𝕜) • B x := by rw [hx, map_smul]
  exact fun x hx => hle hx

/-- A compact positive operator has norm at most `c` on the orthogonal
complement of any eigenvalue band covering all eigenvalues above `c`. -/
theorem norm_comp_orthogonal_eigenSpan_le {A : E →L[𝕜] E}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    {S : Set ℝ} {c : ℝ} (hc : 0 ≤ c) (hcover : ∀ s, c < s → s ∈ S) :
    ‖A ∘L (eigenSpan A S)ᗮ.subtypeL‖ ≤ c := by
  apply norm_comp_subtypeL_orthogonal_le hAc hAs (eigenSpan_invariant A S) hc
  intro ν x hx hx0 hxeq
  have hxE : x ∈ Module.End.eigenspace A.toLinearMap ν :=
    Module.End.mem_eigenspace_iff.mpr hxeq
  have hE : Module.End.eigenspace A.toLinearMap ν ≠ ⊥ := by
    intro hbot
    exact hx0 (by simpa [hbot] using hxE)
  obtain ⟨hreal, hnonneg⟩ := eq_ofReal_re_of_eigenspace_ne_bot hAs hApos hE
  have hle : RCLike.re ν ≤ c := by
    by_contra hnot
    have hxE' : x ∈ Module.End.eigenspace A.toLinearMap ((RCLike.re ν : ℝ) : 𝕜) := by
      rwa [← hreal]
    have hxM := eigenspace_le_eigenSpan A (hcover _ (lt_of_not_ge hnot)) hxE'
    have hinter : x ∈ eigenSpan A S ⊓ (eigenSpan A S)ᗮ := ⟨hxM, hx⟩
    rw [(Submodule.orthogonal_disjoint (eigenSpan A S)).eq_bot, Submodule.mem_bot] at hinter
    exact hx0 hinter
  calc
    ‖ν‖ = |RCLike.re ν| := by conv_lhs => rw [hreal]; exact RCLike.norm_ofReal _
    _ = RCLike.re ν := abs_of_nonneg hnonneg
    _ ≤ c := hle

private theorem commute_displacement_modulus (U : E ≃ₗᵢ[𝕜] E) (B : E →L[𝕜] E)
    (hBU : Commute B (U : E →L[𝕜] E)) :
    Commute B (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E).modulus := by
  let u : unitary (E →L[𝕜] E) := Unitary.linearIsometryEquiv.symm U
  have hBUstar : Commute B (star (U : E →L[𝕜] E)) :=
    ContinuousLinearMap.comp_star_eq_star_comp_of_mem_unitary B u.property u.property hBU.eq
  apply ContinuousLinearMap.commute_modulus_of_commute
  change Commute B (star ((U : E →L[𝕜] E) - 1) * ((U : E →L[𝕜] E) - 1))
  rw [star_sub, star_one]
  exact (hBUstar.sub_right (Commute.one_right _)).mul_right
    (hBU.sub_right (Commute.one_right _))

/-- Every compact perturbation of identity in the unitary group admits
a finite-rank unitary approximation at any positive tolerance, with no
increase of its displacement in any accepted operator-ideal gauge. -/
theorem exists_finite_unitary_approximation
    (U : E ≃ₗᵢ[𝕜] E)
    (hcompact : IsCompactOperator (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : E ≃ₗᵢ[𝕜] E, ∃ n : ℕ,
      (1 - (V : E →L[𝕜] E)).rank ≤ n ∧
      ‖(V : E →L[𝕜] E) - (U : E →L[𝕜] E)‖ ≤ ε ∧
      (∀ k, ((V : E →L[𝕜] E) - (U : E →L[𝕜] E)).singularValue k ≤
        (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E).singularValue k) ∧
      (∀ Φ : OperatorIdealFamily.{u, v, v} 𝕜,
        Φ.gauge (1 - (V : E →L[𝕜] E)) ≤ Φ.gauge (1 - (U : E →L[𝕜] E))) ∧
      ∀ B : E →L[𝕜] E, Commute (U : E →L[𝕜] E) B → Commute (V : E →L[𝕜] E) B := by
  let T : E →L[𝕜] E := (U : E →L[𝕜] E) - 1
  let A := T.modulus
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = T.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus T n)
    rw [hseq]
    exact hcompact.tendsto_singularValue
  have hAs : IsSelfAdjoint A := T.isSelfAdjoint_modulus
  have hApos (x : E) : 0 ≤ RCLike.re ⟪A x, x⟫_𝕜 :=
    T.isPositive_modulus.re_inner_nonneg_left x
  have hUA : Commute (U : E →L[𝕜] E) A :=
    commute_displacement_modulus U _ (Commute.refl _)
  let M := eigenSpan A (Ici ε)
  have : FiniteDimensional 𝕜 M := finiteDimensional_eigenSpan hAc hAs hε (fun _ hs => hs)
  have hUM : ∀ x ∈ M, U x ∈ M := eigenSpan_invariant_of_commute A _ hUA _
  obtain ⟨V, _, _, hfactor, herror, hVrank, hVerr, hVcost⟩ :=
    exists_finite_unitary_truncation U M hUM
  have htail : ‖A ∘L Mᗮ.subtypeL‖ ≤ ε :=
    norm_comp_orthogonal_eigenSpan_le hAc hAs hApos hε.le (fun _ hs => hs.le)
  have hTtail : ‖T ∘L Mᗮ.subtypeL‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ hε.le
    intro x
    change ‖T (x : E)‖ ≤ ε * ‖x‖
    calc
      _ = ‖A (x : E)‖ := (T.norm_modulus_apply (x : E)).symm
      _ ≤ ‖A ∘L Mᗮ.subtypeL‖ * ‖x‖ := (A ∘L Mᗮ.subtypeL).le_opNorm x
      _ ≤ _ := mul_le_mul_of_nonneg_right htail (norm_nonneg x)
  refine ⟨V, Module.finrank 𝕜 M, hVrank, hVerr.trans hTtail, ?_, hVcost, ?_⟩
  · intro k
    have hneg : (-(T ∘L Mᗮ.starProjection)).singularValue k =
      (T ∘L Mᗮ.starProjection).singularValue k := by
      simpa only [neg_one_smul, nnnorm_neg, nnnorm_one, one_mul] using
        ContinuousLinearMap.singularValue_smul (-1 : 𝕜) (T ∘L Mᗮ.starProjection) k
    rw [herror, hneg]
    calc
      _ ≤ T.singularValue k * ‖Mᗮ.starProjection‖₊ :=
        ContinuousLinearMap.singularValue_comp_le_right T Mᗮ.starProjection k
      _ ≤ T.singularValue k * 1 := by
        gcongr
        exact_mod_cast Mᗮ.starProjection_norm_le
      _ = _ := mul_one _
  · intro B hUB
    have hBA : Commute B A := commute_displacement_modulus U B hUB.symm
    let u : unitary (E →L[𝕜] E) := Unitary.linearIsometryEquiv.symm U
    have hBUstar : Commute B (star (U : E →L[𝕜] E)) :=
      ContinuousLinearMap.comp_star_eq_star_comp_of_mem_unitary B u.property u.property hUB.symm.eq
    have hBstarU : Commute (star B) (U : E →L[𝕜] E) := by
      simpa only [star_star] using commute_star_star.mpr hBUstar
    have hBstarA : Commute (star B) A := commute_displacement_modulus U _ hBstarU
    have hred : M.IsReducing B :=
      ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr
        ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
            (eigenSpan_invariant_of_commute A B hBA _),
          (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
            (eigenSpan_invariant_of_commute A (star B) hBstarA _)⟩
    have hMB : Commute M.starProjection B :=
      Submodule.isReducing_coe_iff_commute_starProjection.mp hred
    have hpoly := ((Commute.one_left B).sub_left hUB).mul_left hMB
    change Commute ((1 - (U : E →L[𝕜] E)) ∘L M.starProjection) B at hpoly
    rw [← hfactor] at hpoly
    simpa only [sub_sub_cancel] using (Commute.one_left B).sub_left hpoly

/-- Compact unitary perturbations are operator-norm limits of finite-rank
unitary perturbations, with every displacement gauge bounded by the
original one at every stage. The same sequence works for all families. -/
theorem exists_finite_unitary_approximation_sequence
    (U : E ≃ₗᵢ[𝕜] E)
    (hcompact : IsCompactOperator (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E)) :
    ∃ V : ℕ → E ≃ₗᵢ[𝕜] E, ∃ N : ℕ → ℕ,
      (∀ n, (1 - (V n : E →L[𝕜] E)).rank ≤ N n) ∧
      Tendsto (fun n => (V n : E →L[𝕜] E)) atTop (𝓝 (U : E →L[𝕜] E)) ∧
      (∀ n k, ((V n : E →L[𝕜] E) - (U : E →L[𝕜] E)).singularValue k ≤
        (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E).singularValue k) ∧
      (∀ n (Φ : OperatorIdealFamily.{u, v, v} 𝕜),
        Φ.gauge (1 - (V n : E →L[𝕜] E)) ≤ Φ.gauge (1 - (U : E →L[𝕜] E))) ∧
      ∀ n (B : E →L[𝕜] E), Commute (U : E →L[𝕜] E) B → Commute (V n : E →L[𝕜] E) B := by
  choose V N hN hbound hdom hcost hcomm using fun n : ℕ =>
    exists_finite_unitary_approximation U hcompact (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨V, N, hN, tendsto_iff_norm_sub_tendsto_zero.mpr ?_, hdom, hcost, hcomm⟩
  exact squeeze_zero (fun _ => norm_nonneg _) hbound
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)))

end TauCeti
