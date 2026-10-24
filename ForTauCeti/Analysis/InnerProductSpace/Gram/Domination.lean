/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Factor

/-!
# Contractive factorization from Gram domination

The accepted `factorThru` construction gives the one-sided Douglas
factorization when the source Gram operator of `T` is dominated by that of `A`.
This retains the genuinely missing domination consequence of the former
`Polar/GramContraction.lean`; its equality construction is supplied upstream.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  {T : E →L[𝕜] F} {A : E →L[𝕜] G}

/-- Gram domination implies pointwise norm domination, allowing different
codomain spaces. -/
theorem norm_apply_le_of_gram_le (h : T.adjoint ∘L T ≤ A.adjoint ∘L A) (x : E) :
    ‖T x‖ ≤ ‖A x‖ := by
  have hpos := (ContinuousLinearMap.le_def).mp h
  have hn := hpos.re_inner_nonneg_left x
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, map_sub, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hn
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by linarith)

/-- **One-sided Douglas factorization.** Gram domination yields a
contractive factor through `A`, including rectangular source and target maps. -/
theorem exists_contraction_of_gram_le (h : T.adjoint ∘L T ≤ A.adjoint ∘L A) :
    ∃ W : G →L[𝕜] F, ‖W‖ ≤ 1 ∧ W ∘L A = T := by
  have hnorm (x : E) : ‖T x‖ ≤ 1 * ‖A x‖ := by
    rw [one_mul]
    exact norm_apply_le_of_gram_le h x
  exact ⟨T.factorThru A, norm_factorThru_le zero_le_one hnorm, factorThru_comp ⟨1, hnorm⟩⟩

end ContinuousLinearMap
