/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierBlockSum
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction

/-!
# Exact spectral costs on an actual reducing decomposition

Use the canonical orthogonal decomposition of the Hilbert space to
identify an operator with its two actual compressed blocks. Schatten
powers and smoothed spectral costs then split exactly, including
infinite values. For compact operators this also holds for every
nonnegative zero-preserving spectral penalty.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An operator reducing an orthogonally complemented subspace is
exactly its two actual compressed blocks in the canonical decomposition. -/
theorem eq_orthogonal_block_of_isReducing
    (A : E →L[𝕜] E) (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (hM : M.IsReducing A.toLinearMap) :
    A = (M.orthogonalDecomposition.symm : WithLp 2 (M × Mᗮ) →L[𝕜] E) ∘L
      ((M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL).withLpProdMap 2
        (Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL)) ∘L
      (M.orthogonalDecomposition : E →L[𝕜] WithLp 2 (M × Mᗮ)) := by
  have hleft (x : M) :
      ((M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL) x : E) = A x := by
    change M.starProjection (A x) = A x
    exact M.starProjection_eq_self_iff.mpr (hM.mem_invtSubmodule x.property)
  have hright (x : Mᗮ) :
      ((Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL) x : E) = A x := by
    change Mᗮ.starProjection (A x) = A x
    exact Mᗮ.starProjection_eq_self_iff.mpr (hM.orthogonal_mem_invtSubmodule x.property)
  ext x
  change A x = M.orthogonalDecomposition.symm
    (((M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL).withLpProdMap 2
      (Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL)) (M.orthogonalDecomposition x))
  rw [withLpProdMap_apply, Submodule.orthogonalDecomposition_symm_apply,
    Submodule.fst_orthogonalDecomposition_apply, Submodule.snd_orthogonalDecomposition_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [hleft, hright]
  change A x = A (M.starProjection x) + A (Mᗮ.starProjection x)
  rw [← map_add, M.starProjection_add_starProjection_orthogonal]

/-- Actual reducing compression preserves the complete block singular
sequence, not only a majorization inequality. -/
theorem singularValue_eq_orthogonal_block_of_isReducing
    (A : E →L[𝕜] E) (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (hM : M.IsReducing A.toLinearMap) (n : ℕ) :
    A.singularValue n =
      ((M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL).withLpProdMap 2
        (Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL)).singularValue n := by
  conv_lhs => rw [A.eq_orthogonal_block_of_isReducing M hM]
  exact singularValue_comp_linearIsometryEquiv _ M.orthogonalDecomposition
    M.orthogonalDecomposition.symm n

variable [CompleteSpace E]

/-- Exact additive spectral penalties on the actual two reducing
compressions of a compact operator, including divergent sums. -/
theorem tsum_singularValue_penalty_eq_add_of_isReducing
    (A : E →L[𝕜] E) (hAc : IsCompactOperator A)
    (M : Submodule 𝕜 E) [M.HasOrthogonalProjection] (hM : M.IsReducing A.toLinearMap)
    (f : ℝ≥0 → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f (A.singularValue n)) =
      (∑' n, f ((M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL).singularValue n)) +
        ∑' n, f ((Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL).singularValue n) := by
  let : CompleteSpace M :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection M).completeSpace_coe
  simp_rw [A.singularValue_eq_orthogonal_block_of_isReducing M hM]
  exact tsum_singularValue_penalty_withLpProdMap _ _
    ((hAc.comp_clm M.subtypeL).clm_comp M.orthogonalProjectionOnto)
    ((hAc.comp_clm Mᗮ.subtypeL).clm_comp Mᗮ.orthogonalProjectionOnto) f hf

/-- **Native Schatten cost decomposition on a reducing subspace.**
The operator and both blocks may have infinite rank and infinite cost. -/
theorem gauge_schatten_rpow_eq_add_of_isReducing
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] E)
    (M : Submodule 𝕜 E) [M.HasOrthogonalProjection] [CompleteSpace M]
    (hM : M.IsReducing A.toLinearMap) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge A ^ p =
      (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge
          (M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL) ^ p +
        (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge
          (Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL) ^ p := by
  rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow]
  simp_rw [A.singularValue_eq_orthogonal_block_of_isReducing M hM]
  rw [← TauCeti.OperatorIdealFamily.gauge_schatten_rpow,
    TauCeti.OperatorIdealFamily.gauge_schatten_rpow_withLpProdMap]

/-- **Smoothed cost decomposition on an actual reducing subspace.**
Only a positive smoothing scale is assumed; both costs may diverge. -/
theorem charbonnierCost_eq_add_of_isReducing
    (tau : ℝ) (hτ : 0 < tau) (A : E →L[𝕜] E)
    (M : Submodule 𝕜 E) [M.HasOrthogonalProjection] (hM : M.IsReducing A.toLinearMap) :
    A.charbonnierCost tau =
      (M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL).charbonnierCost tau +
        (Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL).charbonnierCost tau := by
  let : CompleteSpace M :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection M).completeSpace_coe
  unfold charbonnierCost
  simp_rw [A.singularValue_eq_orthogonal_block_of_isReducing M hM]
  exact charbonnierCost_withLpProdMap tau hτ _ _

/-- An actual unitary replacement on a finite block has exactly the
new finite-block Schatten power plus its unchanged reference tail.
The identity includes infinite reference-tail costs. -/
theorem gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
    (p : ℝ) (hp : 1 ≤ p) (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M]
    (U R : E ≃ₗᵢ[𝕜] E) (W : M ≃ₗᵢ[𝕜] M)
    (hUM : ∀ x : M, U x = (W x : E)) (htail : ∀ x ∈ Mᗮ, U x = R x) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ^ p =
      (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M)) ^ p +
        (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge
          (Mᗮ.orthogonalProjectionOnto ∘L (1 - (R : E →L[𝕜] E)) ∘L Mᗮ.subtypeL) ^ p := by
  obtain ⟨_, _, _, hredU⟩ := U.exists_restriction_of_finite_invariant M (by
    intro x hx
    rw [hUM ⟨x, hx⟩]
    exact (W ⟨x, hx⟩).property)
  have hred : M.IsReducing (1 - (U : E →L[𝕜] E)).toLinearMap := by
    apply (M.isReducing_iff _).mpr
    constructor
    · intro x hx
      change x - U x ∈ M
      exact M.sub_mem hx (hredU.mem_invtSubmodule hx)
    · intro x hx
      change x - U x ∈ Mᗮ
      exact Mᗮ.sub_mem hx (hredU.orthogonal_mem_invtSubmodule hx)
  have hblock : M.orthogonalProjectionOnto ∘L (1 - (U : E →L[𝕜] E)) ∘L M.subtypeL =
      1 - (W : M →L[𝕜] M) := by
    apply ContinuousLinearMap.ext
    intro x
    change M.orthogonalProjectionOnto ((x : E) - U x) = x - W x
    rw [hUM, map_sub, M.orthogonalProjectionOnto_mem_subspace_eq_self,
      M.orthogonalProjectionOnto_mem_subspace_eq_self]
  have htail' : Mᗮ.orthogonalProjectionOnto ∘L (1 - (U : E →L[𝕜] E)) ∘L Mᗮ.subtypeL =
      Mᗮ.orthogonalProjectionOnto ∘L (1 - (R : E →L[𝕜] E)) ∘L Mᗮ.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change Mᗮ.orthogonalProjectionOnto ((x : E) - U x) =
      Mᗮ.orthogonalProjectionOnto ((x : E) - R x)
    rw [htail x x.property]
  rw [gauge_schatten_rpow_eq_add_of_isReducing p hp _ M hred, hblock, htail']

end ContinuousLinearMap
