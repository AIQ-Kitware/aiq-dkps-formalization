/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ReducingUnitaryRestriction

public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierBlockSum
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
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

/-- The operator norm on an actual reducing decomposition is exactly
the larger compressed norm. No compactness or finite dimension is needed. -/
theorem norm_eq_max_compressions_of_isReducing
    (A : E →L[𝕜] E) (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (hM : M.IsReducing A.toLinearMap) :
    ‖A‖ = max ‖M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL‖
      ‖Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL‖ := by
  have h := A.singularValue_eq_orthogonal_block_of_isReducing M hM 0
  rw [singularValue_zero, singularValue_zero] at h
  have hn := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  exact hn.trans (norm_withLpProdMap _ _)

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

/-- An actual unitary replacement on a reducing block has exactly the
new block's Schatten power plus its unchanged reference tail.
The identity includes infinite reference-tail costs. -/
theorem gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
    (p : ℝ) (hp : 1 ≤ p) (M : Submodule 𝕜 E)
    [M.HasOrthogonalProjection] [CompleteSpace M]
    (U R : E ≃ₗᵢ[𝕜] E) (W : M ≃ₗᵢ[𝕜] M)
    (hUM : ∀ x : M, U x = (W x : E)) (htail : ∀ x ∈ Mᗮ, U x = R x) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ^ p =
      (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M)) ^ p +
        (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge
          (Mᗮ.orthogonalProjectionOnto ∘L (1 - (R : E →L[𝕜] E)) ∘L Mᗮ.subtypeL) ^ p := by
  have hredU := U.isReducing_of_restriction M W (fun x => (hUM x).symm)
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

/-- A unitary with a finite-dimensional actual restriction and an
ideal-small reference tail has finite Schatten displacement. -/
theorem gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail
    (p : ℝ) (hp : 1 ≤ p) (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M]
    (U : E ≃ₗᵢ[𝕜] E) (R : E →L[𝕜] E) (V : M ≃ₗᵢ[𝕜] M)
    (hV : ∀ x : M, (V x : E) = U x)
    (htail : ∀ x ∈ Mᗮ, U x = R x)
    (hR : (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - R) ≠ ∞) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≠ ∞ := by
  let Φ := TauCeti.OperatorIdealFamily.schatten 𝕜 p hp
  have hdisp : Mᗮ.orthogonalProjectionOnto ∘L (1 - (U : E →L[𝕜] E)) ∘L Mᗮ.subtypeL =
      Mᗮ.orthogonalProjectionOnto ∘L (1 - R) ∘L Mᗮ.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change Mᗮ.orthogonalProjectionOnto ((x : E) - U x) =
      Mᗮ.orthogonalProjectionOnto ((x : E) - R x)
    rw [htail x x.property]
  have htailfinite : Φ.gauge
      (Mᗮ.orthogonalProjectionOnto ∘L (1 - R) ∘L Mᗮ.subtypeL) ≠ ∞ := by
    apply ne_top_of_le_ne_top hR
    exact (Φ.gauge_comp_left_le_self Mᗮ.orthogonalProjectionOnto_norm_le _).trans
      (Φ.gauge_comp_right_le_self _ Mᗮ.norm_subtypeL_le)
  have hsplit := ContinuousLinearMap.gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
    p hp M U U V (fun x => (hV x).symm) (fun _ _ => rfl)
  have hheadfinite := TauCeti.OperatorIdealFamily.gauge_schatten_ne_top_of_rank_le p hp
    (1 - (V : M →L[𝕜] M)) (Module.finrank 𝕜 M)
      (by simpa only [Module.finrank_eq_rank] using
        LinearMap.rank_le_domain (1 - (V : M →L[𝕜] M)).toLinearMap)
  have hpow : Φ.gauge (1 - (U : E →L[𝕜] E)) ^ p ≠ ∞ := by
    rw [hsplit, hdisp]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.rpow_ne_top_of_nonneg (by linarith) hheadfinite,
        ENNReal.rpow_ne_top_of_nonneg (by linarith) htailfinite⟩
  exact fun h => hpow ((ENNReal.rpow_eq_top_iff_of_pos (zero_lt_one.trans_le hp)).mpr h)


end ContinuousLinearMap
