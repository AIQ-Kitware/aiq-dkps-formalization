/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Columns

/-!
# Trace support of Hilbert–Schmidt products

The diagonal of a product of two Hilbert–Schmidt operators is absolutely
summable in every Hilbert basis. Its sum is the inner product of their
actual square-summable columns, with the first factor adjointed. This
gives the trace support bound and a rigidity theorem when a self-adjoint
factor saturates its energy. Infinite-dimensional kernels and arbitrary
Hilbert-basis cardinalities are included.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped InnerProductSpace ENNReal lp

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

private theorem inner_comp_eq_inner_columns
    (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (f g : ℓ²(ι, E)) (hf : b.columnOperator f = S.adjoint) (hg : b.columnOperator g = T)
    (i : ι) : ⟪b i, S (T (b i))⟫_𝕜 = ⟪f i, g i⟫_𝕜 := by
  rw [← S.adjoint_inner_left, ← hf, ← hg, b.columnOperator_apply_self, b.columnOperator_apply_self]

private theorem norm_columns_sq
    (T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (f : ℓ²(ι, E)) (hf : b.columnOperator f = T) :
    ‖f‖ ^ 2 = (T.hilbertSchmidtEnergy b).toReal := by
  rw [← hf, b.hilbertSchmidtEnergy_columnOperator, ENNReal.toReal_pow, toReal_enorm]

/-- The diagonal trace of a product of Hilbert–Schmidt operators is
absolutely summable, without a separability assumption. -/
theorem summable_norm_inner_comp_of_hilbertSchmidtEnergy_ne_top
    (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    Summable (fun i => ‖⟪b i, S (T (b i))⟫_𝕜‖) := by
  have hSa : S.adjoint.hilbertSchmidtEnergy b ≠ ∞ := by
    rwa [S.hilbertSchmidtEnergy_adjoint b b]
  obtain ⟨f, hf, _⟩ := b.existsUnique_columnOperator_eq hSa
  obtain ⟨g, hg, _⟩ := b.existsUnique_columnOperator_eq hT
  simp_rw [inner_comp_eq_inner_columns S T b f g hf hg]
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_inner_le_norm (f i) (g i))
  exact lp.summable_mul (by norm_num [Real.holderConjugate_iff]) f g

/-- The norm of the diagonal trace sum of a Hilbert–Schmidt product
is bounded by the product of its Hilbert–Schmidt norms. -/
theorem norm_tsum_inner_comp_le_hilbertSchmidtNorm_mul
    (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    ‖∑' i, ⟪b i, S (T (b i))⟫_𝕜‖ ≤ S.hilbertSchmidtNorm * T.hilbertSchmidtNorm := by
  have hSa : S.adjoint.hilbertSchmidtEnergy b ≠ ∞ := by
    rwa [S.hilbertSchmidtEnergy_adjoint b b]
  obtain ⟨f, hf, _⟩ := b.existsUnique_columnOperator_eq hSa
  obtain ⟨g, hg, _⟩ := b.existsUnique_columnOperator_eq hT
  have hfnorm : ‖f‖ = S.hilbertSchmidtNorm := by
    rw [← S.hilbertSchmidtNorm_adjoint, ← hf, b.hilbertSchmidtNorm_columnOperator]
  have hgnorm : ‖g‖ = T.hilbertSchmidtNorm := by
    rw [← hg, b.hilbertSchmidtNorm_columnOperator]
  simp_rw [inner_comp_eq_inner_columns S T b f g hf hg]
  rw [← lp.inner_eq_tsum, ← hfnorm, ← hgnorm]
  exact norm_inner_le_norm f g

/-- **Trace-support rigidity from an energy bound.** Let H be
self-adjoint and Hilbert–Schmidt and let Y have no larger energy.
Saturation of the real trace of Y H at H's full energy forces Y=H.
The proof uses equality of the actual square-summable columns; it
requires no trace-class eigenbasis or finite-rank approximation. -/
theorem eq_of_re_tsum_inner_comp_eq_hilbertSchmidtEnergy
    (H Y : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) (hH : IsSelfAdjoint H)
    (hHfinite : H.hilbertSchmidtEnergy b ≠ ∞)
    (hY : Y.hilbertSchmidtEnergy b ≤ H.hilbertSchmidtEnergy b)
    (htrace : RCLike.re (∑' i, ⟪b i, Y (H (b i))⟫_𝕜) =
      (H.hilbertSchmidtEnergy b).toReal) : Y = H := by
  have hYfinite : Y.hilbertSchmidtEnergy b ≠ ∞ := ne_top_of_le_ne_top hHfinite hY
  have hYa : Y.adjoint.hilbertSchmidtEnergy b ≠ ∞ := by
    rwa [Y.hilbertSchmidtEnergy_adjoint b b]
  obtain ⟨f, hf, _⟩ := b.existsUnique_columnOperator_eq hYa
  obtain ⟨g, hg, _⟩ := b.existsUnique_columnOperator_eq hHfinite
  have hfnorm := norm_columns_sq Y.adjoint b f hf
  rw [Y.hilbertSchmidtEnergy_adjoint b b] at hfnorm
  have hgnorm := norm_columns_sq H b g hg
  have hnorm : ‖f‖ ≤ ‖g‖ := by
    apply (sq_le_sq₀ (norm_nonneg f) (norm_nonneg g)).mp
    rw [hfnorm, hgnorm]
    exact ENNReal.toReal_mono hHfinite hY
  have hinner : RCLike.re ⟪f, g⟫_𝕜 = ‖g‖ ^ 2 := by
    rw [hgnorm, lp.inner_eq_tsum]
    simpa only [inner_comp_eq_inner_columns Y H b f g hf hg] using htrace
  have heq : f = g := eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) hnorm hinner
  have hYaH : Y.adjoint = H := hf.symm.trans ((congrArg b.columnOperator heq).trans hg)
  have h := congrArg adjoint hYaH
  simpa only [adjoint_adjoint, hH.adjoint_eq] using h

end ContinuousLinearMap
