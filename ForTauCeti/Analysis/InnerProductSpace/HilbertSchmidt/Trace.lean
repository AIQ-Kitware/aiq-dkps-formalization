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

/-- Real trace of a Hilbert–Schmidt product is the polarization of
three native energies. This makes basis independence a consequence
of the accepted energy invariance, with no double-series rearrangement. -/
theorem two_mul_re_tsum_inner_comp_eq_energy_deficit
    (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    2 * RCLike.re (∑' i, ⟪b i, S (T (b i))⟫_𝕜) =
      (S.hilbertSchmidtEnergy b).toReal + (T.hilbertSchmidtEnergy b).toReal -
        ((S.adjoint - T).hilbertSchmidtEnergy b).toReal := by
  have hSa : S.adjoint.hilbertSchmidtEnergy b ≠ ∞ := by
    rwa [S.hilbertSchmidtEnergy_adjoint b b]
  obtain ⟨f, hf, _⟩ := b.existsUnique_columnOperator_eq hSa
  obtain ⟨g, hg, _⟩ := b.existsUnique_columnOperator_eq hT
  have hdiff : b.columnOperator (f - g) = S.adjoint - T := by rw [map_sub, hf, hg]
  have hnorm := norm_sub_sq (𝕜 := 𝕜) f g
  rw [norm_columns_sq _ b (f - g) hdiff, norm_columns_sq _ b f hf,
    norm_columns_sq _ b g hg, S.hilbertSchmidtEnergy_adjoint b b] at hnorm
  have htrace : ⟪f, g⟫_𝕜 = ∑' i, ⟪b i, S (T (b i))⟫_𝕜 := by
    rw [lp.inner_eq_tsum]
    exact tsum_congr (fun i => (inner_comp_eq_inner_columns S T b f g hf hg i).symm)
  rw [htrace] at hnorm
  linarith

/-- The real diagonal trace of a Hilbert–Schmidt product is independent
of the Hilbert basis, with no restriction on either basis cardinality. -/
theorem re_tsum_inner_comp_eq_of_hilbertBasis
    {κ : Type*} (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    RCLike.re (∑' i, ⟪b i, S (T (b i))⟫_𝕜) =
      RCLike.re (∑' j, ⟪c j, S (T (c j))⟫_𝕜) := by
  have hSc : S.hilbertSchmidtEnergy c ≠ ∞ := by rwa [← S.hilbertSchmidtEnergy_indep b c]
  have hTc : T.hilbertSchmidtEnergy c ≠ ∞ := by rwa [← T.hilbertSchmidtEnergy_indep b c]
  have hb := two_mul_re_tsum_inner_comp_eq_energy_deficit S T b hS hT
  have hc := two_mul_re_tsum_inner_comp_eq_energy_deficit S T c hSc hTc
  rw [← S.hilbertSchmidtEnergy_indep b c, ← T.hilbertSchmidtEnergy_indep b c,
    ← (S.adjoint - T).hilbertSchmidtEnergy_indep b c] at hc
  linarith

/-- The full scalar diagonal trace of a Hilbert–Schmidt product is
basis independent over either field. Real-part invariance after every
scalar multiplication determines the scalar trace uniquely. -/
theorem tsum_inner_comp_eq_of_hilbertBasis
    {κ : Type*} (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    (∑' i, ⟪b i, S (T (b i))⟫_𝕜) = ∑' j, ⟪c j, S (T (c j))⟫_𝕜 := by
  let z := ∑' i, ⟪b i, S (T (b i))⟫_𝕜
  let w := ∑' j, ⟪c j, S (T (c j))⟫_𝕜
  have hscalar (a : 𝕜) : RCLike.re (a * z) = RCLike.re (a * w) := by
    have haS : (a • S).hilbertSchmidtEnergy b ≠ ∞ := by
      rw [hilbertSchmidtEnergy_smul]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by finiteness)) hS
    have h := re_tsum_inner_comp_eq_of_hilbertBasis (a • S) T b c haS hT
    simpa only [smul_apply, inner_smul_right, tsum_mul_left] using h
  have hzero : RCLike.re (star (z - w) * (z - w)) = 0 := by
    rw [mul_sub, map_sub, hscalar]
    exact sub_self _
  have hnorm : ‖z - w‖ ^ 2 = 0 := by
    simpa only [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re] using hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))


/-- The real diagonal trace is cyclic on Hilbert–Schmidt products.
Adjoint invariance of the energy gives the equality without a
conditionally convergent change of summation order. -/
theorem re_tsum_inner_comp_comm
    (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    RCLike.re (∑' i, ⟪b i, S (T (b i))⟫_𝕜) =
      RCLike.re (∑' i, ⟪b i, T (S (b i))⟫_𝕜) := by
  have hdiff : (S.adjoint - T).hilbertSchmidtEnergy b =
      (T.adjoint - S).hilbertSchmidtEnergy b := by
    rw [← (S.adjoint - T).hilbertSchmidtEnergy_adjoint b b, map_sub, adjoint_adjoint,
      ← neg_sub T.adjoint S]
    simp only [hilbertSchmidtEnergy_def, neg_apply, enorm_neg]
  have hST := two_mul_re_tsum_inner_comp_eq_energy_deficit S T b hS hT
  have hTS := two_mul_re_tsum_inner_comp_eq_energy_deficit T S b hT hS
  rw [hdiff] at hST
  linarith

/-- The scalar diagonal trace is cyclic on Hilbert–Schmidt products,
over either field and without any separability assumption. -/
theorem tsum_inner_comp_comm
    (S T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    (∑' i, ⟪b i, S (T (b i))⟫_𝕜) = ∑' i, ⟪b i, T (S (b i))⟫_𝕜 := by
  let z := ∑' i, ⟪b i, S (T (b i))⟫_𝕜
  let w := ∑' i, ⟪b i, T (S (b i))⟫_𝕜
  have hscalar (a : 𝕜) : RCLike.re (a * z) = RCLike.re (a * w) := by
    have haS : (a • S).hilbertSchmidtEnergy b ≠ ∞ := by
      rw [hilbertSchmidtEnergy_smul]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by finiteness)) hS
    have h := re_tsum_inner_comp_comm (a • S) T b haS hT
    simpa only [smul_apply, map_smul, inner_smul_right, tsum_mul_left] using h
  have hzero : RCLike.re (star (z - w) * (z - w)) = 0 := by
    rw [mul_sub, map_sub, hscalar]
    exact sub_self _
  have hnorm : ‖z - w‖ ^ 2 = 0 := by
    simpa only [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
      RCLike.ofReal_re] using hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))


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
