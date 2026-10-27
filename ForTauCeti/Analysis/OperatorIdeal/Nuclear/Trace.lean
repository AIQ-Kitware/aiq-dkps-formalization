/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Trace
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenGram
public import ForTauCeti.Analysis.OperatorIdeal.Family.Modulus
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Nuclear.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry

/-!
# Nuclear trace support in arbitrary complex Hilbert dimension

Square-root polar factorization turns the diagonal trace of a trace-class
operator into an inner product of square-summable columns. Absolute
summability and the nuclear trace bound follow from Hilbert–Schmidt
energy. Saturation forces the two factors to agree, so real trace equals
native nuclear gauge exactly for positive operators. No separability or
finite-rank hypothesis is used, and no infinite-dimensional algebraic
`LinearMap.trace` is substituted for the diagonal trace series.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped InnerProductSpace ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The nuclear gauge of the Gram operator is exactly the native
Hilbert–Schmidt energy in every Hilbert basis, including infinite values. -/
theorem nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_complex
    (T : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) :
    (T.adjoint ∘L T).nuclearENorm = T.hilbertSchmidtEnergy b := by
  have h := TauCeti.OperatorIdealFamily.gauge_schatten_gram_rpow 2 (by norm_num) T
  norm_num only [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one] at h
  have hleft (A : E →L[ℂ] E) :
      (TauCeti.OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge A = A.nuclearENorm := by
    simp only [TauCeti.OperatorIdealFamily.gauge_schatten, one_div_one, ENNReal.rpow_one,
      nuclearENorm_def]
  rw [hleft, TauCeti.OperatorIdealFamily.gauge_schatten_rpow] at h
  simp only [ENNReal.rpow_two] at h
  exact h.trans (T.tsum_singularValue_sq_eq_hilbertSchmidtEnergy b)

/-- Square-root polar factorization has exact square-root nuclear
energy and a contractive second factor. The identities remain valid at
infinite energy; finite nuclear gauge makes both factors Hilbert–Schmidt. -/
theorem exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy_complex
    (A : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) :
    ∃ H Y : E →L[ℂ] E, H.IsPositive ∧ H * H = A.modulus ∧ Y * H = A ∧
      H.hilbertSchmidtEnergy b = A.nuclearENorm ∧
      Y.hilbertSchmidtEnergy b ≤ H.hilbertSchmidtEnergy b := by
  let H := CFC.sqrt A.modulus
  let Y := A.polarPartial * H
  have hH : H.IsPositive := nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hHsq : H * H = A.modulus := CFC.sqrt_mul_sqrt_self _ A.modulus_nonneg
  have hgram : H.adjoint ∘L H = A.modulus := by
    change star H * H = A.modulus
    rw [hH.isSelfAdjoint.star_eq, hHsq]
  have henergy : H.hilbertSchmidtEnergy b = A.nuclearENorm := by
    rw [← nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_complex H b, hgram]
    simp only [nuclearENorm_def, singularValue_modulus]
  have hfactor : Y * H = A := by
    change (A.polarPartial * H) * H = A
    rw [mul_assoc, hHsq]
    exact A.polarPartial_comp_modulus
  have hnorm : ‖A.polarPartial‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (TauCeti.SymmetricOperatorIdealFamily.norm_polarPartial_le_one_rectangular A)
  refine ⟨H, Y, hH, hHsq, hfactor, henergy, ?_⟩
  calc
    Y.hilbertSchmidtEnergy b ≤ ‖A.polarPartial‖ₑ ^ 2 * H.hilbertSchmidtEnergy b :=
      hilbertSchmidtEnergy_comp_le_left A.polarPartial H b
    _ ≤ 1 ^ 2 * H.hilbertSchmidtEnergy b := by gcongr
    _ = H.hilbertSchmidtEnergy b := by rw [one_pow, one_mul]

/-- Every trace-class operator has an absolutely summable diagonal in
an arbitrary Hilbert basis, also on a nonseparable ambient space. -/
theorem summable_norm_inner_of_nuclearENorm_ne_top_complex
    (A : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) (hA : A.nuclearENorm ≠ ∞) :
    Summable (fun i => ‖⟪b i, A (b i)⟫_ℂ‖) := by
  obtain ⟨H, Y, _, _, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy_complex A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  have hYfinite := ne_top_of_le_ne_top hHfinite hY
  have h := summable_norm_inner_comp_of_hilbertSchmidtEnergy_ne_top Y H b hYfinite hHfinite
  simpa only [← comp_apply, ← mul_def, hfactor] using h

/-- The absolute diagonal trace is bounded by the native nuclear gauge.
The series is absolutely convergent under the stated ideal hypothesis. -/
theorem norm_tsum_inner_le_nuclearENorm_complex
    (A : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) (hA : A.nuclearENorm ≠ ∞) :
    ‖∑' i, ⟪b i, A (b i)⟫_ℂ‖ ≤ A.nuclearENorm.toReal := by
  obtain ⟨H, Y, _, _, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy_complex A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  have hYfinite := ne_top_of_le_ne_top hHfinite hY
  have hnorm : Y.hilbertSchmidtNorm ≤ H.hilbertSchmidtNorm := by
    rw [Y.hilbertSchmidtNorm_eq_sqrt b, H.hilbertSchmidtNorm_eq_sqrt b]
    exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hHfinite hY)
  calc
    _ = ‖∑' i, ⟪b i, Y (H (b i))⟫_ℂ‖ := by
      simp only [← comp_apply, ← mul_def, hfactor]
    _ ≤ Y.hilbertSchmidtNorm * H.hilbertSchmidtNorm :=
      norm_tsum_inner_comp_le_hilbertSchmidtNorm_mul Y H b hYfinite hHfinite
    _ ≤ H.hilbertSchmidtNorm * H.hilbertSchmidtNorm :=
      mul_le_mul_of_nonneg_right hnorm H.hilbertSchmidtNorm_nonneg
    _ = _ := by rw [← pow_two, H.sq_hilbertSchmidtNorm b, henergy]

/-- **Infinite-dimensional nuclear trace equality.** A trace-class
operator saturates the real diagonal trace bound exactly when it is
positive. Every Hilbert basis works; no spectral or separability
hypothesis is imposed on the ambient space. -/
theorem re_tsum_inner_eq_nuclearENorm_iff_isPositive_complex
    (A : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) (hA : A.nuclearENorm ≠ ∞) :
    (∑' i, ⟪b i, A (b i)⟫_ℂ).re = A.nuclearENorm.toReal ↔ A.IsPositive := by
  obtain ⟨H, Y, hH, hHsq, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy_complex A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  constructor
  · intro htrace
    have heq : Y = H := eq_of_re_tsum_inner_comp_eq_hilbertSchmidtEnergy H Y b
      hH.isSelfAdjoint hHfinite hY (by
        change (∑' i, ⟪b i, (Y * H) (b i)⟫_ℂ).re = (H.hilbertSchmidtEnergy b).toReal
        rwa [hfactor, henergy])
    have hAm : A = A.modulus := hfactor.symm.trans (by rw [heq]; exact hHsq)
    rw [hAm]
    exact A.isPositive_modulus
  · intro hpos
    have hgram : A = H.adjoint ∘L H := by
      change A = star H * H
      rw [hH.isSelfAdjoint.star_eq, hHsq, hpos.modulus_eq]
    have hsum := (summable_norm_inner_of_nuclearENorm_ne_top_complex A b hA).of_norm
    rw [Complex.re_tsum hsum]
    have hdiag (i : ι) : (⟪b i, A (b i)⟫_ℂ).re = ‖H (b i)‖ ^ 2 := by
      rw [hgram, comp_apply, H.adjoint_inner_right]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    simp_rw [hdiag]
    rw [← henergy, hilbertSchmidtEnergy_def]
    have h := ENNReal.tsum_toReal_eq (f := fun i : ι => ‖H (b i)‖ₑ ^ 2)
      (fun _ => ENNReal.pow_ne_top (by finiteness))
    simpa only [ENNReal.toReal_pow, toReal_enorm] using h.symm


/-- **Unitary nuclear trace support equality in arbitrary dimension.**
After any actual unitary change of target coordinates, saturation of
the real diagonal trace bound is exactly positivity of the transformed
operator. All diagonal series are absolutely summable by trace-class
membership, in every Hilbert basis. -/
theorem re_tsum_inner_unitary_comp_eq_nuclearENorm_iff_isPositive_complex
    (A : E →L[ℂ] E) (U : E ≃ₗᵢ[ℂ] E) (b : HilbertBasis ι ℂ E)
    (hA : A.nuclearENorm ≠ ∞) :
    (∑' i, ⟪b i, U (A (b i))⟫_ℂ).re = A.nuclearENorm.toReal ↔
      ((U : E →L[ℂ] E) ∘L A).IsPositive := by
  have hcost : ((U : E →L[ℂ] E) ∘L A).nuclearENorm = A.nuclearENorm := by
    rw [nuclearENorm_def, nuclearENorm_def]
    apply tsum_congr
    intro n
    have h := singularValue_comp_linearIsometryEquiv A (LinearIsometryEquiv.refl ℂ E) U n
    have heq : U.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
        (LinearIsometryEquiv.refl ℂ E).toLinearIsometry.toContinuousLinearMap =
        (U : E →L[ℂ] E) ∘L A := by ext x; rfl
    rw [heq] at h
    exact congrArg (fun s : NNReal => (s : ℝ≥0∞)) h
  have hfinite : ((U : E →L[ℂ] E) ∘L A).nuclearENorm ≠ ∞ := by rwa [hcost]
  have h := re_tsum_inner_eq_nuclearENorm_iff_isPositive_complex
    ((U : E →L[ℂ] E) ∘L A) b hfinite
  rwa [hcost] at h

end ContinuousLinearMap
