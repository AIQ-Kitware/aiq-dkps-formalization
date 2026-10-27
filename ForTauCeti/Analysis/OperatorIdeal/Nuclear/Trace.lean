/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Trace
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenGram
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
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

/-- The diagonal trace in a chosen Hilbert basis. For trace-class
operators, `nuclearTrace_eq_tsum_inner_complex` identifies this with the
absolutely convergent diagonal series in every Hilbert basis. All
linearity and cyclicity assertions below retain ideal hypotheses. -/
@[expose]
def nuclearTrace {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : F →L[𝕜] F) : 𝕜 :=
  let s := Classical.choose (exists_hilbertBasis 𝕜 F)
  let b : HilbertBasis s 𝕜 F := Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 F))
  ∑' i, inner 𝕜 (b i) (A (b i))

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
  let Y := A.polarFactor * H
  have hH : H.IsPositive := nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hHsq : H * H = A.modulus := CFC.sqrt_mul_sqrt_self _ A.modulus_nonneg
  have hgram : H.adjoint ∘L H = A.modulus := by
    change star H * H = A.modulus
    rw [hH.isSelfAdjoint.star_eq, hHsq]
  have henergy : H.hilbertSchmidtEnergy b = A.nuclearENorm := by
    rw [← nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_complex H b, hgram]
    simp only [nuclearENorm_def, singularValue_modulus]
  have hfactor : Y * H = A := by
    change (A.polarFactor * H) * H = A
    rw [mul_assoc, hHsq]
    exact A.polarFactor_comp_modulus
  have hnorm : ‖A.polarFactor‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [A.polarFactor_eq_factorThru]
    exact norm_factorThru_le zero_le_one (fun x => by rw [one_mul, A.norm_modulus_apply])
  refine ⟨H, Y, hH, hHsq, hfactor, henergy, ?_⟩
  calc
    Y.hilbertSchmidtEnergy b ≤ ‖A.polarFactor‖ₑ ^ 2 * H.hilbertSchmidtEnergy b :=
      hilbertSchmidtEnergy_comp_le_left A.polarFactor H b
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


/-- The absolutely convergent diagonal trace of a trace-class operator
is independent of the Hilbert basis, including arbitrary kernel cardinality. -/
theorem tsum_inner_eq_of_hilbertBasis_of_nuclearENorm_ne_top_complex
    {κ : Type*} (A : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (hA : A.nuclearENorm ≠ ∞) :
    (∑' i, ⟪b i, A (b i)⟫_ℂ) = ∑' j, ⟪c j, A (c j)⟫_ℂ := by
  obtain ⟨H, Y, _, _, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy_complex A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  have hYfinite := ne_top_of_le_ne_top hHfinite hY
  have h := tsum_inner_comp_eq_of_hilbertBasis Y H b c hYfinite hHfinite
  simpa only [← comp_apply, ← mul_def, hfactor] using h

/-- The nuclear trace equals the absolutely convergent diagonal sum in
every Hilbert basis. In particular the chosen basis is not part of its value. -/
theorem nuclearTrace_eq_tsum_inner_complex
    (A : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) (hA : A.nuclearENorm ≠ ∞) :
    A.nuclearTrace = ∑' i, ⟪b i, A (b i)⟫_ℂ := by
  unfold nuclearTrace
  exact tsum_inner_eq_of_hilbertBasis_of_nuclearENorm_ne_top_complex A _ b hA

/-- The canonical nuclear trace obeys the exact native nuclear bound. -/
theorem norm_nuclearTrace_le_nuclearENorm_complex
    (A : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    ‖A.nuclearTrace‖ ≤ A.nuclearENorm.toReal := by
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  rw [nuclearTrace_eq_tsum_inner_complex A b hA]
  exact norm_tsum_inner_le_nuclearENorm_complex A b hA

/-- Positivity is precisely saturation of the real canonical nuclear
trace bound on any complete complex Hilbert space. -/
theorem re_nuclearTrace_eq_nuclearENorm_iff_isPositive_complex
    (A : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    A.nuclearTrace.re = A.nuclearENorm.toReal ↔ A.IsPositive := by
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  rw [nuclearTrace_eq_tsum_inner_complex A b hA]
  exact re_tsum_inner_eq_nuclearENorm_iff_isPositive_complex A b hA

/-- Additivity of the canonical nuclear trace retains finite nuclear
gauge for both summands; no operator-norm continuous trace is asserted. -/
theorem nuclearTrace_add_complex
    (A B : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) (hB : B.nuclearENorm ≠ ∞) :
    (A + B).nuclearTrace = A.nuclearTrace + B.nuclearTrace := by
  have hAB : (A + B).nuclearENorm ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA, hB⟩) (A.nuclearENorm_add_le B)
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  rw [nuclearTrace_eq_tsum_inner_complex (A + B) b hAB,
    nuclearTrace_eq_tsum_inner_complex A b hA, nuclearTrace_eq_tsum_inner_complex B b hB]
  simp only [add_apply, inner_add_right]
  exact ((summable_norm_inner_of_nuclearENorm_ne_top_complex A b hA).of_norm).tsum_add
    (summable_norm_inner_of_nuclearENorm_ne_top_complex B b hB).of_norm

/-- Scalar homogeneity of the canonical nuclear trace on its natural domain. -/
theorem nuclearTrace_smul_complex
    (a : ℂ) (A : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    (a • A).nuclearTrace = a * A.nuclearTrace := by
  have haA : (a • A).nuclearENorm ≠ ∞ := by
    rw [nuclearENorm_smul]
    exact ENNReal.mul_ne_top (by finiteness) hA
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  rw [nuclearTrace_eq_tsum_inner_complex (a • A) b haA, nuclearTrace_eq_tsum_inner_complex A b hA]
  simp only [smul_apply, inner_smul_right, tsum_mul_left]

/-- Taking adjoints conjugates the canonical nuclear trace. -/
theorem nuclearTrace_adjoint_complex
    (A : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    A.adjoint.nuclearTrace = star A.nuclearTrace := by
  have haA : A.adjoint.nuclearENorm ≠ ∞ := by rwa [nuclearENorm_adjoint]
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  rw [nuclearTrace_eq_tsum_inner_complex A.adjoint b haA, nuclearTrace_eq_tsum_inner_complex A b hA,
    tsum_star]
  apply tsum_congr
  intro i
  rw [A.adjoint_inner_right]
  exact (inner_conj_symm (A (b i)) (b i)).symm


omit [CompleteSpace E] in
private theorem nuclearENorm_mul_ne_top_left_complex
    (A B : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) : (A * B).nuclearENorm ≠ ∞ := by
  have h := nuclearENorm_comp_comp_le (ContinuousLinearMap.id ℂ E) A B
  change (A ∘L B).nuclearENorm ≤ ‖ContinuousLinearMap.id ℂ E‖ₑ * A.nuclearENorm * ‖B‖ₑ at h
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hA) (by finiteness)) h

omit [CompleteSpace E] in
private theorem nuclearENorm_mul_ne_top_right_complex
    (A B : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) : (B * A).nuclearENorm ≠ ∞ := by
  have h := nuclearENorm_comp_comp_le B A (ContinuousLinearMap.id ℂ E)
  rw [comp_id] at h
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hA) (by finiteness)) h

/-- **Cyclicity of the nuclear trace.** One factor is trace class and
the other is an arbitrary bounded operator. Square-root factorization
reduces the identity to cyclicity of two Hilbert–Schmidt products. -/
theorem nuclearTrace_mul_comm_complex
    (A B : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    (A * B).nuclearTrace = (B * A).nuclearTrace := by
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  obtain ⟨H, Y, _, _, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy_complex A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  have hYfinite := ne_top_of_le_ne_top hHfinite hY
  have hHB : (H * B).hilbertSchmidtEnergy b ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hHfinite (ENNReal.pow_ne_top (by finiteness)))
      (hilbertSchmidtEnergy_comp_le_right H B b b)
  have hBY : (B * Y).hilbertSchmidtEnergy b ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by finiteness)) hYfinite)
      (hilbertSchmidtEnergy_comp_le_left B Y b)
  have hAB := nuclearENorm_mul_ne_top_left_complex A B hA
  have hBA := nuclearENorm_mul_ne_top_right_complex A B hA
  calc
    (A * B).nuclearTrace = ∑' i, ⟪b i, Y ((H * B) (b i))⟫_ℂ := by
      rw [nuclearTrace_eq_tsum_inner_complex _ b hAB, ← hfactor]
      rfl
    _ = ∑' i, ⟪b i, (H * B) (Y (b i))⟫_ℂ :=
      tsum_inner_comp_comm Y (H * B) b hYfinite hHB
    _ = ∑' i, ⟪b i, H ((B * Y) (b i))⟫_ℂ := rfl
    _ = ∑' i, ⟪b i, (B * Y) (H (b i))⟫_ℂ :=
      tsum_inner_comp_comm H (B * Y) b hHfinite hBY
    _ = (B * A).nuclearTrace := by
      rw [nuclearTrace_eq_tsum_inner_complex _ b hBA, ← hfactor]
      rfl

/-- Nuclear trace is invariant under actual unitary conjugation. -/
theorem nuclearTrace_conjStarAlgEquiv_complex
    (A : E →L[ℂ] E) (U : E ≃ₗᵢ[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    (U.conjStarAlgEquiv A).nuclearTrace = A.nuclearTrace := by
  have hUA := nuclearENorm_mul_ne_top_right_complex A (U : E →L[ℂ] E) hA
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  change ((U : E →L[ℂ] E) * (A * (U.symm : E →L[ℂ] E))).nuclearTrace = _
  rw [← mul_assoc, nuclearTrace_mul_comm_complex _ _ hUA]
  have hinv : (U.symm : E →L[ℂ] E) * (U : E →L[ℂ] E) = 1 := by
    ext x
    exact U.symm_apply_apply x
  rw [← mul_assoc, hinv, one_mul]

/-- A trace-class operator negated by unitary conjugation has zero
nuclear trace, also in arbitrary infinite-dimensional ambient space. -/
theorem nuclearTrace_eq_zero_of_conjStarAlgEquiv_eq_neg_complex
    (A : E →L[ℂ] E) (U : E ≃ₗᵢ[ℂ] E) (hA : A.nuclearENorm ≠ ∞)
    (hodd : U.conjStarAlgEquiv A = -A) : A.nuclearTrace = 0 := by
  have h := nuclearTrace_conjStarAlgEquiv_complex A U hA
  rw [hodd, show -A = (-1 : ℂ) • A from (neg_one_smul ℂ A).symm,
    nuclearTrace_smul_complex _ A hA, neg_one_mul] at h
  exact CharZero.neg_eq_self_iff.mp h

/-- A positive trace-class operator has zero nuclear trace exactly
when it is zero. This is the faithful positivity endpoint needed for
vanishing diagonal-defect arguments. -/
theorem nuclearTrace_eq_zero_iff_of_isPositive_complex
    (A : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) (hpos : A.IsPositive) :
    A.nuclearTrace = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    have h := (re_nuclearTrace_eq_nuclearENorm_iff_isPositive_complex A hA).mpr hpos
    rw [hzero, Complex.zero_re] at h
    have hnorm : A.nuclearENorm = 0 := by
      exact ((ENNReal.toReal_eq_zero_iff A.nuclearENorm).mp h.symm).resolve_right hA
    exact A.nuclearENorm_eq_zero.mp hnorm
  · rintro rfl
    unfold nuclearTrace
    simp


/-- **Exact trace defect of a unitary on a projected sector.** If
G=(I-Z)Q is trace class, twice its real nuclear trace is its squared
Hilbert–Schmidt norm. This quantifies the nonnegative fixed-direction
slack without requiring Q to have finite rank or Z-I to be trace class. -/
theorem two_mul_re_nuclearTrace_unitary_projection_defect_complex
    (Z : E ≃ₗᵢ[ℂ] E) (Q : E →L[ℂ] E) (hQ : IsStarProjection Q)
    (hfinite : ((1 - (Z : E →L[ℂ] E)) * Q).nuclearENorm ≠ ∞) :
    2 * (((1 - (Z : E →L[ℂ] E)) * Q).nuclearTrace).re =
      (((1 - (Z : E →L[ℂ] E)) * Q).hilbertSchmidtNorm) ^ 2 := by
  let G := (1 - (Z : E →L[ℂ] E)) * Q
  have hunit : star (Z : E →L[ℂ] E) * (Z : E →L[ℂ] E) = 1 := by
    rw [show star (Z : E →L[ℂ] E) = (Z.symm : E →L[ℂ] E) from Z.adjoint_eq_symm]
    ext x
    exact Z.symm_apply_apply x
  have hmid : (1 - star (Z : E →L[ℂ] E)) * (1 - (Z : E →L[ℂ] E)) =
      (1 - (Z : E →L[ℂ] E)) + (1 - star (Z : E →L[ℂ] E)) := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hunit]
    simp only [one_mul]
    abel
  have hgram : G.adjoint * G = Q * G + G.adjoint * Q := by
    change star ((1 - (Z : E →L[ℂ] E)) * Q) * ((1 - (Z : E →L[ℂ] E)) * Q) = _
    calc
      _ = Q * ((1 - star (Z : E →L[ℂ] E)) * (1 - (Z : E →L[ℂ] E))) * Q := by
        rw [star_mul, hQ.isSelfAdjoint.star_eq, star_sub, star_one]
        simp only [mul_assoc]
      _ = Q * ((1 - (Z : E →L[ℂ] E)) + (1 - star (Z : E →L[ℂ] E))) * Q := by rw [hmid]
      _ = _ := by
        change _ = Q * ((1 - (Z : E →L[ℂ] E)) * Q) +
          star ((1 - (Z : E →L[ℂ] E)) * Q) * Q
        rw [star_mul, hQ.isSelfAdjoint.star_eq, star_sub, star_one]
        simp only [mul_add, add_mul, mul_assoc]
  have hGQ : G * Q = G := by dsimp only [G]; rw [mul_assoc, hQ.isIdempotentElem.eq]
  have hQGa : Q * G.adjoint = G.adjoint := by
    change Q * star G = star G
    have h := congrArg star hGQ
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using h
  have hGafinite : G.adjoint.nuclearENorm ≠ ∞ := by rwa [nuclearENorm_adjoint]
  have hQGfinite := nuclearENorm_mul_ne_top_right_complex G Q hfinite
  have hGaQfinite := nuclearENorm_mul_ne_top_left_complex G.adjoint Q hGafinite
  have hGramfinite := nuclearENorm_mul_ne_top_right_complex G G.adjoint hfinite
  have hTrQG : (Q * G).nuclearTrace = G.nuclearTrace := by
    rw [← nuclearTrace_mul_comm_complex G Q hfinite, hGQ]
  have hTrGaQ : (G.adjoint * Q).nuclearTrace = G.adjoint.nuclearTrace := by
    rw [nuclearTrace_mul_comm_complex G.adjoint Q hGafinite, hQGa]
  have htrace : (G.adjoint * G).nuclearTrace.re = 2 * G.nuclearTrace.re := by
    rw [hgram, nuclearTrace_add_complex _ _ hQGfinite hGaQfinite,
      hTrQG, hTrGaQ, nuclearTrace_adjoint_complex G hfinite]
    simp [two_mul]
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
  calc
    2 * G.nuclearTrace.re = (G.adjoint * G).nuclearTrace.re := htrace.symm
    _ = (G.adjoint * G).nuclearENorm.toReal :=
      (re_nuclearTrace_eq_nuclearENorm_iff_isPositive_complex _ hGramfinite).mpr
        (isPositive_adjoint_comp_self G)
    _ = G.hilbertSchmidtNorm ^ 2 := by
      change (G.adjoint ∘L G).nuclearENorm.toReal = _
      rw [nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_complex G b,
        G.sq_hilbertSchmidtNorm b]

/-- The real trace defect is nonnegative and vanishes exactly when
the unitary fixes the entire projected sector. No finite-rank hypothesis
on that sector or global trace-class displacement is assumed. -/
theorem re_nuclearTrace_unitary_projection_defect_nonneg_and_eq_zero_iff_complex
    (Z : E ≃ₗᵢ[ℂ] E) (Q : E →L[ℂ] E) (hQ : IsStarProjection Q)
    (hfinite : ((1 - (Z : E →L[ℂ] E)) * Q).nuclearENorm ≠ ∞) :
    0 ≤ (((1 - (Z : E →L[ℂ] E)) * Q).nuclearTrace).re ∧
      ((((1 - (Z : E →L[ℂ] E)) * Q).nuclearTrace).re = 0 ↔
        (1 - (Z : E →L[ℂ] E)) * Q = 0) := by
  let G := (1 - (Z : E →L[ℂ] E)) * Q
  have hid := two_mul_re_nuclearTrace_unitary_projection_defect_complex Z Q hQ hfinite
  change 2 * G.nuclearTrace.re = G.hilbertSchmidtNorm ^ 2 at hid
  refine ⟨by nlinarith [sq_nonneg G.hilbertSchmidtNorm], ?_⟩
  constructor
  · intro hzero
    have hnorm : G.hilbertSchmidtNorm = 0 := by
      exact sq_eq_zero_iff.mp (by rw [← hid, hzero, mul_zero])
    have hGramfinite := nuclearENorm_mul_ne_top_right_complex G G.adjoint hfinite
    obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ E
    have hHS : G.hilbertSchmidtEnergy b ≠ ∞ := by
      rwa [← nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_complex G b]
    exact norm_eq_zero.mp (le_antisymm (hnorm ▸ G.norm_le_hilbertSchmidtNorm b hHS) (norm_nonneg G))
  · intro hzero
    change G = 0 at hzero
    have htrace : G.nuclearTrace = 0 := by rw [hzero]; unfold nuclearTrace; simp
    exact congrArg Complex.re htrace

end ContinuousLinearMap
