/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Trace
public import ForTauCeti.Analysis.OperatorIdeal.Nuclear.CompactGram
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Family.Modulus
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry

/-!
# Trace support and projected unitary defects

A square-root polar factorization identifies saturation of the real trace bound
with positivity. The trace is TauCeti's trace on the trace class. The projected
unitary defect formula uses the native trace of the Gram operator and keeps
arbitrary Hilbert dimension and arbitrary orthogonal projections.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped InnerProductSpace ENNReal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

open RCLike TauCeti.OperatorIdealFamily

attribute [local instance] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower

/-- The nuclear gauge of the Gram operator is exactly the native
Hilbert–Schmidt energy in every Hilbert basis, including infinite values. -/
theorem nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy
    (T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) :
    (T.adjoint ∘L T).nuclearENorm = T.hilbertSchmidtEnergy b := by
  by_cases hc : IsCompactOperator (T.adjoint ∘L T)
  · exact nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy_of_compact T b hc
  have hn : (T.adjoint ∘L T).nuclearENorm = ∞ := by
    by_contra h
    exact hc (isCompactOperator_of_nuclearENorm_ne_top h)
  have he : T.hilbertSchmidtEnergy b = ∞ := by
    by_contra h
    exact hc ((isCompactOperator_of_hilbertSchmidtEnergy_ne_top h).clm_comp T.adjoint)
  rw [hn, he]

/-- Square-root polar factorization has exact square-root nuclear
energy and a contractive second factor. The identities remain valid at
infinite energy; finite nuclear gauge makes both factors Hilbert–Schmidt. -/
theorem exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy
    (A : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) :
    ∃ H Y : E →L[𝕜] E, H.IsPositive ∧ H * H = A.modulus ∧ Y * H = A ∧
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
    rw [← nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy H b, hgram]
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

/-- Every trace-class operator has an absolutely summable diagonal in every
Hilbert basis, including on a nonseparable ambient space. -/
theorem summable_norm_inner_of_nuclearENorm_ne_top
    (A : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) (hA : A.nuclearENorm ≠ ∞) :
    Summable (fun i => ‖⟪b i, A (b i)⟫_𝕜‖) := by
  obtain ⟨H, Y, _, _, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  have h := summable_norm_inner_adjoint_apply_apply
    ((mem_finiteSubmodule_hilbertSchmidt_iff Y b).2 (ne_top_of_le_ne_top hHfinite hY))
    ((mem_finiteSubmodule_hilbertSchmidt_iff H b).2 hHfinite) b
  simpa only [adjoint_inner_left, ← comp_apply, ← mul_def, hfactor] using h

/-- The real trace of a trace-class operator saturates the trace-norm bound
exactly when the operator is positive. -/
theorem re_trace_eq_nuclearENorm_iff_isPositive
    (A : E →L[𝕜] E) (hA : A.nuclearENorm ≠ ∞) :
    RCLike.re A.trace = A.nuclearENorm.toReal ↔ A.IsPositive := by
  obtain ⟨_, b, _⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨H, Y, hH, hHsq, hfactor, henergy, hY⟩ :=
    exists_polar_sqrt_factorization_with_hilbertSchmidtEnergy A b
  have hHfinite : H.hilbertSchmidtEnergy b ≠ ∞ := by rwa [henergy]
  constructor
  · intro htrace
    rw [trace_eq_tsum_inner_apply b
      ((mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top A).2 hA)] at htrace
    have heq : Y = H := eq_of_re_tsum_inner_comp_eq_hilbertSchmidtEnergy H Y b
      hH.isSelfAdjoint hHfinite hY (by
        change RCLike.re (∑' i, ⟪b i, (Y * H) (b i)⟫_𝕜) = (H.hilbertSchmidtEnergy b).toReal
        rwa [hfactor, henergy])
    have hAm : A = A.modulus := hfactor.symm.trans (by rw [heq]; exact hHsq)
    rw [hAm]
    exact A.isPositive_modulus
  · intro hpos
    have hgram : A = H.adjoint ∘L H := by
      change A = star H * H
      rw [hH.isSelfAdjoint.star_eq, hHsq, hpos.modulus_eq]
    rw [congrArg ContinuousLinearMap.trace hgram,
      trace_adjoint_comp_self ((mem_finiteSubmodule_hilbertSchmidt_iff H b).2 hHfinite),
      RCLike.ofReal_re, H.sq_hilbertSchmidtNorm b, henergy]

/-- **Unitary nuclear trace support equality in arbitrary dimension.**
After any actual unitary change of target coordinates, saturation of
the real diagonal trace bound is exactly positivity of the transformed
operator. All diagonal series are absolutely summable by trace-class
membership, in every Hilbert basis. -/
theorem re_tsum_inner_unitary_comp_eq_nuclearENorm_iff_isPositive
    (A : E →L[𝕜] E) (U : E ≃ₗᵢ[𝕜] E) (b : HilbertBasis ι 𝕜 E)
    (hA : A.nuclearENorm ≠ ∞) :
    RCLike.re (∑' i, ⟪b i, U (A (b i))⟫_𝕜) = A.nuclearENorm.toReal ↔
      ((U : E →L[𝕜] E) ∘L A).IsPositive := by
  have hcost : ((U : E →L[𝕜] E) ∘L A).nuclearENorm = A.nuclearENorm := by
    rw [nuclearENorm_def, nuclearENorm_def]
    apply tsum_congr
    intro n
    have h := singularValue_comp_linearIsometryEquiv A (LinearIsometryEquiv.refl 𝕜 E) U n
    have heq : U.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
        (LinearIsometryEquiv.refl 𝕜 E).toLinearIsometry.toContinuousLinearMap =
        (U : E →L[𝕜] E) ∘L A := by ext x; rfl
    rw [heq] at h
    exact congrArg (fun s : NNReal => (s : ℝ≥0∞)) h
  have hfinite : ((U : E →L[𝕜] E) ∘L A).nuclearENorm ≠ ∞ := by rwa [hcost]
  have h := re_trace_eq_nuclearENorm_iff_isPositive
    ((U : E →L[𝕜] E) ∘L A) hfinite
  rwa [trace_eq_tsum_inner_apply b
    ((mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top _).2 hfinite), hcost] at h

/-- Nuclear trace is invariant under actual unitary conjugation. -/
theorem trace_conjStarAlgEquiv
    (A : E →L[𝕜] E) (U : E ≃ₗᵢ[𝕜] E) (hA : A.nuclearENorm ≠ ∞) :
    (U.conjStarAlgEquiv A).trace = A.trace := by
  have hmem := (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top A).2 hA
  have hcyclic : ((U.symm : E →L[𝕜] E) * ((U : E →L[𝕜] E) * A)).trace =
      (((U : E →L[𝕜] E) * A) * (U.symm : E →L[𝕜] E)).trace :=
    trace_comp_comm (U.symm : E →L[𝕜] E)
      (mul_left_mem_finiteSubmodule (U : E →L[𝕜] E) hmem)
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  change ((U : E →L[𝕜] E) * (A * (U.symm : E →L[𝕜] E))).trace = _
  rw [← mul_assoc, ← hcyclic]
  have hinv : (U.symm : E →L[𝕜] E) * (U : E →L[𝕜] E) = 1 := by
    ext x
    exact U.symm_apply_apply x
  rw [← mul_assoc, hinv, one_mul]

/-- A trace-class operator negated by unitary conjugation has zero
nuclear trace, also in arbitrary infinite-dimensional ambient space. -/
theorem trace_eq_zero_of_conjStarAlgEquiv_eq_neg
    (A : E →L[𝕜] E) (U : E ≃ₗᵢ[𝕜] E) (hA : A.nuclearENorm ≠ ∞)
    (hodd : U.conjStarAlgEquiv A = -A) : A.trace = 0 := by
  have h := trace_conjStarAlgEquiv A U hA
  rw [hodd, trace_neg] at h
  exact CharZero.neg_eq_self_iff.mp h

/-- A positive trace-class operator has zero nuclear trace exactly
when it is zero. This is the faithful positivity endpoint needed for
vanishing diagonal-defect arguments. -/
theorem trace_eq_zero_iff_of_isPositive
    (A : E →L[𝕜] E) (hA : A.nuclearENorm ≠ ∞) (hpos : A.IsPositive) :
    A.trace = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    have h := (re_trace_eq_nuclearENorm_iff_isPositive A hA).mpr hpos
    rw [hzero, RCLike.zero_re] at h
    have hnorm : A.nuclearENorm = 0 := by
      exact ((ENNReal.toReal_eq_zero_iff A.nuclearENorm).mp h.symm).resolve_right hA
    exact A.nuclearENorm_eq_zero.mp hnorm
  · rintro rfl
    exact trace_zero


/-- **Exact trace defect of a unitary on a projected sector.** If
G=(I-Z)Q is trace class, twice its real nuclear trace is its squared
Hilbert–Schmidt norm. This quantifies the nonnegative fixed-direction
slack without requiring Q to have finite rank or Z-I to be trace class. -/
theorem two_mul_re_trace_unitary_projection_defect
    (Z : E ≃ₗᵢ[𝕜] E) (Q : E →L[𝕜] E) (hQ : IsStarProjection Q)
    (hfinite : ((1 - (Z : E →L[𝕜] E)) * Q).nuclearENorm ≠ ∞) :
    2 * RCLike.re (((1 - (Z : E →L[𝕜] E)) * Q).trace) =
      (((1 - (Z : E →L[𝕜] E)) * Q).hilbertSchmidtNorm) ^ 2 := by
  let G := (1 - (Z : E →L[𝕜] E)) * Q
  have hunit : star (Z : E →L[𝕜] E) * (Z : E →L[𝕜] E) = 1 := by
    rw [show star (Z : E →L[𝕜] E) = (Z.symm : E →L[𝕜] E) from Z.adjoint_eq_symm]
    ext x
    exact Z.symm_apply_apply x
  have hmid : (1 - star (Z : E →L[𝕜] E)) * (1 - (Z : E →L[𝕜] E)) =
      (1 - (Z : E →L[𝕜] E)) + (1 - star (Z : E →L[𝕜] E)) := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hunit]
    simp only [one_mul]
    abel
  have hgram : G.adjoint * G = Q * G + G.adjoint * Q := by
    change star ((1 - (Z : E →L[𝕜] E)) * Q) * ((1 - (Z : E →L[𝕜] E)) * Q) = _
    calc
      _ = Q * ((1 - star (Z : E →L[𝕜] E)) * (1 - (Z : E →L[𝕜] E))) * Q := by
        rw [star_mul, hQ.isSelfAdjoint.star_eq, star_sub, star_one]
        simp only [mul_assoc]
      _ = Q * ((1 - (Z : E →L[𝕜] E)) + (1 - star (Z : E →L[𝕜] E))) * Q := by rw [hmid]
      _ = _ := by
        change _ = Q * ((1 - (Z : E →L[𝕜] E)) * Q) +
          star ((1 - (Z : E →L[𝕜] E)) * Q) * Q
        rw [star_mul, hQ.isSelfAdjoint.star_eq, star_sub, star_one]
        simp only [mul_add, add_mul, mul_assoc]
  have hGQ : G * Q = G := by dsimp only [G]; rw [mul_assoc, hQ.isIdempotentElem.eq]
  have hQGa : Q * G.adjoint = G.adjoint := by
    change Q * star G = star G
    have h := congrArg star hGQ
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using h
  have hG := (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top G).2 hfinite
  have hGa := (adjoint_mem_finiteSubmodule_iff G).2 hG
  have hTrQG : (Q * G).trace = G.trace := by
    rw [show (Q * G).trace = (G * Q).trace from trace_comp_comm Q hG, hGQ]
  have hTrGaQ : (G.adjoint * Q).trace = G.adjoint.trace := by
    rw [show (G.adjoint * Q).trace = (Q * G.adjoint).trace from (trace_comp_comm Q hGa).symm, hQGa]
  have htrace : RCLike.re (G.adjoint * G).trace = 2 * RCLike.re G.trace := by
    rw [hgram, trace_add (mul_left_mem_finiteSubmodule Q hG)
      (mul_right_mem_finiteSubmodule hGa Q), hTrQG, hTrGaQ, trace_adjoint_eq_conj_trace]
    simp [two_mul]
  obtain ⟨_, b, _⟩ := exists_hilbertBasis 𝕜 E
  have hHS : G.hilbertSchmidtEnergy b ≠ ∞ := by
    rw [← nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy G b]
    exact (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top _).1
      (mul_left_mem_finiteSubmodule G.adjoint hG)
  rw [← htrace]
  change RCLike.re (G.adjoint ∘L G).trace = _
  rw [trace_adjoint_comp_self ((mem_finiteSubmodule_hilbertSchmidt_iff G b).2 hHS),
    RCLike.ofReal_re]

/-- The real trace defect is nonnegative and vanishes exactly when
the unitary fixes the entire projected sector. No finite-rank hypothesis
on that sector or global trace-class displacement is assumed. -/
theorem re_trace_unitary_projection_defect_nonneg_and_eq_zero_iff
    (Z : E ≃ₗᵢ[𝕜] E) (Q : E →L[𝕜] E) (hQ : IsStarProjection Q)
    (hfinite : ((1 - (Z : E →L[𝕜] E)) * Q).nuclearENorm ≠ ∞) :
    0 ≤ RCLike.re (((1 - (Z : E →L[𝕜] E)) * Q).trace) ∧
      (RCLike.re (((1 - (Z : E →L[𝕜] E)) * Q).trace) = 0 ↔
        (1 - (Z : E →L[𝕜] E)) * Q = 0) := by
  let G := (1 - (Z : E →L[𝕜] E)) * Q
  have hid := two_mul_re_trace_unitary_projection_defect Z Q hQ hfinite
  change 2 * RCLike.re G.trace = G.hilbertSchmidtNorm ^ 2 at hid
  refine ⟨by nlinarith [sq_nonneg G.hilbertSchmidtNorm], ?_⟩
  constructor
  · intro hzero
    have hnorm : G.hilbertSchmidtNorm = 0 := by
      exact sq_eq_zero_iff.mp (by rw [← hid, hzero, mul_zero])
    have hG := (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top G).2 hfinite
    obtain ⟨_, b, _⟩ := exists_hilbertBasis 𝕜 E
    have hHS : G.hilbertSchmidtEnergy b ≠ ∞ := by
      rw [← nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy G b]
      exact (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top _).1
        (mul_left_mem_finiteSubmodule G.adjoint hG)
    exact norm_eq_zero.mp (le_antisymm (hnorm ▸ G.norm_le_hilbertSchmidtNorm b hHS) (norm_nonneg G))
  · intro hzero
    change G = 0 at hzero
    rw [show (1 - (Z : E →L[𝕜] E)) * Q = 0 from hzero, trace_zero, RCLike.zero_re]

end ContinuousLinearMap
