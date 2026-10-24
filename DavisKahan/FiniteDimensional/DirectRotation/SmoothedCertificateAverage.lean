/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNuclearCertificate
public import ForTauCeti.Analysis.InnerProductSpace.BasisDiagonal
public import ForTauCeti.Analysis.InnerProductSpace.PositiveUnitaryAverage
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Positive unitary averages from diagonal equality certificates

The fixed subcritical directions and the self-adjoint dual displacement
produce a twisted average with a clipped positive diagonal. Unitarity
then recovers commutation with the original diagonal before clipping.
These lemmas do not assume a plane-preserving competitor.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
private theorem star_unitary_fixes_of_fixes (Z : unitary (E →L[ℂ] E))
    (x : E) (hx : (Z : E →L[ℂ] E) x = x) : star (Z : E →L[ℂ] E) x = x := by
  apply (Unitary.linearIsometryEquiv Z).injective
  change (Z : E →L[ℂ] E) (star (Z : E →L[ℂ] E) x) = (Z : E →L[ℂ] E) x
  rw [hx]
  exact congrArg (fun T : E →L[ℂ] E => T x) (Unitary.mul_star_self_of_mem Z.property)

omit [FiniteDimensional ℂ E] in
/-- A diagonal equality certificate yields a twisted average equation.
Directions on which the supporting phase is not a quarter turn are
allowed, provided that the competitor already fixes them. -/
theorem twisted_average_of_diagonal_certificate_complex
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (b : ℝ) (hb : b ≠ 0) (A B : E →L[ℂ] E)
    (Z V S : unitary (E →L[ℂ] E)) (hS : IsSelfAdjoint (S : E →L[ℂ] E))
    (lam phase : ι → ℂ) (sigma beta : ι → ℝ)
    (hA : ∀ i, A (e i) = lam i • e i)
    (hB : ∀ i, B (e i) = (beta i : ℂ) • e i)
    (hV : ∀ i, (V : E →L[ℂ] E) (e i) = phase i • e i)
    (hSe : ∀ i, (S : E →L[ℂ] E) (e i) = (sigma i : ℂ) • e i)
    (hcase : ∀ i,
      ((Z : E →L[ℂ] E) (e i) = e i ∧ beta i = 1) ∨
      (phase i = (sigma i : ℂ) * Complex.I ∧
        lam i + star (lam i) = (2 * b * beta i : ℝ)))
    (hself : IsSelfAdjoint
      (star (V : E →L[ℂ] E) * (A - (b : ℂ) • (Z : E →L[ℂ] E)))) :
    (Z : E →L[ℂ] E) + (S : E →L[ℂ] E) * star (Z : E →L[ℂ] E) *
        (S : E →L[ℂ] E) = (2 : ℂ) • B := by
  classical
  have hAstar (i) : star A (e i) = star (lam i) • e i :=
    adjoint_apply_of_orthonormal_eigenbasis e A lam hA i
  have hVstar (i) : star (V : E →L[ℂ] E) (e i) = star (phase i) • e i :=
    adjoint_apply_of_orthonormal_eigenbasis e (V : E →L[ℂ] E) phase hV i
  let D := (V : E →L[ℂ] E) - Complex.I • (S : E →L[ℂ] E)
  have hDe (i) : D (e i) = (phase i - Complex.I * (sigma i : ℂ)) • e i := by
    change (V : E →L[ℂ] E) (e i) - Complex.I • (S : E →L[ℂ] E) (e i) = _
    rw [hV, hSe, smul_smul, sub_smul]
  have hfix : star (Z : E →L[ℂ] E) * D = D := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change star (Z : E →L[ℂ] E) (D (e i)) = D (e i)
    rw [hDe, map_smul]
    rcases hcase i with hi | hi
    · rw [star_unitary_fixes_of_fixes Z _ hi.1]
    · have hz : phase i - Complex.I * (sigma i : ℂ) = 0 := by rw [hi.1]; ring
      rw [hz, zero_smul, zero_smul]
  have hstarfix : (star (V : E →L[ℂ] E) + Complex.I • (S : E →L[ℂ] E)) *
      (Z : E →L[ℂ] E) = star (V : E →L[ℂ] E) + Complex.I • (S : E →L[ℂ] E) := by
    have h := congrArg star hfix
    simpa only [D, star_mul, star_sub, star_smul, star_star, RCLike.star_def,
      Complex.conj_I, hS.star_eq, neg_smul, sub_neg_eq_add] using h
  have hlin : (S : E →L[ℂ] E) * (Z : E →L[ℂ] E) +
      star (Z : E →L[ℂ] E) * (S : E →L[ℂ] E) =
        (2 : ℂ) • ((S : E →L[ℂ] E) * B) := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change (S : E →L[ℂ] E) ((Z : E →L[ℂ] E) (e i)) +
      star (Z : E →L[ℂ] E) ((S : E →L[ℂ] E) (e i)) =
        (2 : ℂ) • (S : E →L[ℂ] E) (B (e i))
    rcases hcase i with hi | hi
    · rw [hi.1, hSe, map_smul, star_unitary_fixes_of_fixes Z _ hi.1,
        hB, hi.2, Complex.ofReal_one, one_smul, hSe]
      module
    · have hzero : star (phase i) + Complex.I * (sigma i : ℂ) = 0 := by
        rw [hi.1]
        simp
        ring
      have hrep := congrArg (fun T : E →L[ℂ] E => T (e i)) hstarfix
      change star (V : E →L[ℂ] E) ((Z : E →L[ℂ] E) (e i)) +
        Complex.I • (S : E →L[ℂ] E) ((Z : E →L[ℂ] E) (e i)) =
          star (V : E →L[ℂ] E) (e i) + Complex.I • (S : E →L[ℂ] E) (e i) at hrep
      rw [hVstar, hSe, smul_smul, ← add_smul, hzero, zero_smul] at hrep
      have hrep' := eq_neg_of_add_eq_zero_left hrep
      have hv := congrArg (fun T : E →L[ℂ] E => T (e i)) hself.star_eq
      simp only [star_mul, star_sub, star_smul, RCLike.star_def, Complex.conj_ofReal,
        star_star, mul_apply_eq_comp, sub_apply,
        smul_apply, map_sub, map_smul, hV, hA, hAstar, hVstar] at hv
      rw [hrep'] at hv
      have hcoef : phase i * star (lam i) - lam i * star (phase i) =
          (b : ℂ) * Complex.I * (2 * (beta i : ℂ) * (sigma i : ℂ)) := by
        rw [hi.1]
        simp only [star_mul, RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
        calc
          _ = (sigma i : ℂ) * Complex.I * (lam i + star (lam i)) := by
            simp only [RCLike.star_def]
            ring
          _ = _ := by rw [hi.2]; push_cast; ring
      have hcomb : ((b : ℂ) * Complex.I) •
          ((S : E →L[ℂ] E) ((Z : E →L[ℂ] E) (e i)) +
            (sigma i : ℂ) • star (Z : E →L[ℂ] E) (e i)) =
          (phase i * star (lam i) - lam i * star (phase i)) • e i := by
        rw [hi.1] at hv ⊢
        simp only [RCLike.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I] at hv ⊢
        linear_combination (norm := module) -hv
      rw [hcoef, ← smul_smul ((b : ℂ) * Complex.I)
        (2 * (beta i : ℂ) * (sigma i : ℂ)) (e i)] at hcomb
      have hc := smul_right_injective E
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hb) Complex.I_ne_zero) hcomb
      rw [hSe, map_smul, hB, map_smul, hSe]
      simpa only [smul_smul, mul_assoc] using hc
  have hSS : (S : E →L[ℂ] E) * (S : E →L[ℂ] E) = 1 := by
    simpa only [hS.star_eq] using Unitary.star_mul_self_of_mem S.property
  calc
    _ = (S : E →L[ℂ] E) * ((S : E →L[ℂ] E) * (Z : E →L[ℂ] E) +
        star (Z : E →L[ℂ] E) * (S : E →L[ℂ] E)) := by
      rw [mul_add, ← mul_assoc, hSS, one_mul, mul_assoc]
    _ = (S : E →L[ℂ] E) * ((2 : ℂ) • ((S : E →L[ℂ] E) * B)) := by rw [hlin]
    _ = _ := by rw [mul_smul_comm, ← mul_assoc, hSS, one_mul]

/-- Certificate equality gives a positive average with the clipped
principal cosine. Fixed and subcritical directions are included in the
same ambient equation; no restriction of the competitor is assumed. -/
theorem paired_certificate_twisted_average_complex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →L[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (Z V : unitary (E →L[ℂ] E))
    (hV : ∀ j, (V : E →L[ℂ] E) (e j) = pairedDualPhase a b theta j • e j)
    (hself : IsSelfAdjoint
      (star (V : E →L[ℂ] E) * (A - (b : ℂ) • (Z : E →L[ℂ] E))))
    (hfix : ∀ i, b ≤ a * Real.cos (theta i) → ∀ r : Fin 2,
      (Z : E →L[ℂ] E) (e (.inl (r, i))) = e (.inl (r, i)))
    (hfixed : ∀ j, (Z : E →L[ℂ] E) (e (.inr j)) = e (.inr j)) :
    let c : ((Fin 2 × ι) ⊕ κ) → ℝ :=
      Sum.elim (fun j => Real.cos (theta j.2)) (fun _ => 1)
    let sigma : ((Fin 2 × ι) ⊕ κ) → ℝ :=
      Sum.elim (fun j => if j.1 = 0 then 1 else -1) (fun _ => 1)
    let B := (basisDiagonal e (fun j => min 1 (a * c j / b))).toContinuousLinearMap
    ∃ S : unitary (E →L[ℂ] E), IsSelfAdjoint (S : E →L[ℂ] E) ∧
      (∀ j, (S : E →L[ℂ] E) (e j) = (sigma j : ℂ) • e j) ∧
      (Z : E →L[ℂ] E) + (S : E →L[ℂ] E) * star (Z : E →L[ℂ] E) *
        (S : E →L[ℂ] E) = (2 : ℂ) • B ∧ Commute (Z : E →L[ℂ] E) B ∧ B.IsPositive := by
  classical
  let c : ((Fin 2 × ι) ⊕ κ) → ℝ :=
    Sum.elim (fun j => Real.cos (theta j.2)) (fun _ => 1)
  let sigma : ((Fin 2 × ι) ⊕ κ) → ℝ :=
    Sum.elim (fun j => if j.1 = 0 then 1 else -1) (fun _ => 1)
  let beta (j) := min 1 (a * c j / b)
  let B := (basisDiagonal e beta).toContinuousLinearMap
  have hc (j) : 0 ≤ c j := by
    rcases j with ⟨r, i⟩ | j
    · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [(hθ i).1, Real.pi_pos], (hθ i).2⟩
    · exact zero_le_one
  have hbeta (j) : 0 ≤ beta j :=
    le_min zero_le_one (div_nonneg (mul_nonneg (hb.le.trans hab.le) (hc j)) hb.le)
  have hBpos : B.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff B).mpr (isPositive_basisDiagonal e beta hbeta)
  have hsigmanorm (j) : ‖(sigma j : ℂ)‖ = 1 := by
    rcases j with ⟨r, i⟩ | j
    · dsimp only [sigma, Sum.elim_inl]
      split_ifs <;> norm_num
    · norm_num [sigma]
  obtain ⟨S', hS'⟩ := e.exists_linearIsometryEquiv_apply_eq_smul
    (fun j => (sigma j : ℂ)) hsigmanorm
  let S := Unitary.linearIsometryEquiv.symm S'
  have hSe (j) : (S : E →L[ℂ] E) (e j) = (sigma j : ℂ) • e j := hS' j
  have hS : IsSelfAdjoint (S : E →L[ℂ] E) := by
    change star (S : E →L[ℂ] E) = (S : E →L[ℂ] E)
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro j
    change star (S : E →L[ℂ] E) (e j) = (S : E →L[ℂ] E) (e j)
    rw [show star (S : E →L[ℂ] E) (e j) = star (sigma j : ℂ) • e j from
      adjoint_apply_of_orthonormal_eigenbasis e (S : E →L[ℂ] E) (fun j => (sigma j : ℂ)) hSe j,
      hSe]
    simp
  let lam : ((Fin 2 × ι) ⊕ κ) → ℂ := Sum.elim
    (fun j => if j.1 = 0 then
      (a * Real.cos (theta j.2) : ℝ) + (a * Real.sin (theta j.2)) * Complex.I else
      (a * Real.cos (theta j.2) : ℝ) - (a * Real.sin (theta j.2)) * Complex.I)
    (fun _ => (a : ℂ))
  have hAe (j) : A (e j) = lam j • e j := by
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        simpa [lam] using hA0 i
      · have hr1 : r = 1 := by omega
        subst r
        simpa [lam] using hA1 i
    · exact hAf j
  have hlam (j) : lam j + star (lam j) = (2 * a * c j : ℝ) := by
    rcases j with ⟨r, i⟩ | j
    · dsimp only [lam, c, Sum.elim_inl]
      split_ifs <;>
        apply Complex.ext <;>
        simp only [RCLike.star_def, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im] <;> ring
    · simp only [lam, c, Sum.elim_inr, RCLike.star_def, Complex.conj_ofReal]
      norm_num [Complex.ofReal_mul]
      ring
  have hcase (j) :
      ((Z : E →L[ℂ] E) (e j) = e j ∧ beta j = 1) ∨
      (pairedDualPhase a b theta j = (sigma j : ℂ) * Complex.I ∧
        lam j + star (lam j) = (2 * b * beta j : ℝ)) := by
    rcases j with ⟨r, i⟩ | j
    · by_cases hcut : b ≤ a * Real.cos (theta i)
      · left
        refine ⟨hfix i hcut r, ?_⟩
        change min 1 (a * Real.cos (theta i) / b) = 1
        exact min_eq_left ((le_div_iff₀ hb).mpr (by simpa only [one_mul] using hcut))
      · right
        have ht := dualPhase_eq_I_of_supercritical a b (theta i) hb.le hab (hθ i)
          (le_of_not_ge hcut)
        refine ⟨?_, ?_⟩
        · fin_cases r <;> simp [pairedDualPhase, sigma, ht]
        · rw [hlam]
          apply congrArg Complex.ofReal
          change 2 * a * Real.cos (theta i) = 2 * b * min 1 (a * Real.cos (theta i) / b)
          rw [min_eq_right ((div_le_one hb).mpr (le_of_not_ge hcut))]
          field_simp
    · left
      refine ⟨hfixed j, ?_⟩
      change min 1 (a * 1 / b) = 1
      rw [mul_one]
      exact min_eq_left ((le_div_iff₀ hb).mpr (by simpa only [one_mul] using hab.le))
  have havg := twisted_average_of_diagonal_certificate_complex e b hb.ne' A B Z V S hS lam
    (pairedDualPhase a b theta) sigma beta hAe
    (fun j => basisDiagonal_apply_basis e beta j) hV hSe hcase hself
  have hcomm := ContinuousLinearMap.commute_of_unitary_sum_eq_two_smul
    Z (S * star Z * S) B hBpos (by simpa only [Submonoid.coe_mul, Unitary.coe_star] using havg)
  exact ⟨S, hS, hSe, havg, hcomm.1, hBpos⟩

omit [FiniteDimensional ℂ E] in
/-- Clipping may merge different high eigenvalues, but a unitary fixing
all their eigenvectors still commutes with the original diagonal operator.
This recovers the principal cosine after the certificate clipped it. -/
theorem commute_of_clipped_diagonal_and_fixed_complex
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (c : ι → ℝ)
    (C B : E →L[ℂ] E) (hC : IsSelfAdjoint C) (hB : IsSelfAdjoint B)
    (hCe : ∀ i, C (e i) = (c i : ℂ) • e i)
    (hBe : ∀ i, B (e i) = ((min 1 (a * c i / b) : ℝ) : ℂ) • e i)
    (Z : unitary (E →L[ℂ] E)) (hcomm : Commute (Z : E →L[ℂ] E) B)
    (hfixed : ∀ i, b ≤ a * c i → (Z : E →L[ℂ] E) (e i) = e i) :
    Commute (Z : E →L[ℂ] E) C := by
  let D := C - ((b / a : ℝ) : ℂ) • B
  have hD : IsSelfAdjoint D := by
    change star (C - ((b / a : ℝ) : ℂ) • B) = C - ((b / a : ℝ) : ℂ) • B
    rw [star_sub, star_smul, hC.star_eq, hB.star_eq]
    simp only [RCLike.star_def, Complex.conj_ofReal]
  have hDe (i) : D (e i) = ((c i - b / a * min 1 (a * c i / b) : ℝ) : ℂ) • e i := by
    change C (e i) - ((b / a : ℝ) : ℂ) • B (e i) = _
    rw [hCe, hBe]
    push_cast
    module
  have hZD : (Z : E →L[ℂ] E) * D = D := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change (Z : E →L[ℂ] E) (D (e i)) = D (e i)
    rw [hDe, map_smul]
    by_cases hi : b ≤ a * c i
    · rw [hfixed i hi]
    · have hz : c i - b / a * min 1 (a * c i / b) = 0 := by
        rw [min_eq_right ((div_le_one hb).mpr (le_of_not_ge hi))]
        field_simp
        ring
      rw [hz, Complex.ofReal_zero, zero_smul, zero_smul]
  have hDZ : D * (Z : E →L[ℂ] E) = D := by
    have hs := congrArg star hZD
    simp only [star_mul, hD.star_eq] at hs
    have h := congrArg (fun T : E →L[ℂ] E => T * (Z : E →L[ℂ] E)) hs
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem Z.property, mul_one] using h.symm
  have hCeq : C = D + ((b / a : ℝ) : ℂ) • B := by dsimp only [D]; module
  change (Z : E →L[ℂ] E) * C = C * (Z : E →L[ℂ] E)
  rw [hCeq, mul_add, add_mul, hZD, hDZ, mul_smul_comm, smul_mul_assoc, hcomm.eq]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
