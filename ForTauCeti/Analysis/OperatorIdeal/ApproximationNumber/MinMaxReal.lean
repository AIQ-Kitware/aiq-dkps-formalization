/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/

import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core
import ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus

/-!
# The real threshold theorem for approximation numbers

This module proves the real spectral-threshold form of the accepted complex
infinite-dimensional Courant--Fischer localization theorem, together with its
LUB / epsilon characterizations.

Mathlib's continuous functional calculus is available for bounded operators on complex
Hilbert spaces but not directly for bounded operators on real ones, so the proof works on
the complexification and descends.  The transport it needs — the canonical conjugation, the
descent of conjugation-fixed operators, and the complexification laws for the adjoint and
the Gram operator — is
`ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus`.  What is local
to this file is the continuous high-energy spectral cutoff, which is `private`.

## Main results

* `TauCeti.ApproximationNumber.exists_linearIndependent_lowerBound_of_lt_approximationNumber_real`:
  every strict lower bound for `aₙ(T)` is realized by a uniform lower modulus on a real
  `(n+1)`-dimensional subspace — the real Courant--Fischer localization;
* `TauCeti.ApproximationNumber.hasMinMaxLowerBound_real`: the packaged form, which is the
  hypothesis `kyFanGauge_add_le_of_exists_finiteRestriction` takes over `RCLike 𝕜` and which
  until now only `ℂ` could discharge;
* `TauCeti.ApproximationNumber.exists_finiteRestrictionApproximationNumber_gt_of_lt_real`;
* `TauCeti.ApproximationNumber.approximationNumber_isLUB_finiteRestrictions_real`;
* `TauCeti.ApproximationNumber.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound_real`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/Real/Threshold.lean`.
* Extraction class: **moved**, not restated.  Of its three non-Mathlib imports, two were
  already `ForTauCeti` and the third,
  `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`, is an export shim whose own
  docstring says every declaration in it is a forwarding name — so the module depended on no
  mathematics in the paper library.
* Namespace `TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal` became
  `TauCeti.ApproximationNumber`, the namespace of the `approximationNumber` these theorems
  are about.  The `_real` suffix stays: it distinguishes each statement from its `_complex`
  twin, which is what the suffix has always meant here.
* **317 lines came off on the way in.**  The module carried a `private` copy of thirty
  transport lemmas that are declaration-for-declaration the public API it already imported.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware,
  Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

open scoped InnerProductSpace ComplexConjugate Topology

namespace TauCeti
namespace ApproximationNumber

open Module (finrank)
open Filter
open TauCeti.RealComplexification

noncomputable section

universe v vF vG vH w

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! The real algebra structure and the real continuous functional calculus on the complexified
operator algebra are `scoped instance`s of `RealComplexification`, opened here.
They used to be reinstalled in this file as a second `local instance`, which made them a
*different declaration* from the one that module's lemmas are stated against — and proving the
two defeq is what timed out `isDefEq` when this file first tried to import them.  See lane
`{lane:CPLX-DEDUP-3}`. -/
open scoped TauCeti.RealComplexification

/-! ## Transport to the complexification

The conjugation, its induced involution on operators, and the complexification laws for the
adjoint and the Gram operator all live in
`ForTauCeti/Analysis/InnerProductSpace/Complexification/FunctionalCalculus.lean` and are
opened above.  This module used to carry a `private` copy of all thirty of them; they were
identical, so the copy is gone. -/

/-! ## Continuous high-energy cutoff -/

/-- A continuous cutoff which vanishes at energies at most `u²`, tends to one
at high energy, and gives a tail operator bounded by `u`. -/
private def spectralCutoff (u x : ℝ) : ℝ :=
  1 - u ^ 2 / max x (u ^ 2)

private theorem continuous_spectralCutoff (u : ℝ) (hu : 0 < u) :
    Continuous (spectralCutoff u) := by
  have hden : ∀ x : ℝ, max x (u ^ 2) ≠ 0 := by
    intro x hx
    have hle : u ^ 2 ≤ max x (u ^ 2) := le_max_right _ _
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    rw [hx] at hle
    linarith
  exact continuous_const.sub
    (continuous_const.div (continuous_id.max continuous_const) hden)

private theorem spectralCutoff_eq_zero_of_le
    {u x : ℝ} (hu : 0 < u) (hx : x ≤ u ^ 2) :
    spectralCutoff u x = 0 := by
  rw [spectralCutoff, max_eq_right hx]
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  rw [div_self hu2, sub_self]

private theorem spectralCutoff_tail_bound
    {u x : ℝ} (hu : 0 < u) (_hx0 : 0 ≤ x) :
    x * (1 - spectralCutoff u x) ^ 2 ≤ u ^ 2 := by
  by_cases hx : x ≤ u ^ 2
  · rw [spectralCutoff_eq_zero_of_le hu hx]
    simpa using hx
  · have hux : u ^ 2 < x := lt_of_not_ge hx
    have hxpos : 0 < x := (sq_pos_of_pos hu).trans hux
    rw [spectralCutoff, max_eq_left hux.le]
    have hid : 1 - (1 - u ^ 2 / x) = u ^ 2 / x := by ring
    rw [hid]
    have hmul : u ^ 4 ≤ u ^ 2 * x := by
      nlinarith [sq_nonneg (u ^ 2)]
    calc
      x * (u ^ 2 / x) ^ 2 = u ^ 4 / x := by
        field_simp [hxpos.ne']
      _ ≤ u ^ 2 := (div_le_iff₀ hxpos).2 hmul

private theorem spectralCutoff_lower_bound
    {u x : ℝ} (hu : 0 < u) :
    u ^ 2 * (spectralCutoff u x) ^ 2 ≤
      x * (spectralCutoff u x) ^ 2 := by
  by_cases hx : x ≤ u ^ 2
  · rw [spectralCutoff_eq_zero_of_le hu hx]
    simp
  · exact mul_le_mul_of_nonneg_right (le_of_not_ge hx)
      (sq_nonneg (spectralCutoff u x))

/-! ## The real threshold theorem -/

omit [CompleteSpace E] [CompleteSpace F] in
/-- Restriction to a real subspace cannot increase an approximation number.

The staged statement is already field-generic; this is it at `ℝ`. -/
theorem approximationNumber_comp_subtypeL_le_real
    (T : E →L[ℝ] F) (n : ℕ) (V : Submodule ℝ E) :
    (T ∘L V.subtypeL).approximationNumber n ≤ T.approximationNumber n :=
  T.approximationNumber_comp_subtypeL_le n V

/-- Approximation numbers of restrictions to real spans of `n+1` vectors. -/
def finiteRestrictionApproximationNumbersReal
    (T : E →L[ℝ] F) (n : ℕ) : Set ℝ :=
  T.finiteRestrictionApproximationNumbers n

omit [CompleteSpace E] [CompleteSpace F] in
/-- The ambient real approximation number bounds all finite restrictions. -/
theorem finiteRestrictionApproximationNumbersReal_upperBound
    (T : E →L[ℝ] F) (n : ℕ) :
    T.approximationNumber n ∈
      upperBounds (finiteRestrictionApproximationNumbersReal T n) :=
  T.finiteRestrictionApproximationNumbers_upperBound n

/-- Real spectral-threshold form of infinite-dimensional Courant--Fischer.
Every strict nonnegative lower bound for `a_n(T)` is improved to a uniform
lower modulus on a real `(n+1)`-dimensional subspace. -/
theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
    (T : E →L[ℝ] F) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < T.approximationNumber n) :
    ∃ s : ℝ, r < s ∧
      ∃ v : Fin (n + 1) → E, LinearIndependent ℝ v ∧
        ∀ x ∈ Submodule.span ℝ (Set.range v),
          s * ‖x‖ ≤ ‖T x‖ := by
  classical
  let a : ℝ := T.approximationNumber n
  let u : ℝ := (r + a) / 2
  have hru : r < u := by dsimp only [u, a]; linarith
  have hua : u < a := by dsimp only [u, a]; linarith
  have hu0 : 0 < u := by linarith
  -- Transport to the complexification: the functional calculus is available there.
  let Tc : RealComplexification E →L[ℂ] RealComplexification F := complexify T
  let C0 : E →L[ℝ] E := T.adjoint ∘L T
  let C : RealComplexification E →L[ℂ] RealComplexification E := Tc.adjoint ∘L Tc
  have hCeq : C = complexify C0 := by
    dsimp only [C, C0, Tc]
    exact (complexify_gram T).symm
  have hCnonneg : (0 : RealComplexification E →L[ℂ] RealComplexification E) ≤ C := by
    dsimp only [C]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Tc)
  have hC : IsSelfAdjoint C := IsSelfAdjoint.of_nonneg hCnonneg
  have hCfix : conjugateOperator C = C := by
    rw [hCeq, conjugateOperator_complexify]
  -- Split the spectrum of the Gram operator at `u ^ 2` with the continuous cutoff.
  let p : ℝ → ℝ := spectralCutoff u
  let q : ℝ → ℝ := fun x => 1 - p x
  have hpcont : Continuous p := continuous_spectralCutoff u hu0
  have hqcont : Continuous q := continuous_const.sub hpcont
  let Pc : RealComplexification E →L[ℂ] RealComplexification E := cfc p C
  let Qc : RealComplexification E →L[ℂ] RealComplexification E := cfc q C
  have hPcfix : conjugateOperator Pc = Pc := by
    dsimp only [Pc]
    exact conjugateOperator_cfc_eq C hC hCfix p hpcont.continuousOn
  let P : E →L[ℝ] E := realPartOperator Pc
  let Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  have hPcComplexify : complexify P = Pc := by
    dsimp only [P]
    exact complexify_realPartOperator hPcfix
  have hQcEq : Qc = ContinuousLinearMap.id ℂ (RealComplexification E) - Pc := by
    dsimp only [Qc, q, Pc]
    rw [cfc_sub (fun _ : ℝ => 1) p C,
      cfc_const_one ℝ C]
    rfl
  have hQcComplexify : complexify Q = Qc := by
    rw [hQcEq]
    dsimp only [Q]
    rw [complexify_sub, complexify_id, hPcComplexify]
  -- `C` is a Gram operator, so its real spectrum is nonnegative.
  have hCspec_nonneg : ∀ x ∈ spectrum ℝ C, 0 ≤ x := by
    intro x hx
    exact spectrum_nonneg_of_nonneg hCnonneg hx
  -- The high-energy piece: `T ∘L Q` has norm at most `u`.
  have hQcSelfAdjoint : IsSelfAdjoint Qc := cfc_predicate q C
  have htailGram :
      (Tc ∘L Qc).adjoint ∘L (Tc ∘L Qc) =
        cfc (fun x => x * (q x) ^ 2) C := by
    rw [ContinuousLinearMap.adjoint_comp, hQcSelfAdjoint.adjoint_eq]
    calc
      (Qc ∘L Tc.adjoint) ∘L (Tc ∘L Qc) =
          (Qc ∘L C) ∘L Qc := by
        simp only [C, ContinuousLinearMap.comp_assoc]
      _ = cfc (fun x => x * (q x) ^ 2) C := by
        change cfc q C * C * cfc q C = _
        calc
          cfc q C * C * cfc q C =
              cfc q C * cfc (fun x : ℝ => x) C * cfc q C := by
            rw [cfc_id' ℝ C]
          _ = cfc (fun x : ℝ => q x * x) C * cfc q C := by
            rw [cfc_mul q (fun x : ℝ => x) C
              hqcont.continuousOn continuous_id.continuousOn]
          _ = cfc (fun x : ℝ => (q x * x) * q x) C := by
            rw [cfc_mul (fun x : ℝ => q x * x) q C
              (hqcont.mul continuous_id).continuousOn hqcont.continuousOn]
          _ = cfc (fun x => x * (q x) ^ 2) C := by
            apply cfc_congr
            intro x _
            ring
  -- and its Gram operator is `x * q x ^ 2`, which the cutoff bounds by `u ^ 2`.
  have htailCfcNorm :
      ‖cfc (fun x => x * (q x) ^ 2) C‖ ≤ u ^ 2 := by
    refine norm_cfc_le (f := fun x : ℝ => x * (q x) ^ 2) (a := C)
      (sq_nonneg u) ?_
    intro x hx
    have hx0 := hCspec_nonneg x hx
    have hbound := spectralCutoff_tail_bound hu0 hx0
    change |x * (1 - spectralCutoff u x) ^ 2| ≤ u ^ 2
    rw [abs_of_nonneg (mul_nonneg hx0 (sq_nonneg _))]
    exact hbound
  have htailComplex : ‖Tc ∘L Qc‖ ≤ u := by
    have hsq : ‖Tc ∘L Qc‖ ^ 2 ≤ u ^ 2 := by
      calc
        ‖Tc ∘L Qc‖ ^ 2 =
            ‖(Tc ∘L Qc).adjoint ∘L (Tc ∘L Qc)‖ := by
              rw [sq, ContinuousLinearMap.norm_adjoint_comp_self]
        _ = ‖cfc (fun x => x * (q x) ^ 2) C‖ := by rw [htailGram]
        _ ≤ u ^ 2 := htailCfcNorm
    exact le_of_sq_le_sq hsq hu0.le
  have htailReal : ‖T ∘L Q‖ ≤ u := by
    rw [← norm_complexify]
    rw [complexify_comp, hQcComplexify]
    exact htailComplex
  -- The low-energy piece: on the range of `P` the modulus is bounded below by `u`.
  have hlowerCfcNonneg :
      (0 : RealComplexification E →L[ℂ] RealComplexification E) ≤
        cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C := by
    apply cfc_nonneg
    intro x hx
    have hx0 := hCspec_nonneg x hx
    have hcut := spectralCutoff_lower_bound (x := x) hu0
    change 0 ≤ (x - u ^ 2) * (spectralCutoff u x) ^ 2
    nlinarith
  have hlowerIdentity :
      cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
        Pc * C * Pc - u ^ 2 • (Pc * Pc) := by
    have hpcmul : Pc * Pc = cfc (fun x => (p x) ^ 2) C := by
      dsimp only [Pc]
      calc
        cfc p C * cfc p C = cfc (fun x : ℝ => p x * p x) C :=
          (cfc_mul p p C hpcont.continuousOn hpcont.continuousOn).symm
        _ = cfc (fun x => (p x) ^ 2) C := by
          apply cfc_congr
          intro x _
          ring
    have hpcCpc : Pc * C * Pc = cfc (fun x => x * (p x) ^ 2) C := by
      dsimp only [Pc]
      calc
        cfc p C * C * cfc p C =
            cfc p C * cfc (fun x : ℝ => x) C * cfc p C := by
          rw [cfc_id' ℝ C]
        _ = cfc (fun x : ℝ => p x * x) C * cfc p C := by
          rw [cfc_mul p (fun x : ℝ => x) C
            hpcont.continuousOn continuous_id.continuousOn]
        _ = cfc (fun x : ℝ => (p x * x) * p x) C := by
          rw [cfc_mul (fun x : ℝ => p x * x) p C
            (hpcont.mul continuous_id).continuousOn hpcont.continuousOn]
        _ = cfc (fun x => x * (p x) ^ 2) C := by
          apply cfc_congr
          intro x _
          ring
    have hscale :
        u ^ 2 • (Pc * Pc) = cfc (fun x => u ^ 2 * (p x) ^ 2) C := by
      rw [hpcmul]
      calc
        u ^ 2 • cfc (fun x => (p x) ^ 2) C =
            @SMul.smul ℝ
              (RealComplexification E →L[ℂ] RealComplexification E)
              TauCeti.RealComplexification.complexOperatorRealAlgebra.toSMul (u ^ 2)
              (cfc (fun x => (p x) ^ 2) C) := by
          exact (restrictedReal_smul_operator_eq
            (u ^ 2) (cfc (fun x => (p x) ^ 2) C)).symm
        _ = cfc (fun x => u ^ 2 * (p x) ^ 2) C :=
          (cfc_const_mul (u ^ 2) (fun x => (p x) ^ 2) C
            (hpcont.fun_pow 2).continuousOn).symm
    calc
      cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
          cfc (fun x => x * (p x) ^ 2 - u ^ 2 * (p x) ^ 2) C := by
        apply cfc_congr
        intro x _
        ring
      _ = cfc (fun x => x * (p x) ^ 2) C -
          cfc (fun x => u ^ 2 * (p x) ^ 2) C := by
        exact cfc_sub (fun x => x * (p x) ^ 2)
          (fun x => u ^ 2 * (p x) ^ 2) C
          ((continuous_id.mul (hpcont.fun_pow 2)).continuousOn)
          ((continuous_const.mul (hpcont.fun_pow 2)).continuousOn)
      _ = Pc * C * Pc - u ^ 2 • (Pc * Pc) := by
        rw [← hpcCpc, ← hscale]
  have hPcLower : ∀ z : RealComplexification E, u * ‖Pc z‖ ≤ ‖Tc (Pc z)‖ := by
    intro z
    have hpositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp hlowerCfcNonneg
    have hform := hpositive.re_inner_nonneg_left z
    rw [hlowerIdentity] at hform
    have henergy :
        u ^ 2 * ‖Pc z‖ ^ 2 ≤ ‖Tc (Pc z)‖ ^ 2 := by
      change 0 ≤
        RCLike.re ⟪(Pc * C * Pc - u ^ 2 • (Pc * Pc)) z, z⟫_ℂ at hform
      have hPcsa : IsSelfAdjoint Pc := cfc_predicate p C
      have h1 :
          RCLike.re ⟪(Pc * C * Pc) z, z⟫_ℂ = ‖Tc (Pc z)‖ ^ 2 := by
        simp only [mul_apply_eq_comp]
        have hadj : ⟪Pc (C (Pc z)), z⟫_ℂ = ⟪C (Pc z), Pc z⟫_ℂ := by
          simpa only [hPcsa.adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_left Pc z (C (Pc z)))
        rw [hadj]
        dsimp only [C]
        exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left Tc (Pc z)).symm
      have h2 :
          RCLike.re ⟪(u ^ 2 • (Pc * Pc)) z, z⟫_ℂ =
            u ^ 2 * ‖Pc z‖ ^ 2 := by
        have hadj : ⟪Pc (Pc z), z⟫_ℂ = ⟪Pc z, Pc z⟫_ℂ := by
          simpa only [hPcsa.adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_left Pc z (Pc z))
        simp only [smul_apply, mul_apply_eq_comp]
        rw [inner_smul_left_eq_smul, hadj, inner_self_eq_norm_sq_to_K,
          RCLike.smul_re, RCLike.re_ofReal_pow]
      have hform' :
          0 ≤ RCLike.re ⟪(Pc * C * Pc) z, z⟫_ℂ -
            RCLike.re ⟪(u ^ 2 • (Pc * Pc)) z, z⟫_ℂ := by
        simpa only [sub_apply, inner_sub_left, map_sub] using hform
      rw [h1, h2] at hform'
      linarith
    exact le_of_sq_le_sq (by simpa [mul_pow] using henergy) (norm_nonneg _)
  have hPLower : ∀ x : E, u * ‖P x‖ ≤ ‖T (P x)‖ := by
    intro x
    have h := hPcLower (ofReal x)
    have hPcReal : Pc (ofReal x) = ofReal (P x) := by
      rw [← hPcComplexify, complexify_ofReal]
    calc
      u * ‖P x‖ = u * ‖Pc (ofReal x)‖ := by
        rw [hPcReal, ofReal.norm_map]
      _ ≤ ‖Tc (Pc (ofReal x))‖ := h
      _ = ‖T (P x)‖ := by
        rw [hPcReal]
        dsimp only [Tc]
        rw [complexify_ofReal, ofReal.norm_map]
  -- If `P` had rank at most `n` it would exhibit `a_n(T) ≤ u`, contradicting `u < a`.
  have hPrank : ¬ P.rank ≤ (n : Cardinal) := by
    intro hP
    let R : E →L[ℝ] F := T ∘L P
    -- `R.rank` and `P.rank` live in different universes once the codomain is
    -- independent, so the comparison goes through the natural-number bound.
    have hRrank : R.rank ≤ (n : Cardinal) :=
      ContinuousLinearMap.rank_comp_le_natCast_right P T hP
    have herr : T - R = T ∘L Q := by
      ext x
      change T x - T (P x) = T (Q x)
      dsimp only [Q]
      rw [sub_apply, ContinuousLinearMap.id_apply, map_sub]
    have happroxReal : a ≤ ‖T - R‖ := T.approximationNumber_le_norm_sub hRrank
    have hau : a ≤ u := by
      calc
        a ≤ ‖T - R‖ := happroxReal
        _ = ‖T ∘L Q‖ := by rw [herr]
        _ ≤ u := htailReal
    exact (not_le_of_gt hua) hau
  -- So `P.range` has rank at least `n + 1`; extract the independent family from it.
  let W : Submodule ℝ E := P.range
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ W := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hPrank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨f, hf⟩ := (Module.le_rank_iff).mp hnrank
  let v : Fin (n + 1) → E := W.subtype ∘ f
  have hv : LinearIndependent ℝ v := by
    change LinearIndependent ℝ (W.subtype ∘ f)
    exact hf.map' W.subtype
      (LinearMap.ker_eq_bot.mpr W.injective_subtype)
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hVle : V ≤ W := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).2
  refine ⟨u, hru, v, hv, ?_⟩
  intro x hxV
  have hxW : x ∈ W := hVle hxV
  obtain ⟨y, hy⟩ := hxW
  rw [← hy]
  exact hPLower y

/-- Over `ℝ` the min--max lower-bound property is the real threshold theorem above, which
is where the complexification is paid for.  Everything the localization theory needs from the
scalar field is this one fact — see `ContinuousLinearMap.HasMinMaxLowerBound`. -/
theorem hasMinMaxLowerBound_real :
    ContinuousLinearMap.HasMinMaxLowerBound ℝ E F :=
  fun T n _ hr0 hr =>
    exists_linearIndependent_lowerBound_of_lt_approximationNumber_real T n hr0 hr

/-- Every strict real lower threshold for the ambient approximation number is
exceeded by an approximation number of an `(n+1)`-generated real restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt_real
    (T : E →L[ℝ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < T.approximationNumber n) :
    ∃ v : Fin (n + 1) → E,
      r < (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n :=
  hasMinMaxLowerBound_real.exists_finiteRestrictionApproximationNumber_gt_of_lt T n hr0 hr

/-- Exact real finite-dimensional localization: the ambient approximation
number is the least upper bound of the approximation numbers of restrictions
to spans of `n+1` real vectors. -/
theorem approximationNumber_isLUB_finiteRestrictions_real
    (T : E →L[ℝ] F) (n : ℕ) :
    IsLUB (finiteRestrictionApproximationNumbersReal T n)
      (T.approximationNumber n) :=
  hasMinMaxLowerBound_real.approximationNumber_isLUB_finiteRestrictions T n

/-- Epsilon-form real generalized Courant--Fischer characterization. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound_real
    (T : E →L[ℝ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < T.approximationNumber n ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent ℝ v ∧
          ∀ x ∈ Submodule.span ℝ (Set.range v),
            s * ‖x‖ ≤ ‖T x‖ :=
  hasMinMaxLowerBound_real.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    T n hr0

end

end ApproximationNumber
end TauCeti
