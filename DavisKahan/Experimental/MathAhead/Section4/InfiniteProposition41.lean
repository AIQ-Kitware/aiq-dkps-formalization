/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.MathAhead.Section4.InfiniteIdealDominance
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSelectedReduction
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction
import DavisKahan.Interop.Spectra.DirectRotationSquare
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import DavisKahan.Sylvester.GenuineSpectrum

/-!
# Infinite-dimensional Proposition 4.1 by spectral cutoff

The finite-dimensional proof diagonalizes the positive cosine and compares the
principal-plane chords one by one.  In arbitrary Hilbert space there need not
be a principal-vector basis.  The replacement is a spectral-cutoff/min--max
argument.

Let `C` be the positive cosine on the source space, `A` the direct-rotation
restricted displacement, and `B` a competing restricted displacement.  Given
`r < a_n(A)`, choose

```
r < s₁ < s₂ < a_n(A)
```

and the cosine thresholds `cᵢ = 1 - sᵢ² / 2`.  The low-cosine projection
`E_C((−∞, c₂])` must have rank greater than `n`; otherwise cutting it away
would approximate `A` to error at most `s₂`.  On that low-cosine spectral
range, the slightly larger threshold `c₁` gives `‖Cx‖ ≤ c₁‖x‖`.  Cauchy--
Schwarz and the intertwining condition then imply `s₁‖x‖ ≤ ‖Bx‖`.  The
approximation-number min--max theorem yields `r < a_n(B)`.

The use of two thresholds is intentional.  It avoids having to decide where
spectral mass at a cutoff endpoint belongs.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace Section4

open SpectraBridge
open ExactSinTheta
open DavisKahanExt
open Module (finrank)

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Abstract data needed by the spectral-cutoff proof.  This isolates the
operator-theoretic min--max argument from the geometry of two subspaces. -/
structure CosineDisplacementData
    (C : E →L[ℂ] E) (A B : E →L[ℂ] F) : Prop where
  cosine_selfAdjoint : IsSelfAdjointOperator C
  cosine_nonnegative : ∀ x, 0 ≤ RCLike.re ⟪C x, x⟫_ℂ
  direct_norm_le_sqrt_two : ‖A‖ ≤ Real.sqrt 2
  direct_norm_sq : ∀ x,
    ‖A x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * RCLike.re ⟪C x, x⟫_ℂ
  competitor_norm_sq_lower : ∀ x,
    2 * ‖x‖ ^ 2 - 2 * ‖C x‖ * ‖x‖ ≤ ‖B x‖ ^ 2

namespace CosineDisplacementData

/-- The cosine commutes with each of its spectral projections. -/
private theorem cosine_commutes_spectralProjection
    {C : E →L[ℂ] E} {A B : E →L[ℂ] F}
    (D : CosineDisplacementData C A B)
    (S : Set ℝ) (hS : MeasurableSet S) (x : E) :
    C (boundedSelfAdjointSpectralProjection C D.cosine_selfAdjoint S hS x) =
      boundedSelfAdjointSpectralProjection C D.cosine_selfAdjoint S hS (C x) :=
  boundedSelfAdjointSpectralProjection_apply_comm
    C D.cosine_selfAdjoint S hS x

/-- On the spectral range `(-∞, c₂]`, the cosine has norm at most every
strictly larger threshold `c₁`. -/
private theorem cosine_norm_le_on_low_range
    {C : E →L[ℂ] E} {A B : E →L[ℂ] F}
    (D : CosineDisplacementData C A B)
    {c₁ c₂ : ℝ} (hc₂0 : 0 ≤ c₂) (hc : c₂ < c₁)
    (x : E)
    (hx : x ∈ boundedSelfAdjointSpectralSubspace C D.cosine_selfAdjoint
      (Set.Iic c₂) measurableSet_Iic) :
    ‖C x‖ ≤ c₁ * ‖x‖ := by
  let PVM : TauCeti.ProjValMeasure E :=
    boundedSelfAdjointSpectralPVM C D.cosine_selfAdjoint
  let P : E →L[ℂ] E := PVM.proj (Set.Iic c₂) measurableSet_Iic
  have hPstar : P =
      (boundedSelfAdjointSpectralSubspace C D.cosine_selfAdjoint
        (Set.Iic c₂) measurableSet_Iic).starProjection := by
    exact boundedSelfAdjointSpectralProjection_eq_starProjection
      C D.cosine_selfAdjoint (Set.Iic c₂) measurableSet_Iic
  have hPx : P x = x := by
    exact pvmProjection_eq_self_of_mem_rangeSubspace
      (boundedSelfAdjointSpectralPVM C D.cosine_selfAdjoint)
      (Set.Iic c₂) measurableSet_Iic hx
  have hPcomm (z : E) : C (P z) = P (C z) := by
    exact D.cosine_commutes_spectralProjection
      (Set.Iic c₂) measurableSet_Iic z
  let CP : E →L[ℂ] E := C ∘L P
  have hCPsym : CP.IsSymmetric := by
    intro y z
    change ⟪C (P y), z⟫_ℂ = ⟪y, C (P z)⟫_ℂ
    calc
      ⟪C (P y), z⟫_ℂ = ⟪P y, C z⟫_ℂ :=
        D.cosine_selfAdjoint (P y) z
      _ = ⟪y, P (C z)⟫_ℂ := by
        rw [hPstar]
        exact Submodule.inner_starProjection_left_eq_right
          (boundedSelfAdjointSpectralSubspace C D.cosine_selfAdjoint
            (Set.Iic c₂) measurableSet_Iic) y (C z)
      _ = ⟪y, C (P z)⟫_ℂ := by rw [hPcomm]
  have hc₁0 : 0 ≤ c₁ := hc₂0.trans hc.le
  have hform : ∀ z,
      |RCLike.re ⟪CP z, z⟫_ℂ| ≤ c₁ * ‖z‖ ^ 2 := by
    intro z
    let y : E := P z
    have hyRange : y ∈ boundedSelfAdjointSpectralSubspace C
        D.cosine_selfAdjoint (Set.Iic c₂) measurableSet_Iic := by
      exact pvmProjection_mem_rangeSubspace
        (boundedSelfAdjointSpectralPVM C D.cosine_selfAdjoint)
        (Set.Iic c₂) measurableSet_Iic z
    have hhighZero :
        boundedSelfAdjointSpectralProjection C D.cosine_selfAdjoint
          (Set.Ici c₁) measurableSet_Ici y = 0 := by
      have hinter : Set.Ici c₁ ∩ Set.Iic c₂ = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic,
          Set.mem_empty_iff_false, iff_false]
        exact fun ht => (not_le_of_gt hc) (ht.1.trans ht.2)
      have hmul := PVM.proj_inter (Set.Ici c₁) (Set.Iic c₂)
        measurableSet_Ici measurableSet_Iic
      rw [PVM.proj_congr hinter (measurableSet_Ici.inter measurableSet_Iic)
        MeasurableSet.empty, PVM.proj_empty] at hmul
      exact congrArg (fun T : E →L[ℂ] E => T z) hmul
    have henergy :=
      TauCeti.BorelCalculus.re_inner_le_of_boundedPVM_proj_Ici_eq_zero
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr D.cosine_selfAdjoint)
        c₁ hhighZero
    have hnonneg : 0 ≤ RCLike.re ⟪C y, y⟫_ℂ := D.cosine_nonnegative y
    have hmove : RCLike.re ⟪CP z, z⟫_ℂ =
        RCLike.re ⟪C y, y⟫_ℂ := by
      change RCLike.re ⟪C (P z), z⟫_ℂ = RCLike.re ⟪C y, y⟫_ℂ
      have hPy : P y = y := by
        change PVM.proj (Set.Iic c₂) measurableSet_Iic
          (PVM.proj (Set.Iic c₂) measurableSet_Iic z) =
            PVM.proj (Set.Iic c₂) measurableSet_Iic z
        have hidem := PVM.proj_idem (Set.Iic c₂) measurableSet_Iic
        simpa only [mul_apply_eq_comp] using
          congrArg (fun T : E →L[ℂ] E => T z) hidem
      have hPCy : P (C y) = C y := by
        calc
          P (C y) = C (P y) := (hPcomm y).symm
          _ = C y := by rw [hPy]
      have hinnerP : ⟪P (C y), z⟫_ℂ = ⟪C y, P z⟫_ℂ := by
        rw [hPstar]
        exact Submodule.inner_starProjection_left_eq_right
          (boundedSelfAdjointSpectralSubspace C D.cosine_selfAdjoint
            (Set.Iic c₂) measurableSet_Iic) (C y) z
      calc
        RCLike.re ⟪C (P z), z⟫_ℂ = RCLike.re ⟪C y, z⟫_ℂ := rfl
        _ = RCLike.re ⟪P (C y), z⟫_ℂ := by rw [hPCy]
        _ = RCLike.re ⟪C y, P z⟫_ℂ := congrArg RCLike.re hinnerP
        _ = RCLike.re ⟪C y, y⟫_ℂ := rfl
    rw [hmove, abs_of_nonneg hnonneg]
    calc
      RCLike.re ⟪C y, y⟫_ℂ = (⟪C y, y⟫_ℂ).re := rfl
      _ ≤ c₁ * ‖y‖ ^ 2 := henergy
      _ ≤ c₁ * ‖z‖ ^ 2 := by
        have hyNorm : ‖y‖ ≤ ‖z‖ := by
          exact
            (boundedSelfAdjointSpectralPVM C D.cosine_selfAdjoint).norm_proj_apply_le
              (Set.Iic c₂) measurableSet_Iic z
        have hySq : ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hyNorm 2
        exact mul_le_mul_of_nonneg_left hySq hc₁0
  have hCPnorm : ‖CP‖ ≤ c₁ :=
    ForMathlib.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le
      hCPsym hc₁0 hform
  calc
    ‖C x‖ = ‖CP x‖ := by rw [show CP x = C x by simp [CP, hPx]]
    _ ≤ ‖CP‖ * ‖x‖ := CP.le_opNorm x
    _ ≤ c₁ * ‖x‖ := mul_le_mul_of_nonneg_right hCPnorm (norm_nonneg x)

/-- A strict lower threshold for the direct displacement transfers to the
competitor.  This is the hard min--max statement. -/
theorem lt_approximationNumber_competitor_of_lt_direct
    {C : E →L[ℂ] E} {A B : E →L[ℂ] F}
    (D : CosineDisplacementData C A B) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < (A.approximationNumber n : ℝ)) :
    r < (B.approximationNumber n : ℝ) := by
  classical
  let a : ℝ := (A.approximationNumber n : ℝ)
  let s₁ : ℝ := (2 * r + a) / 3
  let s₂ : ℝ := (r + 2 * a) / 3
  have hra : r < a := by simpa only [a] using hr
  have hrs₁ : r < s₁ := by dsimp only [s₁]; linarith
  have hs₁s₂ : s₁ < s₂ := by dsimp only [s₁, s₂]; linarith
  have hs₂a : s₂ < a := by dsimp only [s₂]; linarith
  have hs₁0 : 0 ≤ s₁ := hr0.trans hrs₁.le
  have hs₂0 : 0 ≤ s₂ := hs₁0.trans hs₁s₂.le
  have haNorm : a ≤ ‖A‖ := A.approximationNumber_le_norm n
  have hs₂sqrt : s₂ < Real.sqrt 2 :=
    hs₂a.trans_le (haNorm.trans D.direct_norm_le_sqrt_two)
  have hs₂sq : s₂ ^ 2 < 2 := by
    have h := (sq_lt_sq₀ hs₂0 (Real.sqrt_nonneg 2)).2 hs₂sqrt
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  let c₁ : ℝ := 1 - s₁ ^ 2 / 2
  let c₂ : ℝ := 1 - s₂ ^ 2 / 2
  have hc₂0 : 0 < c₂ := by dsimp [c₂]; linarith
  have hc₂c₁ : c₂ < c₁ := by
    dsimp [c₁, c₂]
    have hsquares : s₁ ^ 2 < s₂ ^ 2 := (sq_lt_sq₀ hs₁0 hs₂0).2 hs₁s₂
    linarith

  have hCsa : IsSelfAdjoint C :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr D.cosine_selfAdjoint
  let PVM : TauCeti.ProjValMeasure E :=
    boundedSelfAdjointSpectralPVM C D.cosine_selfAdjoint
  let P : E →L[ℂ] E := PVM.proj (Set.Iic c₂) measurableSet_Iic
  let Q : E →L[ℂ] E := PVM.proj (Set.Ioi c₂) measurableSet_Ioi
  have hQeq : Q = ContinuousLinearMap.id ℂ E - P := by
    have h := PVM.proj_compl (Set.Iic c₂) measurableSet_Iic
    rw [PVM.proj_congr Set.compl_Iic measurableSet_Iic.compl measurableSet_Ioi] at h
    exact h

  have htailNorm : ‖A ∘L Q‖ ≤ s₂ := by
    refine (A ∘L Q).opNorm_le_bound hs₂0 ?_
    intro x
    let y : E := Q x
    have hlowZero : PVM.proj (Set.Iic c₂) measurableSet_Iic y = 0 := by
      have hinter : Set.Iic c₂ ∩ Set.Ioi c₂ = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
          Set.mem_empty_iff_false, iff_false]
        exact fun ht => (not_lt_of_ge ht.1) ht.2
      have hmul := PVM.proj_inter (Set.Iic c₂) (Set.Ioi c₂)
        measurableSet_Iic measurableSet_Ioi
      rw [PVM.proj_congr hinter (measurableSet_Iic.inter measurableSet_Ioi)
        MeasurableSet.empty, PVM.proj_empty] at hmul
      exact congrArg (fun T : E →L[ℂ] E => T x) hmul
    have henergy :=
      TauCeti.BorelCalculus.le_re_inner_of_boundedPVM_proj_Iic_eq_zero
        hCsa c₂ hlowZero
    have hform : c₂ * ‖y‖ ^ 2 ≤ RCLike.re ⟪C y, y⟫_ℂ := by
      rw [RCLike.re_eq_complex_re]
      exact henergy
    have hsq : ‖A y‖ ^ 2 ≤ (s₂ * ‖y‖) ^ 2 := by
      rw [D.direct_norm_sq]
      calc
        2 * ‖y‖ ^ 2 - 2 * RCLike.re ⟪C y, y⟫_ℂ
            ≤ 2 * ‖y‖ ^ 2 - 2 * (c₂ * ‖y‖ ^ 2) := by
              exact sub_le_sub_left
                (mul_le_mul_of_nonneg_left hform (by norm_num)) _
        _ = (s₂ * ‖y‖) ^ 2 := by dsimp only [c₂]; ring
    have hAy : ‖A y‖ ≤ s₂ * ‖y‖ :=
      le_of_sq_le_sq hsq (mul_nonneg hs₂0 (norm_nonneg y))
    calc
      ‖(A ∘L Q) x‖ = ‖A y‖ := rfl
      _ ≤ s₂ * ‖y‖ := hAy
      _ ≤ s₂ * ‖x‖ :=
        mul_le_mul_of_nonneg_left
          (PVM.norm_proj_apply_le (Set.Ioi c₂) measurableSet_Ioi x) hs₂0

  have hPrank : ¬ P.rank ≤ (n : Cardinal) := by
    intro hP
    let R : E →L[ℂ] F := A ∘L P
    have hRrank : R.rank ≤ (n : Cardinal) :=
      ContinuousLinearMap.rank_comp_le_natCast_right P A hP
    have herr : A - R = A ∘L Q := by
      ext x
      change A x - A (P x) = A (Q x)
      rw [hQeq, sub_apply, ContinuousLinearMap.id_apply, map_sub]
    have happrox := A.approximationNumber_le_norm_sub hRrank
    have happroxReal : a ≤ ‖A - R‖ := happrox
    have has₂ : a ≤ s₂ := by
      calc
        a ≤ ‖A - R‖ := happroxReal
        _ = ‖A ∘L Q‖ := by rw [herr]
        _ ≤ s₂ := htailNorm
    exact (not_le_of_gt hs₂a) has₂

  let L : Submodule ℂ E :=
    pvmRangeSubspace PVM (Set.Iic c₂) measurableSet_Iic
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ L := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hPrank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨f, hf⟩ := (Module.le_rank_iff).mp hnrank
  let v : Fin (n + 1) → E := L.subtype ∘ f
  have hv : LinearIndependent ℂ v := by
    change LinearIndependent ℂ (L.subtype ∘ f)
    exact hf.map' L.subtype (LinearMap.ker_eq_bot.mpr L.injective_subtype)
  let M : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  have hMle : M ≤ L := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).2
  have hs₁NN : (⟨s₁, hs₁0⟩ : NNReal) ≤ B.approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      B n v hv
    intro x hxM hxNorm
    have hxL : x ∈ L := hMle hxM
    have hCbound : ‖C x‖ ≤ c₁ * ‖x‖ :=
      CosineDisplacementData.cosine_norm_le_on_low_range D hc₂0.le hc₂c₁ x hxL
    have hBsq0 := D.competitor_norm_sq_lower x
    have hBsq : (s₁ * ‖x‖) ^ 2 ≤ ‖B x‖ ^ 2 := by
      dsimp [c₁] at hCbound
      have hmul := mul_le_mul_of_nonneg_right hCbound (norm_nonneg x)
      nlinarith only [hBsq0, hmul]
    have hlower : s₁ * ‖x‖ ≤ ‖B x‖ :=
      (sq_le_sq₀ (mul_nonneg hs₁0 (norm_nonneg x)) (norm_nonneg _)).1 hBsq
    change s₁ ≤ ‖B x‖
    simpa only [hxNorm, mul_one] using hlower
  have hs₁le : s₁ ≤ (B.approximationNumber n : ℝ) := hs₁NN
  exact hrs₁.trans_le hs₁le

/-- Pointwise approximation-number dominance furnished by the spectral-cutoff
argument. -/
theorem approximationNumber_direct_le_competitor
    {C : E →L[ℂ] E} {A B : E →L[ℂ] F}
    (D : CosineDisplacementData C A B) (n : ℕ) :
    A.approximationNumber n ≤ B.approximationNumber n := by
  by_contra hnot
  have hlt : B.approximationNumber n < A.approximationNumber n :=
    lt_of_not_ge hnot
  have hltReal : (B.approximationNumber n : ℝ) <
      (A.approximationNumber n : ℝ) := by exact_mod_cast hlt
  have htransfer := D.lt_approximationNumber_competitor_of_lt_direct n
    (B.approximationNumber_nonneg n) hltReal
  exact (lt_irrefl (B.approximationNumber n : ℝ)) htransfer

end CosineDisplacementData

section DavisKahanGeometry

universe w

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

local instance sourceCompleteSpace : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- The positive cosine acting in source coordinates. -/
noncomputable def sourceCosine : U →L[ℂ] U := by
  let C : H →L[ℂ] H :=
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  have hCU : InvariantFor C U := by
    intro x hx
    apply U.starProjection_eq_self_iff.mp
    have hcomm := spectraCanonicalAbsoluteValue_commute_projection U V
    have happ := congrArg (fun T : H →L[ℂ] H => T x) hcomm.eq
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hx] at happ
    exact happ.symm
  exact C.restrict hCU

/-- Restricted displacement with source coordinates exposed. -/
noncomputable def sourceRestrictedDisplacement (T : H →L[ℂ] H) : U →L[ℂ] H :=
  (1 - T) ∘L U.subtypeL

@[simp]
theorem sourceCosine_apply_coe (x : U) :
    ((sourceCosine U V x : U) : H) =
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) (x : H) :=
  rfl

/-- The source cosine is self-adjoint. -/
theorem sourceCosine_selfAdjoint : IsSelfAdjointOperator (sourceCosine U V) := by
  intro x y
  change ⟪spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
      (x : H), (y : H)⟫_ℂ =
    ⟪(x : H), spectraOperatorAbsoluteValue
      (spectraCanonicalIntertwiner U V) (y : H)⟫_ℂ
  exact (spectraOperatorAbsoluteValue_isSelfAdjoint
    (spectraCanonicalIntertwiner U V)).isSymmetric (x : H) (y : H)

/-- The source cosine has nonnegative quadratic form. -/
theorem sourceCosine_nonnegative (x : U) :
    0 ≤ RCLike.re ⟪sourceCosine U V x, x⟫_ℂ := by
  change 0 ≤ RCLike.re
    ⟪spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
      (x : H), (x : H)⟫_ℂ
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (spectraOperatorAbsoluteValue_nonneg (spectraCanonicalIntertwiner U V))
  exact hpos.re_inner_nonneg_left (x : H)

/-- The norm of the source cosine is the norm of the target projection. -/
theorem norm_sourceCosine_eq_norm_targetProjection (x : U) :
    ‖sourceCosine U V x‖ = ‖projection V (x : H)‖ := by
  let C : H →L[ℂ] H :=
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  let P : H →L[ℂ] H := projection U
  let Q : H →L[ℂ] H := projection V
  have hxP : P (x : H) = (x : H) := Submodule.starProjection_eq_self_iff.mpr x.property
  have hCsa : star C = C :=
    (spectraOperatorAbsoluteValue_isSelfAdjoint
      (spectraCanonicalIntertwiner U V)).star_eq
  have hC2 : C * C = halmosCosineSq U V :=
    spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq U V
  have hCosx : halmosCosineSq U V (x : H) = P (Q (x : H)) := by
    simp only [halmosCosineSq, add_apply, mul_apply_eq_comp]
    rw [hxP]
    have hxPc : complementaryProjection U (x : H) = 0 := by
      change Uᗮ.starProjection (x : H) = 0
      apply (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      rw [Submodule.orthogonal_orthogonal]
      exact x.property
    rw [hxPc, map_zero, map_zero, add_zero]
  have hleft : ‖C (x : H)‖ ^ 2 =
      RCLike.re ⟪halmosCosineSq U V (x : H), (x : H)⟫_ℂ := by
    calc
      ‖C (x : H)‖ ^ 2 = RCLike.re ⟪(star C * C) (x : H), (x : H)⟫_ℂ := by
        simpa only [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.mul_def] using
          ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left C (x : H)
      _ = RCLike.re ⟪halmosCosineSq U V (x : H), (x : H)⟫_ℂ := by
        rw [hCsa, hC2]
  have hright : RCLike.re ⟪P (Q (x : H)), (x : H)⟫_ℂ =
      ‖Q (x : H)‖ ^ 2 := by
    calc
      RCLike.re ⟪P (Q (x : H)), (x : H)⟫_ℂ =
          RCLike.re ⟪Q (x : H), P (x : H)⟫_ℂ := by
        rw [U.inner_starProjection_left_eq_right]
      _ = RCLike.re ⟪Q (x : H), (x : H)⟫_ℂ := by rw [hxP]
      _ = ‖Q (x : H)‖ ^ 2 := by
        have hQfix : Q (Q (x : H)) = Q (x : H) := by
          dsimp only [Q]
          exact V.starProjection_eq_self_iff.mpr
            (V.starProjection_apply_mem (x : H))
        calc
          RCLike.re ⟪Q (x : H), (x : H)⟫_ℂ =
              RCLike.re ⟪Q (Q (x : H)), (x : H)⟫_ℂ := by rw [hQfix]
          _ = RCLike.re ⟪Q (x : H), Q (x : H)⟫_ℂ := by
            exact congrArg RCLike.re
              (V.inner_starProjection_left_eq_right (Q (x : H)) (x : H))
          _ = ‖Q (x : H)‖ ^ 2 := by
            exact (norm_sq_eq_re_inner (𝕜 := ℂ) (Q (x : H))).symm
  have hsquares : ‖C (x : H)‖ ^ 2 = ‖Q (x : H)‖ ^ 2 := by
    rw [hleft, hCosx, hright]
  have hnorm : ‖C (x : H)‖ = ‖Q (x : H)‖ := by
    nlinarith [norm_nonneg (C (x : H)), norm_nonneg (Q (x : H))]
  simpa [sourceCosine, C, Q] using hnorm

/-- The direct restricted displacement is modeled by the positive source
cosine. -/
theorem sourceRestrictedDisplacement_direct_norm_sq
    (hacute : IsAcute U V) (x : U) :
    ‖sourceRestrictedDisplacement U (spectraDirectRotation U V hacute) x‖ ^ 2 =
      2 * ‖x‖ ^ 2 - 2 * RCLike.re ⟪sourceCosine U V x, x⟫_ℂ := by
  let D : H →L[ℂ] H := spectraDirectRotation U V hacute
  have hunit : D ∈ unitary (H →L[ℂ] H) :=
    spectraDirectRotation_mem_unitary U V hacute
  have hdisp := norm_sub_one_apply_sq_of_mem_unitary D hunit (x : H)
  have hform := re_inner_spectraDirectRotation_eq_absoluteValue U V hacute
    (x : H)
  change ‖(1 - D) (x : H)‖ ^ 2 = _
  have hneg : (1 - D) (x : H) = -((D - 1) (x : H)) := by simp
  rw [hneg, norm_neg, hdisp, hform]
  rfl

/-- A competitor carrying `U` to `V` has real compression bounded by the
source cosine norm. -/
theorem competitor_real_inner_le_sourceCosine_norm
    (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) (x : U) :
    RCLike.re ⟪W (x : H), (x : H)⟫_ℂ ≤
      ‖sourceCosine U V x‖ * ‖x‖ := by
  let Q : H →L[ℂ] H := projection V
  have hWxV : W (x : H) ∈ V := by
    apply V.starProjection_eq_self_iff.mp
    have happ := congrArg (fun T : H →L[ℂ] H => T (x : H)) hWmap
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr x.property] at happ
    exact happ.symm
  have hQWx : Q (W (x : H)) = W (x : H) :=
    Submodule.starProjection_eq_self_iff.mpr hWxV
  have hinner : ⟪W (x : H), (x : H)⟫_ℂ =
      ⟪W (x : H), Q (x : H)⟫_ℂ := by
    calc
      ⟪W (x : H), (x : H)⟫_ℂ =
          ⟪Q (W (x : H)), (x : H)⟫_ℂ := by rw [hQWx]
      _ = ⟪W (x : H), Q (x : H)⟫_ℂ :=
        V.inner_starProjection_left_eq_right _ _
  calc
    RCLike.re ⟪W (x : H), (x : H)⟫_ℂ =
        RCLike.re ⟪W (x : H), Q (x : H)⟫_ℂ := by rw [hinner]
    _ ≤ ‖W (x : H)‖ * ‖Q (x : H)‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ = ‖sourceCosine U V x‖ * ‖x‖ := by
      rw [norm_sourceCosine_eq_norm_targetProjection U V x]
      have hWnorm : ‖W (x : H)‖ = ‖(x : H)‖ :=
        Unitary.norm_map (⟨W, hWunitary⟩ : unitary (H →L[ℂ] H)) (x : H)
      have hxnorm : ‖(x : H)‖ = ‖x‖ := rfl
      rw [hWnorm, hxnorm]
      exact mul_comm _ _

/-- The competitor displacement has the lower quadratic estimate required by
`CosineDisplacementData`. -/
theorem sourceRestrictedDisplacement_competitor_norm_sq_lower
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) (x : U) :
    2 * ‖x‖ ^ 2 - 2 * ‖sourceCosine U V x‖ * ‖x‖ ≤
      ‖sourceRestrictedDisplacement U W x‖ ^ 2 := by
  have hdisp := norm_sub_one_apply_sq_of_mem_unitary W hWunitary (x : H)
  have hreal := competitor_real_inner_le_sourceCosine_norm
    U V W hWunitary hWmap x
  change _ ≤ ‖(1 - W) (x : H)‖ ^ 2
  have hneg : (1 - W) (x : H) = -((W - 1) (x : H)) := by simp
  rw [hneg, norm_neg, hdisp]
  have hxnorm : ‖(x : H)‖ = ‖x‖ := rfl
  rw [hxnorm]
  linarith only [hreal]

/-- Assemble the geometric input for the infinite-dimensional min--max proof. -/
noncomputable def proposition4_1_cosineDisplacementData
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) :
    CosineDisplacementData
      (sourceCosine U V)
      (sourceRestrictedDisplacement U (spectraDirectRotation U V hacute))
      (sourceRestrictedDisplacement U W) where
  cosine_selfAdjoint := sourceCosine_selfAdjoint U V
  cosine_nonnegative := sourceCosine_nonnegative U V
  direct_norm_le_sqrt_two := by
    calc
      ‖sourceRestrictedDisplacement U (spectraDirectRotation U V hacute)‖
          ≤ ‖1 - spectraDirectRotation U V hacute‖ * ‖U.subtypeL‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.sqrt 2 * 1 := by
        gcongr
        · simpa [norm_sub_rev] using
            norm_spectraDirectRotation_sub_one_le_sqrt_two U V hacute
        · exact U.norm_subtypeL_le
      _ = Real.sqrt 2 := mul_one _
  direct_norm_sq := sourceRestrictedDisplacement_direct_norm_sq U V hacute
  competitor_norm_sq_lower :=
    sourceRestrictedDisplacement_competitor_norm_sq_lower U V W hWunitary hWmap

/-- Infinite-dimensional Proposition 4.1 in source coordinates. -/
theorem proposition4_1_source_approximationNumbers
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) (n : ℕ) :
    (sourceRestrictedDisplacement U
        (spectraDirectRotation U V hacute)).approximationNumber n ≤
      (sourceRestrictedDisplacement U W).approximationNumber n :=
  CosineDisplacementData.approximationNumber_direct_le_competitor
    (proposition4_1_cosineDisplacementData U V hacute W hWunitary hWmap) n

/-- The source-coordinate displacement extended by zero equals the ambient
restricted displacement. -/
theorem sourceRestrictedDisplacement_extendDomainByZero
    (T : H →L[ℂ] H) :
    sourceRestrictedDisplacement U T ∘L U.subtypeL.adjoint =
      (1 - T) ∘L projection U := by
  ext x
  simp [sourceRestrictedDisplacement, Submodule.adjoint_subtypeL]

/-- Extending a source-coordinate displacement by zero gives the same
approximation-singular-value sequence as the ambient restricted displacement. -/
theorem sourceRestrictedDisplacement_sameApproximationSingularSequence
    (T : H →L[ℂ] H) :
    SameApproximationSingularSequence
      ((1 - T) ∘L projection U) (sourceRestrictedDisplacement U T) := by
  intro n
  rw [← sourceRestrictedDisplacement_extendDomainByZero U T]
  exact sameApproximationSingularValues_extendDomainByZero U
    (sourceRestrictedDisplacement U T) n

/-- Infinite-dimensional Davis--Kahan Proposition 4.1 in the ambient form used
by the frontier. -/
theorem proposition4_1_restrictedDisplacement_approximationNumbers_scratch
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) (n : ℕ) :
    ContinuousLinearMap.approximationNumber
        ((1 - spectraDirectRotation U V hacute) ∘L projection U) n ≤
      ContinuousLinearMap.approximationNumber
        ((1 - W) ∘L projection U) n := by
  have hsource := proposition4_1_source_approximationNumbers
    U V hacute W hWunitary hWmap n
  have hDseq := sourceRestrictedDisplacement_sameApproximationSingularSequence
    U (spectraDirectRotation U V hacute) n
  have hWseq := sourceRestrictedDisplacement_sameApproximationSingularSequence
    U W n
  change approximationSingularValue n
      ((1 - spectraDirectRotation U V hacute) ∘L projection U) ≤
    approximationSingularValue n ((1 - W) ∘L projection U)
  calc
    approximationSingularValue n
        ((1 - spectraDirectRotation U V hacute) ∘L projection U) =
        approximationSingularValue n
          (sourceRestrictedDisplacement U
            (spectraDirectRotation U V hacute)) := hDseq
    _ ≤ approximationSingularValue n (sourceRestrictedDisplacement U W) := by
      simpa only [approximationSingularValue] using hsource
    _ = approximationSingularValue n ((1 - W) ∘L projection U) := hWseq.symm

/-- Package the hard theorem for the existing infinite ideal-dominance bridge. -/
noncomputable def infinite_restrictedDisplacementDominance
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) :
    RestrictedDisplacementApproximationDominance
      ((1 - spectraDirectRotation U V hacute) ∘L projection U)
      ((1 - W) ∘L projection U) where
  approximation_le := by
    intro n
    simpa only [approximationSingularValue] using
      proposition4_1_restrictedDisplacement_approximationNumbers_scratch
        U V hacute W hWunitary hWmap n

end DavisKahanGeometry

end

end Section4
end MathAhead
end Experimental
end DavisKahan
end TauCeti