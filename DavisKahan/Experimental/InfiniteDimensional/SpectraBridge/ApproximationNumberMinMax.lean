/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberMinMax
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.Basic
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.PVMSubspace
import Spectra.SpectralTheory.ResolventForm
import Spectra.SpectralTheory.Algebra

/-!
# Infinite-dimensional Courant--Fischer localization for approximation numbers

For a bounded operator between complex Hilbert spaces, the `n`th approximation
number is already detected on finite-dimensional source subspaces. The proof is
the spectral-theorem extension of Courant--Fischer applied to the bounded
positive Gram operator `T⋆T`.

The core threshold theorem says that every strict lower bound for `a_n(T)` is
realized, with margin, as a uniform lower modulus on an `(n+1)`-dimensional
subspace. The exact localization is expressed as an `IsLUB` statement for the
set of approximation numbers of these finite restrictions. This formulation is
appropriate for `NNReal`, which is conditionally complete rather than a
complete lattice.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open Module (finrank)
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Restriction to a subspace cannot increase an approximation number. -/
theorem approximationNumber_comp_subtypeL_le
    (T : E →L[ℂ] F) (n : ℕ) (V : Submodule ℂ E) :
    (T ∘L V.subtypeL).approximationNumber n ≤ T.approximationNumber n := by
  have h := T.approximationNumber_comp_right_le V.subtypeL n
  have hsub : ‖V.subtypeL‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast V.norm_subtypeL_le
  calc
    (T ∘L V.subtypeL).approximationNumber n
        ≤ T.approximationNumber n * ‖V.subtypeL‖₊ := h
    _ ≤ T.approximationNumber n * 1 :=
      mul_le_mul_of_nonneg_left hsub
        (show (0 : NNReal) ≤ T.approximationNumber n from bot_le)
    _ = T.approximationNumber n := by rw [mul_one]

/-- Approximation numbers obtained by restricting `T` to spans of `n+1`
vectors. Linearly dependent families are harmless: they merely contribute
smaller-dimensional restrictions. -/
def finiteRestrictionApproximationNumbers
    (T : E →L[ℂ] F) (n : ℕ) : Set NNReal :=
  Set.range fun v : Fin (n + 1) → E =>
    (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n

/-- The ambient approximation number is an upper bound for all finite
restrictions. -/
theorem finiteRestrictionApproximationNumbers_upperBound
    (T : E →L[ℂ] F) (n : ℕ) :
    T.approximationNumber n ∈
      upperBounds (finiteRestrictionApproximationNumbers T n) := by
  rintro _ ⟨v, rfl⟩
  exact approximationNumber_comp_subtypeL_le T n
    (Submodule.span ℂ (Set.range v))

/-- Spectral-threshold form of the infinite-dimensional Courant--Fischer
principle. Every strict nonnegative lower bound for `a_n(T)` can be improved to
a uniform lower modulus on an `(n+1)`-dimensional subspace. -/
theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < (T.approximationNumber n : ℝ)) :
    ∃ s : ℝ, r < s ∧
      ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
        ∀ x ∈ Submodule.span ℂ (Set.range v),
          s * ‖x‖ ≤ ‖T x‖ := by
  classical
  let a : ℝ := (T.approximationNumber n : ℝ)
  let s : ℝ := (2 * r + a) / 3
  let u : ℝ := (r + 2 * a) / 3
  have hrs : r < s := by dsimp only [s, a]; linarith
  have hsu : s < u := by dsimp only [s, u, a]; linarith
  have hua : u < a := by dsimp only [u, a]; linarith
  have hs0 : 0 ≤ s := hr0.trans hrs.le
  have hu0 : 0 ≤ u := hs0.trans hsu.le
  have hsq : s ^ 2 < u ^ 2 := by nlinarith

  let C : E →L[ℂ] E := T.adjoint ∘L T
  have hC : IsSelfAdjoint C := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change ⟪T.adjoint (T x), y⟫_ℂ = ⟪x, T.adjoint (T y)⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
  let A : Spectra.Operator.SelfAdjointOperator E :=
    Spectra.Operator.SelfAdjointOperator.ofBounded C hC
  have hA : IsSelfAdjoint A.toLinearPMap := A.selfAdjoint
  let U := genToGroup hA
  let PVM : Spectra.ProjValMeasure E := spectralPVM hA
  let P : E →L[ℂ] E := PVM.proj (Set.Ioi (s ^ 2)) measurableSet_Ioi
  let Q : E →L[ℂ] E := PVM.proj (Set.Iic (s ^ 2)) measurableSet_Iic

  have hgen : generator U = A.toLinearPMap := by
    dsimp only [U]
    exact generator_genToGroup hA
  have hAdom : A.toLinearPMap.domain = ⊤ := by
    dsimp only [A]
    exact Spectra.Operator.SelfAdjointOperator.domain_ofBounded C hC
  have hdom : (generator U).domain = ⊤ := by
    rw [hgen, hAdom]
  have hgenApply (x : E) (hx : x ∈ (generator U).domain) :
      generator U ⟨x, hx⟩ = C x := by
    have hxA : x ∈ A.toLinearPMap.domain := by
      rw [hAdom]
      exact Submodule.mem_top
    have happly := (LinearPMap.ext_iff.mp hgen).2
    calc
      generator U ⟨x, hx⟩ = A.toLinearPMap ⟨x, hxA⟩ :=
        happly (x := x) (hf := hx) (hg := hxA)
      _ = C x := rfl

  have hQeq : Q = ContinuousLinearMap.id ℂ E - P := by
    change spectralProjection U (Set.Iic (s ^ 2)) measurableSet_Iic =
      ContinuousLinearMap.id ℂ E -
        spectralProjection U (Set.Ioi (s ^ 2)) measurableSet_Ioi
    simpa only [Set.compl_Ioi] using
      (spectralProjection_compl U (Set.Ioi (s ^ 2)) measurableSet_Ioi)

  have hIciIic : Set.Ici (u ^ 2) ∩ Set.Iic (s ^ 2) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic,
      Set.mem_empty_iff_false, iff_false]
    exact fun hz => (not_le_of_gt hsq) (hz.1.trans hz.2)
  have hIicIoi : Set.Iic (s ^ 2) ∩ Set.Ioi (s ^ 2) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_empty_iff_false, iff_false]
    exact fun hz => (not_lt_of_ge hz.1) hz.2

  have htailNorm : ‖T ∘L Q‖ ≤ u := by
    refine (T ∘L Q).opNorm_le_bound hu0 ?_
    intro x
    let y : E := Q x
    have hyDom : y ∈ (generator U).domain := by
      rw [hdom]
      exact Submodule.mem_top
    have hhighZero :
        spectralProjection U (Set.Ici (u ^ 2)) measurableSet_Ici y = 0 := by
      change spectralProjection U (Set.Ici (u ^ 2)) measurableSet_Ici
        (spectralProjection U (Set.Iic (s ^ 2)) measurableSet_Iic x) = 0
      rw [← mul_apply_eq_comp, spectralProjection_inter U,
        spectralProjection_congr U hIciIic
          (measurableSet_Ici.inter measurableSet_Iic) MeasurableSet.empty,
        spectralProjection_empty U, zero_apply]
    have henergy := energy_upper_bound_of_spectralProjection_Ici_eq_zero
      U (u ^ 2) (⟨y, hyDom⟩ : (generator U).domain) hhighZero
    have hquad : ‖T y‖ ^ 2 ≤ u ^ 2 * ‖y‖ ^ 2 := by
      calc
        ‖T y‖ ^ 2 = (⟪C y, y⟫_ℂ).re := by
          change ‖T y‖ ^ 2 =
            (⟪(T.adjoint ∘L T) y, y⟫_ℂ).re
          exact ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T y
        _ = (⟪generator U ⟨y, hyDom⟩, y⟫_ℂ).re := by
          rw [hgenApply y hyDom]
        _ ≤ u ^ 2 * ‖y‖ ^ 2 := henergy
    have hquad' : ‖T y‖ ^ 2 ≤ (u * ‖y‖) ^ 2 := by
      calc
        ‖T y‖ ^ 2 ≤ u ^ 2 * ‖y‖ ^ 2 := hquad
        _ = (u * ‖y‖) ^ 2 := by ring
    have hyNorm : ‖T y‖ ≤ u * ‖y‖ :=
      le_of_sq_le_sq hquad' (mul_nonneg hu0 (norm_nonneg y))
    calc
      ‖(T ∘L Q) x‖ = ‖T y‖ := rfl
      _ ≤ u * ‖y‖ := hyNorm
      _ ≤ u * ‖x‖ :=
        mul_le_mul_of_nonneg_left (PVM.norm_proj_apply_le
          (Set.Iic (s ^ 2)) measurableSet_Iic x) hu0

  have hPrank : ¬ P.rank ≤ (n : Cardinal) := by
    intro hP
    let R : E →L[ℂ] F := T ∘L P
    have hRrank : R.rank ≤ (n : Cardinal) := by
      calc
        R.rank ≤ P.rank := by
          change LinearMap.rank (T.toLinearMap.comp P.toLinearMap) ≤ P.rank
          exact LinearMap.rank_comp_le_right P.toLinearMap T.toLinearMap
        _ ≤ (n : Cardinal) := hP
    have herr : T - R = T ∘L Q := by
      ext x
      change T x - T (P x) = T (Q x)
      rw [hQeq, sub_apply, ContinuousLinearMap.id_apply, map_sub]
    have happrox := T.approximationNumber_le hRrank
    have happroxReal : a ≤ ‖T - R‖ := by
      have hco := NNReal.coe_le_coe.mpr happrox
      change a ≤ ‖T - R‖ at hco
      exact hco
    have hau : a ≤ u := by
      calc
        a ≤ ‖T - R‖ := happroxReal
        _ = ‖T ∘L Q‖ := by rw [herr]
        _ ≤ u := htailNorm
    exact (not_le_of_gt hua) hau

  let W : Submodule ℂ E :=
    pvmRangeSubspace PVM (Set.Ioi (s ^ 2)) measurableSet_Ioi
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ W := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hPrank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨f, hf⟩ := (Module.le_rank_iff).mp hnrank
  let v : Fin (n + 1) → E := W.subtype ∘ f
  have hv : LinearIndependent ℂ v := by
    change LinearIndependent ℂ (W.subtype ∘ f)
    exact hf.map' W.subtype
      (LinearMap.ker_eq_bot.mpr W.injective_subtype)
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  have hVle : V ≤ W := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).2
  refine ⟨s, hrs, v, hv, ?_⟩
  intro x hxV
  have hxW : x ∈ W := hVle hxV
  have hPfix : P x = x := by
    exact pvmProjection_eq_self_of_mem_rangeSubspace
      PVM (Set.Ioi (s ^ 2)) measurableSet_Ioi hxW
  have hlowZero :
      spectralProjection U (Set.Iic (s ^ 2)) measurableSet_Iic x = 0 := by
    rw [← hPfix]
    change spectralProjection U (Set.Iic (s ^ 2)) measurableSet_Iic
      (spectralProjection U (Set.Ioi (s ^ 2)) measurableSet_Ioi x) = 0
    rw [← mul_apply_eq_comp, spectralProjection_inter U,
      spectralProjection_congr U hIicIoi
        (measurableSet_Iic.inter measurableSet_Ioi) MeasurableSet.empty,
      spectralProjection_empty U, zero_apply]
  have hxDom : x ∈ (generator U).domain := by
    rw [hdom]
    exact Submodule.mem_top
  have henergy := energy_lower_bound_of_spectralProjection_Iic_eq_zero
    U (s ^ 2) (⟨x, hxDom⟩ : (generator U).domain) hlowZero
  have hquad : (s * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    calc
      (s * ‖x‖) ^ 2 = s ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ (⟪generator U ⟨x, hxDom⟩, x⟫_ℂ).re := henergy
      _ = (⟪C x, x⟫_ℂ).re := by rw [hgenApply x hxDom]
      _ = ‖T x‖ ^ 2 := by
        change (⟪(T.adjoint ∘L T) x, x⟫_ℂ).re = ‖T x‖ ^ 2
        exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T x).symm
  exact le_of_sq_le_sq hquad (norm_nonneg (T x))

/-- Every strict lower threshold for the ambient approximation number is
exceeded by an approximation number of an `(n+1)`-generated restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt
    (T : E →L[ℂ] F) (n : ℕ) {r : NNReal}
    (hr : r < T.approximationNumber n) :
    ∃ v : Fin (n + 1) → E,
      r < (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n := by
  have hrReal : (r : ℝ) < (T.approximationNumber n : ℝ) := by
    exact_mod_cast hr
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    exists_linearIndependent_lowerBound_of_lt_approximationNumber
      T n (NNReal.coe_nonneg r) hrReal
  have hs0 : 0 ≤ s := (NNReal.coe_nonneg r).trans hrs.le
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
  let w : Fin (n + 1) → V := fun i => b i
  have hw : LinearIndependent ℂ w := by
    simpa only [w] using b.linearIndependent
  have hsNN : (⟨s, hs0⟩ : NNReal) ≤
      (T ∘L V.subtypeL).approximationNumber n := by
    apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
      (T ∘L V.subtypeL) n w hw
    intro x _ hxNorm
    have hxV : ((x : V) : E) ∈ V := x.property
    have hxNormE : ‖((x : V) : E)‖ = 1 := by
      simpa using hxNorm
    change s ≤ ‖T ((x : V) : E)‖
    calc
      s = s * ‖((x : V) : E)‖ := by rw [hxNormE, mul_one]
      _ ≤ ‖T ((x : V) : E)‖ := hV ((x : V) : E) hxV
  have hrsNN : r < (⟨s, hs0⟩ : NNReal) := by
    change (r : ℝ) < s
    exact hrs
  refine ⟨v, ?_⟩
  simpa only [V] using hrsNN.trans_le hsNN

/-- Exact finite-dimensional localization: the ambient approximation number is
the least upper bound of the approximation numbers of the restrictions to
spans of `n+1` vectors. -/
theorem approximationNumber_isLUB_finiteRestrictions
    (T : E →L[ℂ] F) (n : ℕ) :
    IsLUB (finiteRestrictionApproximationNumbers T n)
      (T.approximationNumber n) := by
  refine ⟨finiteRestrictionApproximationNumbers_upperBound T n, ?_⟩
  intro b hb
  by_contra hnot
  have hlt : b < T.approximationNumber n := lt_of_not_ge hnot
  obtain ⟨v, hv⟩ :=
    exists_finiteRestrictionApproximationNumber_gt_of_lt T n hlt
  have hle := hb (show
    (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n ∈
      finiteRestrictionApproximationNumbers T n from ⟨v, rfl⟩)
  exact (not_le_of_gt hv) hle

/-- Epsilon-form generalized Courant--Fischer characterization. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < (T.approximationNumber n : ℝ) ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
          ∀ x ∈ Submodule.span ℂ (Set.range v),
            s * ‖x‖ ≤ ‖T x‖ := by
  constructor
  · exact exists_linearIndependent_lowerBound_of_lt_approximationNumber T n hr0
  · rintro ⟨s, hrs, v, hv, hV⟩
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    have hsNN : (⟨s, hs0⟩ : NNReal) ≤ T.approximationNumber n := by
      apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
        T n v hv
      intro x hxV hxNorm
      change s ≤ ‖T x‖
      calc
        s = s * ‖x‖ := by rw [hxNorm, mul_one]
        _ ≤ ‖T x‖ := hV x hxV
    have hs : s ≤ (T.approximationNumber n : ℝ) := by
      exact NNReal.coe_le_coe.mpr hsNN
    exact hrs.trans_le hs

end

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
