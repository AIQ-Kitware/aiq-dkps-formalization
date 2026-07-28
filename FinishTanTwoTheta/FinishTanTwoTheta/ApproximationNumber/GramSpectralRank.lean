/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper
import DavisKahan.Interop.Spectra.PVMSubspace
import Spectra.SpectralTheory.Algebra

/-!
# Spectral ranks of Gram cutoffs

This module is the rank-theoretic input for finite spectral-band selection.
For the positive Gram operator `X†X`, approximation-number thresholds control
the dimensions of the upper spectral ranges:

* if `r < a_n(X)`, the closed upper range `[r², ∞)` has rank at least `n+1`;
* if `a_n(X) < r`, the open upper range `(r², ∞)` has rank at most `n`.

The proofs are explicit min--max arguments.  No tactic search, compactness, or
singular-vector attainment is used.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open Set
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory
open TauCeti.DavisKahan.Experimental.SpectraBridge

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The bounded positive Gram operator. -/
def gramOperator (X : E0 →L[ℂ] E1) : E0 →L[ℂ] E0 :=
  X.adjoint ∘L X

/-- The Gram operator is self-adjoint. -/
theorem gramOperator_isSelfAdjoint (X : E0 →L[ℂ] E1) :
    IsSelfAdjoint (gramOperator X) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪X.adjoint (X x), y⟫_ℂ = ⟪x, X.adjoint (X y)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- The Gram quadratic form is the squared image norm. -/
theorem re_inner_gramOperator (X : E0 →L[ℂ] E1) (x : E0) :
    RCLike.re ⟪gramOperator X x, x⟫_ℂ = ‖X x‖ ^ 2 := by
  change RCLike.re ⟪X.adjoint (X x), x⟫_ℂ = ‖X x‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A strict lower threshold for `a_n(X)` forces at least `n+1` dimensions in
`E_{X†X}([r²,∞))`. -/
theorem natCast_succ_le_rank_gramProjection_Ici_of_lt_approximationNumber
    (X : E0 →L[ℂ] E1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < X.approximationNumber n) :
    ((n + 1 : ℕ) : Cardinal) ≤
      (Spectra.QuantumMechanics.SpectralTheory.spectralProjection
        (genToGroup
          (Spectra.Operator.SelfAdjointOperator.ofBounded
            (gramOperator X) (gramOperator_isSelfAdjoint X)).selfAdjoint)
        (Set.Ici (r ^ 2)) measurableSet_Ici).rank := by
  classical
  let C : E0 →L[ℂ] E0 := gramOperator X
  have hC : IsSelfAdjoint C := gramOperator_isSelfAdjoint X
  let A : Spectra.Operator.SelfAdjointOperator E0 :=
    Spectra.Operator.SelfAdjointOperator.ofBounded C hC
  have hA : IsSelfAdjoint A.toLinearPMap := A.selfAdjoint
  let U := genToGroup hA
  let P : E0 →L[ℂ] E0 :=
    Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      U (Set.Ici (r ^ 2)) measurableSet_Ici
  have hgen : generator U = A.toLinearPMap := by
    dsimp only [U]
    exact generator_genToGroup hA
  have hAdom : A.toLinearPMap.domain = ⊤ := by
    dsimp only [A]
    exact Spectra.Operator.SelfAdjointOperator.domain_ofBounded C hC
  have hdom : (generator U).domain = ⊤ := by rw [hgen, hAdom]
  have hgenApply (x : E0) (hx : x ∈ (generator U).domain) :
      generator U ⟨x, hx⟩ = C x := by
    have hxA : x ∈ A.toLinearPMap.domain := by
      rw [hAdom]
      exact Submodule.mem_top
    exact (LinearPMap.ext_iff.mp hgen).2 (x := x) (hf := hx) (hg := hxA)
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    X.exists_linearIndependent_lowerBound_of_lt_approximationNumber n hr0 hr
  let V : Submodule ℂ E0 := Submodule.span ℂ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
  let W : Submodule ℂ E0 := P.range
  let f : V →ₗ[ℂ] W :=
    { toFun := fun x => ⟨P x, ⟨x, rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    let z : E0 := (x : E0) - (y : E0)
    have hzV : z ∈ V := V.sub_mem x.property y.property
    have hPz : P z = 0 := by
      have hval := congrArg Subtype.val hxy
      change P (x : E0) = P (y : E0) at hval
      simpa [z, map_sub] using sub_eq_zero.mpr hval
    have hzDom : z ∈ (generator U).domain := by
      rw [hdom]
      exact Submodule.mem_top
    have henergy := energy_upper_bound_of_spectralProjection_Ici_eq_zero
      U (r ^ 2) (⟨z, hzDom⟩ : (generator U).domain) hPz
    have hupper : ‖X z‖ ^ 2 ≤ r ^ 2 * ‖z‖ ^ 2 := by
      calc
        ‖X z‖ ^ 2 = RCLike.re ⟪C z, z⟫_ℂ := by
          symm
          simpa only [C] using re_inner_gramOperator X z
        _ = RCLike.re ⟪generator U ⟨z, hzDom⟩, z⟫_ℂ := by
          rw [hgenApply z hzDom]
        _ ≤ r ^ 2 * ‖z‖ ^ 2 := henergy
    have hlower : s * ‖z‖ ≤ ‖X z‖ := hV z hzV
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    have hupper' : ‖X z‖ ^ 2 ≤ (r * ‖z‖) ^ 2 := by
      simpa only [mul_pow] using hupper
    have hupperLinear : ‖X z‖ ≤ r * ‖z‖ :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg z))).1 hupper'
    have hz0 : ‖z‖ = 0 := by
      nlinarith [hlower.trans hupperLinear, norm_nonneg z]
    have hz : (x : E0) - (y : E0) = 0 := by
      simpa only [z] using norm_eq_zero.mp hz0
    exact sub_eq_zero.mp hz
  have hfb : LinearIndependent ℂ (f ∘ fun i => b i) := by
    exact b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf_injective)
  have hrankW : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ W :=
    (Module.le_rank_iff).2 ⟨fun i => f (b i), hfb⟩
  change ((n + 1 : ℕ) : Cardinal) ≤ P.rank at hrankW
  simpa only [P, U, A, C] using hrankW

/-- A strict upper threshold for `a_n(X)` forces the open upper Gram range
`E_{X†X}((r²,∞))` to have rank at most `n`. -/
theorem rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt
    (X : E0 →L[ℂ] E1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : X.approximationNumber n < r) :
    (Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      (genToGroup
        (Spectra.Operator.SelfAdjointOperator.ofBounded
          (gramOperator X) (gramOperator_isSelfAdjoint X)).selfAdjoint)
      (Set.Ioi (r ^ 2)) measurableSet_Ioi).rank ≤ (n : Cardinal) := by
  classical
  let C : E0 →L[ℂ] E0 := gramOperator X
  have hC : IsSelfAdjoint C := gramOperator_isSelfAdjoint X
  let A : Spectra.Operator.SelfAdjointOperator E0 :=
    Spectra.Operator.SelfAdjointOperator.ofBounded C hC
  have hA : IsSelfAdjoint A.toLinearPMap := A.selfAdjoint
  let U := genToGroup hA
  let P : E0 →L[ℂ] E0 :=
    Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      U (Set.Ioi (r ^ 2)) measurableSet_Ioi
  have hgen : generator U = A.toLinearPMap := by
    dsimp only [U]
    exact generator_genToGroup hA
  have hAdom : A.toLinearPMap.domain = ⊤ := by
    dsimp only [A]
    exact Spectra.Operator.SelfAdjointOperator.domain_ofBounded C hC
  have hdom : (generator U).domain = ⊤ := by rw [hgen, hAdom]
  have hgenApply (x : E0) (hx : x ∈ (generator U).domain) :
      generator U ⟨x, hx⟩ = C x := by
    have hxA : x ∈ A.toLinearPMap.domain := by
      rw [hAdom]
      exact Submodule.mem_top
    exact (LinearPMap.ext_iff.mp hgen).2 (x := x) (hf := hx) (hg := hxA)
  by_contra hnot
  have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hnot
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ P.range := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨g, hg⟩ := (Module.le_rank_iff).1 hnrank
  let v : Fin (n + 1) → E0 := P.range.subtype ∘ g
  have hv : LinearIndependent ℂ v := by
    exact hg.map' P.range.subtype
      (LinearMap.ker_eq_bot.mpr P.range.injective_subtype)
  have hrle : r ≤ X.approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent X n v hv
    intro x hxspan hxnorm
    have hspan_le : Submodule.span ℂ (Set.range v) ≤ P.range := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      exact (g i).property
    have hxP : x ∈ P.range := hspan_le hxspan
    have hPx : P x = x := by
      rcases hxP with ⟨y, rfl⟩
      change
        (spectralPVM hA).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi
            ((spectralPVM hA).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi y) =
          (spectralPVM hA).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi y
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : E0 →L[ℂ] E0 => T y)
          ((spectralPVM hA).proj_idem (Set.Ioi (r ^ 2)) measurableSet_Ioi)
    have hzlow :
        Spectra.QuantumMechanics.SpectralTheory.spectralProjection
          U (Set.Iic (r ^ 2)) measurableSet_Iic x = 0 := by
      calc
        Spectra.QuantumMechanics.SpectralTheory.spectralProjection
              U (Set.Iic (r ^ 2)) measurableSet_Iic x =
            Spectra.QuantumMechanics.SpectralTheory.spectralProjection
              U (Set.Iic (r ^ 2)) measurableSet_Iic (P x) := by rw [hPx]
        _ = 0 := by
          change
            (Spectra.QuantumMechanics.SpectralTheory.spectralProjection
              U (Set.Iic (r ^ 2)) measurableSet_Iic * P) x = 0
          have hinter : Set.Iic (r ^ 2) ∩ Set.Ioi (r ^ 2) = ∅ := by
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
              Set.mem_empty_iff_false, iff_false]
            exact fun ht => (not_lt_of_ge ht.1) ht.2
          rw [spectralProjection_inter U,
            spectralProjection_congr U hinter
              (measurableSet_Iic.inter measurableSet_Ioi) MeasurableSet.empty,
            spectralProjection_empty U, zero_apply]
    have hxDom : x ∈ (generator U).domain := by
      rw [hdom]
      exact Submodule.mem_top
    have henergy := energy_lower_bound_of_spectralProjection_Iic_eq_zero
      U (r ^ 2) (⟨x, hxDom⟩ : (generator U).domain) hzlow
    have hlowerSq : r ^ 2 * ‖x‖ ^ 2 ≤ ‖X x‖ ^ 2 := by
      calc
        r ^ 2 * ‖x‖ ^ 2 ≤
            RCLike.re ⟪generator U ⟨x, hxDom⟩, x⟫_ℂ := henergy
        _ = RCLike.re ⟪C x, x⟫_ℂ := by rw [hgenApply x hxDom]
        _ = ‖X x‖ ^ 2 := by simpa only [C] using re_inner_gramOperator X x
    have hlowerSq' : (r * ‖x‖) ^ 2 ≤ ‖X x‖ ^ 2 := by
      simpa only [mul_pow] using hlowerSq
    have : r * ‖x‖ ≤ ‖X x‖ :=
      (sq_le_sq₀ (mul_nonneg hr0 (norm_nonneg x)) (norm_nonneg _)).1 hlowerSq'
    simpa only [hxnorm, mul_one] using this
  exact (not_le_of_gt hr) hrle

end

end FinishTanTwoTheta
end TauCeti
