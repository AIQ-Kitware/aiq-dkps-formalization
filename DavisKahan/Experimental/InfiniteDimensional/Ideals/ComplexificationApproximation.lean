/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.ClosedOperatorComplexification
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbers

/-!
# Approximation-number transport through real complexification

A bounded real operator and its coordinatewise complexification have the same
approximation singular values.  The upper inequality complexifies finite-rank
approximants.  The lower inequality uses the real finite-dimensional min--max
witness and complexifies its linearly independent family without changing its
cardinality or lower modulus.

Consequently every finite Ky Fan gauge is preserved exactly.  This is the
scalar bridge needed to apply a complex Sylvester theorem at each finite Ky Fan
gauge and descend the resulting majorization through an arbitrary real
unitarily invariant ideal family.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace ComplexificationApproximation

open scoped InnerProductSpace
open Foundation
open Foundation.RealComplexification

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The range of a complexified operator is the complexification of its real
range. -/
theorem range_complexify
    (T : E →L[ℝ] F) :
    LinearMap.range (RealComplexification.complexify T).toLinearMap =
      complexifySubmodule (LinearMap.range T.toLinearMap) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [mem_complexifySubmodule]
    exact ⟨⟨re w, rfl⟩, ⟨im w, rfl⟩⟩
  · intro hz
    rw [mem_complexifySubmodule] at hz
    rcases hz with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨mk x y, ?_⟩
    apply RealComplexification.ext
    · simpa using hx.symm
    · simpa using hy.symm

/-- A basis of a real space gives a complex basis of its concrete
complexification by embedding every basis vector in the real copy. -/
noncomputable def complexificationBasis
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) :
    Module.Basis ι ℂ (RealComplexification V) := by
  classical
  refine Module.Basis.mk (v := fun i => ofReal (b i)) ?_ ?_
  · rw [linearIndependent_iff]
    intro l s hs i hi
    have hre := congrArg re hs
    have him := congrArg im hs
    have hre' : ∑ j ∈ s, (l j).re • b j = 0 := by
      simpa [map_sum] using hre
    have him' : ∑ j ∈ s, (l j).im • b j = 0 := by
      simpa [map_sum] using him
    have hr := (linearIndependent_iff.mp b.linearIndependent)
      (fun j => (l j).re) s hre' i hi
    have hii := (linearIndependent_iff.mp b.linearIndependent)
      (fun j => (l j).im) s him' i hi
    apply Complex.ext <;> assumption
  · rw [eq_top_iff]
    intro z
    have realCopy_mem (x : V) :
        ofReal x ∈ Submodule.span ℂ (Set.range fun i => ofReal (b i)) := by
      have hx : x ∈ Submodule.span ℝ (Set.range b) := by
        rw [b.span_eq]
        exact Submodule.mem_top
      refine Submodule.span_induction hx ?_ ?_ ?_ ?_
      · rintro y ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, rfl⟩
      · simpa using (Submodule.zero_mem
          (Submodule.span ℂ (Set.range fun i => ofReal (b i))))
      · intro x y hx hy
        simpa using Submodule.add_mem _ hx hy
      · intro r x hx
        have := Submodule.smul_mem
          (Submodule.span ℂ (Set.range fun i => ofReal (b i))) (r : ℂ) hx
        simpa using this
    have hz : z = ofReal (re z) + Complex.I • ofReal (im z) := by
      apply RealComplexification.ext <;> simp
    rw [hz]
    exact Submodule.add_mem _ (realCopy_mem (re z))
      (Submodule.smul_mem _ Complex.I (realCopy_mem (im z)))

/-- Complexification does not change module dimension. -/
theorem rank_complexification
    {V : Type v} [AddCommGroup V] [Module ℝ V] :
    Module.rank ℂ (RealComplexification V) = Module.rank ℝ V := by
  classical
  let b := Module.Free.chooseBasis ℝ V
  calc
    Module.rank ℂ (RealComplexification V) =
        Cardinal.mk (Module.Free.ChooseBasisIndex ℝ V) :=
      (complexificationBasis b).mk_eq_rank.symm
    _ = Module.rank ℝ V := b.mk_eq_rank

/-- Complexifying a real submodule preserves its dimension. -/
theorem rank_complexifySubmodule
    (U : Submodule ℝ E) :
    Module.rank ℂ (complexifySubmodule U) = Module.rank ℝ U := by
  let e : RealComplexification U ≃ₗ[ℂ] complexifySubmodule U :=
    { toFun := fun z =>
        ⟨mk ((re z : U) : E) ((im z : U) : E), by
          rw [mem_complexifySubmodule]
          exact ⟨(re z : U).property, (im z : U).property⟩⟩
      invFun := fun z => mk
        ⟨re (z : RealComplexification E),
          (mem_complexifySubmodule.mp z.property).1⟩
        ⟨im (z : RealComplexification E),
          (mem_complexifySubmodule.mp z.property).2⟩
      left_inv := fun z => by apply RealComplexification.ext <;> rfl
      right_inv := fun z => by apply Subtype.ext; apply RealComplexification.ext <;> rfl
      map_add' := fun z w => by apply Subtype.ext; apply RealComplexification.ext <;> simp
      map_smul' := fun c z => by apply Subtype.ext; apply RealComplexification.ext <;> simp }
  calc
    Module.rank ℂ (complexifySubmodule U) =
        Module.rank ℂ (RealComplexification U) := e.rank_eq.symm
    _ = Module.rank ℝ U := rank_complexification

/-- Complexification preserves the rank of a bounded operator. -/
theorem rank_complexify
    (T : E →L[ℝ] F) :
    (RealComplexification.complexify T).rank = T.rank := by
  change Module.rank ℂ (LinearMap.range
      (RealComplexification.complexify T).toLinearMap) =
    Module.rank ℝ (LinearMap.range T.toLinearMap)
  rw [range_complexify, rank_complexifySubmodule]

/-- A real linearly independent family remains complex linearly independent in
the real copy of the complexification. -/
theorem linearIndependent_ofReal
    {ι : Type*} {v : ι → E} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun i => ofReal (v i)) := by
  rw [linearIndependent_iff]
  intro l s hs i hi
  have hre := congrArg re hs
  have him := congrArg im hs
  have hre' : ∑ j ∈ s, (l j).re • v j = 0 := by
    simpa [map_sum] using hre
  have him' : ∑ j ∈ s, (l j).im • v j = 0 := by
    simpa [map_sum] using him
  have hr := (linearIndependent_iff.mp hv)
    (fun j => (l j).re) s hre' i hi
  have hii := (linearIndependent_iff.mp hv)
    (fun j => (l j).im) s him' i hi
  apply Complex.ext <;> assumption

/-- The complex span of real copies has real and imaginary coordinates in the
corresponding real span. -/
theorem coordinates_mem_real_span
    {ι : Type*} [Fintype ι] (v : ι → E)
    {z : RealComplexification E}
    (hz : z ∈ Submodule.span ℂ (Set.range fun i => ofReal (v i))) :
    re z ∈ Submodule.span ℝ (Set.range v) ∧
      im z ∈ Submodule.span ℝ (Set.range v) := by
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, by simp⟩
  · exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  · rintro x y hx hy
    exact ⟨Submodule.add_mem _ hx.1 hy.1,
      Submodule.add_mem _ hx.2 hy.2⟩
  · rintro c z hz
    exact ⟨
      Submodule.sub_mem _
        (Submodule.smul_mem _ c.re hz.1)
        (Submodule.smul_mem _ c.im hz.2),
      Submodule.add_mem _
        (Submodule.smul_mem _ c.im hz.1)
        (Submodule.smul_mem _ c.re hz.2)⟩

/-- A real lower modulus on a real span becomes the same complex lower modulus
on the complex span. -/
theorem lowerBound_complex_span
    {ι : Type*} [Fintype ι]
    (T : E →L[ℝ] F) (v : ι → E) {s : ℝ} (hs : 0 ≤ s)
    (hV : ∀ x ∈ Submodule.span ℝ (Set.range v),
      s * ‖x‖ ≤ ‖T x‖) :
    ∀ z ∈ Submodule.span ℂ (Set.range fun i => ofReal (v i)),
      s * ‖z‖ ≤ ‖RealComplexification.complexify T z‖ := by
  intro z hz
  have hcoord := coordinates_mem_real_span v hz
  have hr := hV (re z) hcoord.1
  have hi := hV (im z) hcoord.2
  rw [← sq_le_sq₀ (mul_nonneg hs (norm_nonneg _)) (norm_nonneg _)]
  rw [RealComplexification.norm_sq, mul_pow,
    RealComplexification.norm_sq]
  have hrsq : s ^ 2 * ‖re z‖ ^ 2 ≤ ‖T (re z)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖T (re z)‖ - s * ‖re z‖)]
  have hisq : s ^ 2 * ‖im z‖ ^ 2 ≤ ‖T (im z)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖T (im z)‖ - s * ‖im z‖)]
  change s ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2) ≤
    ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2
  nlinarith

/-- Complexification cannot increase an approximation number: complexify a
near-optimal real approximant and preserve both its rank and error norm. -/
theorem approximationNumber_complexify_le
    (T : E →L[ℝ] F) (n : ℕ) :
    (RealComplexification.complexify T).approximationNumber n ≤
      T.approximationNumber n := by
  rw [T.approximationNumber_def]
  apply le_ciInf
  rintro ⟨R, hR⟩
  have hRc : (RealComplexification.complexify R).rank ≤ (n : Cardinal) := by
    rw [rank_complexify]
    exact hR
  calc
    (RealComplexification.complexify T).approximationNumber n ≤
        ‖RealComplexification.complexify T -
          RealComplexification.complexify R‖₊ :=
      (RealComplexification.complexify T).approximationNumber_le hRc
    _ = ‖T - R‖₊ := by
      apply NNReal.eq
      change ‖RealComplexification.complexify T -
        RealComplexification.complexify R‖ = ‖T - R‖
      rw [← RealComplexification.complexify_sub,
        RealComplexification.norm_complexify]

/-- The real approximation number cannot exceed the complexified one.  A strict
real lower threshold supplies an `(n+1)`-vector min--max witness, and that
witness complexifies with the same lower modulus. -/
theorem approximationNumber_le_complexify
    (T : E →L[ℝ] F) (n : ℕ) :
    T.approximationNumber n ≤
      (RealComplexification.complexify T).approximationNumber n := by
  apply le_of_forall_lt
  intro r hr
  have hrReal : (r : ℝ) < (T.approximationNumber n : ℝ) := by
    exact_mod_cast hr
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    ApproximationNumbersReal.exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
      T n (NNReal.coe_nonneg r) hrReal
  have hs0 : 0 ≤ s := (NNReal.coe_nonneg r).trans hrs.le
  have hvC : LinearIndependent ℂ (fun i => ofReal (v i)) :=
    linearIndependent_ofReal hv
  have hlower := lowerBound_complex_span T v hs0 hV
  have hsNN : (⟨s, hs0⟩ : NNReal) ≤
      (RealComplexification.complexify T).approximationNumber n := by
    apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
      (RealComplexification.complexify T) n (fun i => ofReal (v i)) hvC
    intro z hz hnorm
    change s ≤ ‖RealComplexification.complexify T z‖
    calc
      s = s * ‖z‖ := by rw [hnorm, mul_one]
      _ ≤ ‖RealComplexification.complexify T z‖ := hlower z hz
  have hrsNN : r < (⟨s, hs0⟩ : NNReal) := by
    exact_mod_cast hrs
  exact hrsNN.trans_le hsNN

/-- Approximation numbers are exactly preserved by real complexification. -/
theorem approximationNumber_complexify
    (T : E →L[ℝ] F) (n : ℕ) :
    (RealComplexification.complexify T).approximationNumber n =
      T.approximationNumber n :=
  le_antisymm (approximationNumber_complexify_le T n)
    (approximationNumber_le_complexify T n)

/-- Approximation singular values are exactly preserved by real
complexification. -/
theorem approximationSingularValue_complexify
    (T : E →L[ℝ] F) (n : ℕ) :
    approximationSingularValue n (RealComplexification.complexify T) =
      approximationSingularValue n T := by
  exact congrArg (fun x : NNReal => (x : ℝ))
    (approximationNumber_complexify T n)

/-- Every finite Ky Fan approximation gauge is exactly preserved by real
complexification. -/
theorem kyFanApproximationGauge_complexify
    (T : E →L[ℝ] F) (k : ℕ) :
    kyFanApproximationGauge k (RealComplexification.complexify T) =
      kyFanApproximationGauge k T := by
  unfold kyFanApproximationGauge
  apply Finset.sum_congr rfl
  intro n hn
  exact approximationSingularValue_complexify T n

end

end ComplexificationApproximation
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
