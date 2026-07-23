/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Banach spaces carried by rectangular symmetric ideals

A `RectangularSymmetricIdealFamily` already contains exactly the analytic data
needed to regard its members as a Banach space in the ideal gauge.  This file
packages that observation once and for all.

The resulting type has three uses.

* Its norm is the family gauge, not the ambient operator norm.
* The forgetful map to bounded operators is contractive.
* Bochner integration in the ideal norm automatically produces an ideal member,
  and forgetting the integral agrees with integrating the underlying operators.

The construction is completely generic.  Once the rectangular Hilbert--Schmidt,
trace, or Schatten family has been supplied, no additional completeness or
integration argument is needed for that family.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace Scratch
namespace IdealBanach

open scoped InnerProductSpace
open Filter Topology MeasureTheory

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The linear subspace of members of a rectangular symmetric ideal. -/
noncomputable def idealSubmodule
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜)) :
    Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | N.Mem A}
  zero_mem' := N.zero_mem
  add_mem' := fun hA hB => N.add_mem hA hB
  smul_mem' := fun c A hA => N.smul_mem c hA

/-- A member of a rectangular symmetric ideal, bundled with the ideal gauge as
its norm.  This is a fresh type synonym so it does not inherit the ambient
operator norm from the submodule subtype. -/
def IdealOperator
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜)) : Type _ :=
  ↥(idealSubmodule (E := E) (F := F) N)

namespace IdealOperator

variable (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))

instance instAddCommGroup : AddCommGroup (IdealOperator (E := E) (F := F) N) :=
  inferInstanceAs (AddCommGroup ↥(idealSubmodule (E := E) (F := F) N))

instance instModule : Module 𝕜 (IdealOperator (E := E) (F := F) N) :=
  inferInstanceAs (Module 𝕜 ↥(idealSubmodule (E := E) (F := F) N))

/-- Forget the ideal membership witness. -/
def toOp (A : IdealOperator (E := E) (F := F) N) : E →L[𝕜] F :=
  (A : ↥(idealSubmodule (E := E) (F := F) N)).1

/-- The underlying operator belongs to the ideal. -/
theorem mem (A : IdealOperator (E := E) (F := F) N) : N.Mem A.toOp :=
  (A : ↥(idealSubmodule (E := E) (F := F) N)).2

@[simp] theorem toOp_zero :
    (0 : IdealOperator (E := E) (F := F) N).toOp = 0 := rfl

@[simp] theorem toOp_add
    (A B : IdealOperator (E := E) (F := F) N) :
    (A + B).toOp = A.toOp + B.toOp := rfl

@[simp] theorem toOp_smul
    (c : 𝕜) (A : IdealOperator (E := E) (F := F) N) :
    (c • A).toOp = c • A.toOp := rfl

@[simp] theorem toOp_neg
    (A : IdealOperator (E := E) (F := F) N) :
    (-A).toOp = -A.toOp := rfl

@[simp] theorem toOp_sub
    (A B : IdealOperator (E := E) (F := F) N) :
    (A - B).toOp = A.toOp - B.toOp := rfl

@[simp] theorem toOp_mk
    (A : E →L[𝕜] F) (hA : N.Mem A) :
    (show IdealOperator (E := E) (F := F) N from ⟨A, hA⟩).toOp = A := rfl

/-- Ideal members are equal when their underlying bounded operators agree. -/
@[ext] theorem ext
    {A B : IdealOperator (E := E) (F := F) N}
    (h : A.toOp = B.toOp) : A = B :=
  show (A : ↥(idealSubmodule (E := E) (F := F) N)) =
      (B : ↥(idealSubmodule (E := E) (F := F) N)) from Subtype.ext h

/-- The ideal gauge is the norm on bundled ideal operators. -/
noncomputable instance instNorm :
    Norm (IdealOperator (E := E) (F := F) N) :=
  ⟨fun A => N.gauge A.toOp⟩

@[simp] theorem norm_def
    (A : IdealOperator (E := E) (F := F) N) :
    ‖A‖ = N.gauge A.toOp := rfl

/-- Norm laws supplied directly by the rectangular ideal fields. -/
theorem core : NormedSpace.Core 𝕜 (IdealOperator (E := E) (F := F) N) where
  norm_nonneg A := N.gauge_nonneg A.mem
  norm_smul c A := by
    change N.gauge (c • A.toOp) = ‖c‖ * N.gauge A.toOp
    exact N.gauge_smul c A.mem
  norm_triangle A B := by
    change N.gauge (A.toOp + B.toOp) ≤ N.gauge A.toOp + N.gauge B.toOp
    exact N.gauge_add_le A.mem B.mem
  norm_eq_zero_iff A := by
    change N.gauge A.toOp = 0 ↔ A = 0
    constructor
    · intro hzero
      apply IdealOperator.ext N
      exact (N.gauge_eq_zero A.mem hzero).trans toOp_zero.symm
    · intro hzero
      rw [hzero, toOp_zero, N.gauge_zero]

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (IdealOperator (E := E) (F := F) N) :=
  NormedAddCommGroup.ofCore (core (E := E) (F := F) N)

noncomputable instance instNormedSpace :
    NormedSpace 𝕜 (IdealOperator (E := E) (F := F) N) :=
  NormedSpace.ofCore (core (E := E) (F := F) N)

/-- Forgetting to the bounded-operator space is contractive. -/
theorem norm_toOp_le
    (A : IdealOperator (E := E) (F := F) N) :
    ‖A.toOp‖ ≤ ‖A‖ := by
  change ‖A.toOp‖ ≤ N.gauge A.toOp
  exact N.opNorm_le_gauge A.mem

/-- The forgetful linear map from the ideal Banach space to bounded operators. -/
noncomputable def toOpL :
    IdealOperator (E := E) (F := F) N →L[𝕜] (E →L[𝕜] F) := by
  let L : IdealOperator (E := E) (F := F) N →ₗ[𝕜] (E →L[𝕜] F) :=
    { toFun := toOp N
      map_add' := fun A B => toOp_add N A B
      map_smul' := fun c A => toOp_smul N c A }
  exact L.mkContinuous 1 fun A => by
    simpa only [one_mul] using norm_toOp_le N A

@[simp] theorem toOpL_apply
    (A : IdealOperator (E := E) (F := F) N) :
    toOpL (E := E) (F := F) N A = A.toOp := rfl

/-- Left composition by a fixed bounded operator, acting continuously in the
ideal norm. -/
noncomputable def compLeftL
    {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) :
    IdealOperator (E := E) (F := F) N →L[𝕜]
      IdealOperator (E := E) (F := G) N := by
  let M : IdealOperator (E := E) (F := F) N →ₗ[𝕜]
      IdealOperator (E := E) (F := G) N :=
    { toFun := fun A =>
        (⟨L ∘L A.toOp, N.comp_left_mem L A.mem⟩ :
          IdealOperator (E := E) (F := G) N)
      map_add' := by
        intro A B
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.comp_add]
      map_smul' := by
        intro c A
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.comp_smul] }
  exact M.mkContinuous ‖L‖ fun A => by
    change N.gauge (L ∘L A.toOp) ≤ ‖L‖ * N.gauge A.toOp
    exact N.gauge_comp_left_le_mul L A.mem

@[simp] theorem compLeftL_toOp
    {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G)
    (A : IdealOperator (E := E) (F := F) N) :
    (compLeftL N L A).toOp = L ∘L A.toOp := rfl

/-- Right composition by a fixed bounded operator, acting continuously in the
ideal norm. -/
noncomputable def compRightL
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (R : H →L[𝕜] E) :
    IdealOperator (E := E) (F := F) N →L[𝕜]
      IdealOperator (E := H) (F := F) N := by
  let M : IdealOperator (E := E) (F := F) N →ₗ[𝕜]
      IdealOperator (E := H) (F := F) N :=
    { toFun := fun A =>
        (⟨A.toOp ∘L R, N.comp_right_mem R A.mem⟩ :
          IdealOperator (E := H) (F := F) N)
      map_add' := by
        intro A B
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.add_comp]
      map_smul' := by
        intro c A
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.smul_comp] }
  exact M.mkContinuous ‖R‖ fun A => by
    change N.gauge (A.toOp ∘L R) ≤ ‖R‖ * N.gauge A.toOp
    have h := N.gauge_comp_right_le_mul R A.mem
    simpa [mul_comm] using h

@[simp] theorem compRightL_toOp
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (R : H →L[𝕜] E)
    (A : IdealOperator (E := E) (F := F) N) :
    (compRightL N R A).toOp = A.toOp ∘L R := rfl

/-- Two-sided bounded composition as a continuous linear map in the ideal
norm. -/
noncomputable def compBothL
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (R : H →L[𝕜] E) :
    IdealOperator (E := E) (F := F) N →L[𝕜]
      IdealOperator (E := H) (F := G) N := by
  let M : IdealOperator (E := E) (F := F) N →ₗ[𝕜]
      IdealOperator (E := H) (F := G) N :=
    { toFun := fun A =>
        (⟨L ∘L A.toOp ∘L R, N.comp_mem L R A.mem⟩ :
          IdealOperator (E := H) (F := G) N)
      map_add' := by
        intro A B
        apply IdealOperator.ext N
        ext x
        simp only [ContinuousLinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        apply IdealOperator.ext N
        ext x
        simp only [ContinuousLinearMap.comp_apply, map_smul] }
  exact M.mkContinuous (‖L‖ * ‖R‖) fun A => by
    change N.gauge (L ∘L A.toOp ∘L R) ≤
      (‖L‖ * ‖R‖) * N.gauge A.toOp
    calc
      N.gauge (L ∘L A.toOp ∘L R)
          ≤ ‖L‖ * N.gauge A.toOp * ‖R‖ := N.gauge_comp_le L R A.mem
      _ = (‖L‖ * ‖R‖) * N.gauge A.toOp := by ring

@[simp] theorem compBothL_toOp
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (R : H →L[𝕜] E)
    (A : IdealOperator (E := E) (F := F) N) :
    (compBothL N L R A).toOp = L ∘L A.toOp ∘L R := rfl

/-- The ideal gauge completeness field produces an actual `CompleteSpace`
instance on the bundled ideal. -/
noncomputable instance instCompleteSpace :
    CompleteSpace (IdealOperator (E := E) (F := F) N) := by
  refine Metric.complete_of_cauchySeq_tendsto fun A hA => ?_
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n,
      M ≤ m → M ≤ n → N.gauge ((A m).toOp - (A n).toOp) < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.1 hA ε hε
    refine ⟨M, ?_⟩
    intro m n hm hn
    have hdist := hM m hm n hn
    simpa only [dist_eq_norm, norm_def, toOp_sub] using hdist
  obtain ⟨L, hL, hconv⟩ := N.gauge_complete
    (fun n => (A n).toOp) (fun n => (A n).mem) hcauchy
  refine ⟨(⟨L, hL⟩ : IdealOperator (E := E) (F := F) N), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := hconv ε hε
  refine ⟨M, ?_⟩
  intro n hn
  have h := hM n hn
  simpa only [dist_eq_norm, norm_def, toOp_sub, toOp_mk] using h

/-- The forgetful map commutes with Bochner integration in the ideal norm. -/
theorem toOp_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → IdealOperator (E := E) (F := F) N)
    (hf : Integrable f μ) :
    (∫ a, f a ∂μ).toOp = ∫ a, (f a).toOp ∂μ := by
  exact (toOpL (E := E) (F := F) N).integral_comp_comm hf

/-- The Bochner integral of an ideal-valued integrable function is an ideal
member after forgetting to bounded operators. -/
theorem mem_integral_toOp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → IdealOperator (E := E) (F := F) N)
    (hf : Integrable f μ) :
    N.Mem (∫ a, (f a).toOp ∂μ) := by
  rw [← toOp_integral N f hf]
  exact (∫ a, f a ∂μ).mem

/-- The ideal gauge of the underlying integral is bounded by the integral of
pointwise ideal norms. -/
theorem gauge_integral_toOp_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → IdealOperator (E := E) (F := F) N)
    (hf : Integrable f μ) :
    N.gauge (∫ a, (f a).toOp ∂μ) ≤ ∫ a, ‖f a‖ ∂μ := by
  rw [← toOp_integral N f hf]
  change ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ
  exact norm_integral_le_integral_norm f

/-- A pointwise ideal-valued raw operator field can be integrated by bundling
its membership witnesses. -/
theorem mem_integral_of_integrable_lift
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → E →L[𝕜] F)
    (hmem : ∀ a, N.Mem (f a))
    (hlift : Integrable
      (fun a => (⟨f a, hmem a⟩ : IdealOperator (E := E) (F := F) N)) μ) :
    N.Mem (∫ a, f a ∂μ) := by
  simpa using mem_integral_toOp N
    (fun a => (⟨f a, hmem a⟩ : IdealOperator (E := E) (F := F) N)) hlift

/-- Gauge estimate for a raw operator field with an integrable ideal-valued
lift. -/
theorem gauge_integral_of_integrable_lift_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → E →L[𝕜] F)
    (hmem : ∀ a, N.Mem (f a))
    (hlift : Integrable
      (fun a => (⟨f a, hmem a⟩ : IdealOperator (E := E) (F := F) N)) μ) :
    N.gauge (∫ a, f a ∂μ) ≤ ∫ a, N.gauge (f a) ∂μ := by
  simpa only [norm_def] using gauge_integral_toOp_le N
    (fun a => (⟨f a, hmem a⟩ : IdealOperator (E := E) (F := F) N)) hlift

end IdealOperator

end

end IdealBanach
end Scratch
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
