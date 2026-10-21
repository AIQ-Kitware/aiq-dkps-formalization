/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Carrier

/-!
# Transitional operator-ideal-family API

Tau Ceti owns the family structure, finite-gauge submodule, normed carrier, and
completeness API. This module contains compatibility names used while downstream
consumers migrate to those declarations. The block-sum estimate is a DKPS result.
-/

public section

open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E H : Type v} {F G : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : OperatorIdealFamily.{u, v, w} 𝕜)

/-- Transitional spelling for Tau Ceti's finite-gauge submodule. -/
abbrev carrier : Submodule 𝕜 (E →L[𝕜] F) := (N.operatorGauge E F).finiteSubmodule

@[simp]
theorem mem_carrier_iff {A : E →L[𝕜] F} : A ∈ N.carrier ↔ N.gauge A ≠ ∞ := by
  unfold carrier
  rw [OperatorGauge.mem_finiteSubmodule, OperatorIdealFamily.operatorGauge_apply,
    lt_top_iff_ne_top]

theorem gauge_eq_zero {A : E →L[𝕜] F} (h : N.gauge A = 0) : A = 0 :=
  (N.gauge_eq_zero_iff A).mp h

theorem gauge_sub_le (A B : E →L[𝕜] F) : N.gauge (A - B) ≤ N.gauge A + N.gauge B := by
  simpa [sub_eq_add_neg] using N.gauge_add_le A (-B)

theorem gauge_ne_top_of_mem {A : E →L[𝕜] F} (hA : A ∈ N.carrier) :
    N.gauge A ≠ ∞ := (mem_carrier_iff (N := N)).mp hA

theorem gauge_lt_top_of_mem {A : E →L[𝕜] F} (hA : A ∈ N.carrier) :
    N.gauge A < ∞ := lt_top_iff_ne_top.mpr (gauge_ne_top_of_mem N hA)

theorem comp_mem_carrier (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E)
    (hA : A ∈ N.carrier) : L ∘L A ∘L R ∈ N.carrier := by
  rw [mem_carrier_iff] at hA ⊢
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top hA) enorm_ne_top)
    (N.gauge_comp_le L A R)

theorem sum_mem_carrier {ι : Type*} (s : Finset ι) {A : ι → E →L[𝕜] F}
    (hA : ∀ i ∈ s, A i ∈ N.carrier) : (∑ i ∈ s, A i) ∈ N.carrier :=
  Submodule.sum_mem _ hA

/-- A DKPS block-sum estimate for contractive factors. -/
theorem gauge_blockSum_le {T : E →L[𝕜] F} {P₁ P₂ : E →L[𝕜] E} {Q₁ Q₂ : F →L[𝕜] F}
    (hP₁ : ‖P₁‖ ≤ 1) (hP₂ : ‖P₂‖ ≤ 1) (hQ₁ : ‖Q₁‖ ≤ 1) (hQ₂ : ‖Q₂‖ ≤ 1)
    (hsplit : Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂ = T) :
    max (N.gauge (Q₁ ∘L T ∘L P₁)) (N.gauge (Q₂ ∘L T ∘L P₂)) ≤ N.gauge T ∧
      N.gauge T ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := by
  have hcomp (Q : F →L[𝕜] F) (P : E →L[𝕜] E) (hQ : ‖Q‖ ≤ 1) (hP : ‖P‖ ≤ 1) :
      N.gauge (Q ∘L T ∘L P) ≤ N.gauge T := by
    refine (N.gauge_comp_le Q T P).trans ?_
    have hQ' : ‖Q‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hQ
    have hP' : ‖P‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hP
    calc ‖Q‖ₑ * N.gauge T * ‖P‖ₑ ≤ 1 * N.gauge T * 1 := by gcongr
      _ = N.gauge T := by simp
  refine ⟨max_le (hcomp Q₁ P₁ hQ₁ hP₁) (hcomp Q₂ P₂ hQ₂ hP₂), ?_⟩
  calc N.gauge T = N.gauge (Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂) := by rw [hsplit]
    _ ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := N.gauge_add_le _ _

/-- Transitional type name for Tau Ceti's normed gauge carrier. -/
abbrev Elem (N : OperatorIdealFamily.{u, v, w} 𝕜) (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :=
  (N.operatorGauge E F).Carrier

namespace Elem

variable {N}

abbrev val (A : N.Elem E F) : E →L[𝕜] F := A.toContinuousLinearMap

theorem val_mem (A : N.Elem E F) : A.val ∈ N.carrier := A.mem_finiteSubmodule

theorem gauge_val_ne_top (A : N.Elem E F) : N.gauge A.val ≠ ∞ :=
  gauge_ne_top_of_mem N A.val_mem

def mk {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.Elem E F := by
  apply OperatorGauge.Carrier.mk A
  apply OperatorGauge.mem_finiteSubmodule.mpr
  rw [OperatorIdealFamily.operatorGauge_apply, lt_top_iff_ne_top]
  exact gauge_ne_top_of_mem N hA

@[simp] theorem val_mk {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : (mk hA).val = A := by
  simp [mk, val]

@[ext] theorem ext {A B : N.Elem E F} (h : A.val = B.val) : A = B :=
  OperatorGauge.Carrier.ext h

@[simp] theorem mk_val (A : N.Elem E F) : mk A.val_mem = A := ext rfl

@[simp] theorem val_zero : (0 : N.Elem E F).val = 0 :=
  OperatorGauge.Carrier.toContinuousLinearMap_zero

@[simp] theorem val_add (A B : N.Elem E F) : (A + B).val = A.val + B.val :=
  OperatorGauge.Carrier.toContinuousLinearMap_add A B

@[simp] theorem val_neg (A : N.Elem E F) : (-A).val = -A.val :=
  OperatorGauge.Carrier.toContinuousLinearMap_neg A

@[simp] theorem val_sub (A B : N.Elem E F) : (A - B).val = A.val - B.val :=
  OperatorGauge.Carrier.toContinuousLinearMap_sub A B

@[simp] theorem val_smul (c : 𝕜) (A : N.Elem E F) : (c • A).val = c • A.val :=
  OperatorGauge.Carrier.toContinuousLinearMap_smul c A

theorem norm_def (A : N.Elem E F) : ‖A‖ = (N.gauge A.val).toReal := by
  calc
    ‖A‖ = ((N.operatorGauge E F) A.toContinuousLinearMap).toReal :=
      OperatorGauge.Carrier.norm_def A
    _ = (N.gauge A.val).toReal := by rw [OperatorIdealFamily.operatorGauge_apply, Elem.val]

theorem enorm_eq_gauge (A : N.Elem E F) : ‖A‖ₑ = N.gauge A.val := by
  calc
    ‖A‖ₑ = (N.operatorGauge E F) A.toContinuousLinearMap :=
      OperatorGauge.Carrier.enorm_eq_gauge A
    _ = N.gauge A.val := by rw [OperatorIdealFamily.operatorGauge_apply, Elem.val]

theorem norm_val_le (A : N.Elem E F) : ‖A.val‖ ≤ ‖A‖ :=
  OperatorGauge.Carrier.norm_toContinuousLinearMap_le A

theorem cauchySeq_val {a : ℕ → N.Elem E F} (ha : CauchySeq a) :
    CauchySeq fun n => (a n).val := by
  rw [Metric.cauchySeq_iff] at ha ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := ha ε hε
  refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (hM m hm n hn)⟩
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_val_le (a m - a n)

end Elem

end OperatorIdealFamily

namespace OperatorGauge.Carrier

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {g : OperatorGauge 𝕜 E F}

/-- Temporary spelling retained for downstream DKPS consumers. -/
abbrev val (A : g.Carrier) : E →L[𝕜] F := A.toContinuousLinearMap

omit [CompleteSpace E] [CompleteSpace F] in
theorem gauge_val_ne_top (A : g.Carrier) : g A.toContinuousLinearMap ≠ ∞ :=
  ne_of_lt (OperatorGauge.Carrier.gauge_lt_top A)

end OperatorGauge.Carrier

namespace SymmetricOperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜] {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Adjoint closure translated to the upstream finite-gauge submodule. -/
theorem adjoint_mem_carrier (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : E →L[𝕜] F} (hA : A ∈ N.toOperatorIdealFamily.carrier) :
    A.adjoint ∈ N.toOperatorIdealFamily.carrier := by
  apply (OperatorIdealFamily.mem_carrier_iff (N := N.toOperatorIdealFamily)).2
  rw [N.gauge_adjoint A]
  exact (OperatorIdealFamily.mem_carrier_iff (N := N.toOperatorIdealFamily)).1 hA

end SymmetricOperatorIdealFamily

end TauCeti
