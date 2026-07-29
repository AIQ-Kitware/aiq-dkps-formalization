import Mathlib

/-!
# Approximation numbers and Hilbert-space singular values: suggested signatures

The roadmap prose is authoritative.  This file records representative target
shapes using names already present in the staged `ForTauCeti` implementation.
Unnamed examples are the genuinely missing targets.
-/

namespace TauCetiRoadmap.ApproximationNumbers

open Module (finrank)
open scoped InnerProductSpace
open Filter Topology

universe u v w x y

/-! ## Part A -- approximation numbers on normed spaces -/

section ApproximationNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type y} [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖

theorem approximationNumber_eq_iInf (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n =
      ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖ :=
  rfl

theorem approximationNumber_le_norm_sub
    (T : E →L[𝕜] F) {R : E →L[𝕜] F} {n : ℕ}
    (hR : R.rank ≤ (n : Cardinal)) :
    approximationNumber T n ≤ ‖T - R‖ := by
  sorry

theorem le_approximationNumber_iff
    (T : E →L[𝕜] F) {n : ℕ} {c : ℝ} :
    c ≤ approximationNumber T n ↔
      ∀ R : E →L[𝕜] F, R.rank ≤ (n : Cardinal) → c ≤ ‖T - R‖ := by
  sorry

@[simp] theorem approximationNumber_index_zero (T : E →L[𝕜] F) :
    approximationNumber T 0 = ‖T‖ := by
  sorry

theorem approximationNumber_antitone (T : E →L[𝕜] F) :
    Antitone (approximationNumber T) := by
  sorry

theorem exists_rank_le_norm_sub_lt_approximationNumber_add
    (T : E →L[𝕜] F) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F,
      R.rank ≤ (n : Cardinal) ∧ ‖T - R‖ < approximationNumber T n + ε := by
  sorry

theorem approximationNumber_add_le
    (T S : E →L[𝕜] F) (m n : ℕ) :
    approximationNumber (T + S) (m + n) ≤
      approximationNumber T m + approximationNumber S n := by
  sorry

theorem abs_approximationNumber_sub_approximationNumber_le
    (T S : E →L[𝕜] F) (n : ℕ) :
    |approximationNumber T n - approximationNumber S n| ≤ ‖T - S‖ := by
  sorry

theorem approximationNumber_comp_comp_le
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) (n : ℕ) :
    approximationNumber (L ∘L T ∘L R) n ≤
      ‖L‖ * approximationNumber T n * ‖R‖ := by
  sorry

@[simp] theorem approximationNumber_smul
    (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (c • T) n = ‖c‖ * approximationNumber T n := by
  sorry

/-- A4: finite-rank cutoff. -/
example (T : E →L[𝕜] F) {n : ℕ} (hT : T.rank ≤ (n : Cardinal)) :
    approximationNumber T n = 0 := by
  sorry

/-- A4: decay exactly characterizes finite-rank norm approximability. -/
example (T : E →L[𝕜] F) :
    Tendsto (approximationNumber T) atTop (𝓝 0) ↔
      ∃ R : ℕ → E →L[𝕜] F,
        (∀ n, (R n).rank < Cardinal.aleph0) ∧ Tendsto R atTop (𝓝 T) := by
  sorry

end ApproximationNumbers

section Compactness

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- A4: finite-rank approximability implies compactness. -/
example (T : E →L[𝕜] F)
    (hT : Tendsto (approximationNumber T) atTop (𝓝 0)) :
    IsCompactOperator T := by
  sorry

end Compactness

/-! ## Part B -- Hilbert-space singular-value theory -/

section Adjoint

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

@[simp] theorem approximationNumber_adjoint (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T.adjoint n = approximationNumber T n := by
  sorry

/-- A4: compact Hilbert-space operators have approximation numbers tending to zero. -/
example (T : E →L[𝕜] F) (hT : IsCompactOperator T) :
    Tendsto (approximationNumber T) atTop (𝓝 0) := by
  sorry

end Adjoint

section ComplexModulus

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable def modulus (T : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

theorem norm_modulus_apply (T : E →L[ℂ] F) (x : E) :
    ‖modulus T x‖ = ‖T x‖ := by
  sorry

def HasSameApproximationNumbers
    {E₁ F₁ E₂ F₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (A : E₁ →L[ℂ] F₁) (B : E₂ →L[ℂ] F₂) : Prop :=
  ∀ n, approximationNumber A n = approximationNumber B n

theorem modulus_hasSameApproximationNumbers (T : E →L[ℂ] F) :
    HasSameApproximationNumbers (modulus T) T := by
  sorry

end ComplexModulus

section FiniteDimensional

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

theorem approximationNumber_eq_singularValues
    (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n = T.toLinearMap.singularValues n := by
  sorry

/-- B4: finite-dimensional orthogonal-tail formula. -/
example (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n =
      ⨅ V : {V : Submodule 𝕜 E // finrank 𝕜 V ≤ n},
        ‖T ∘L ((V.1)ᗮ).starProjection‖ := by
  sorry

end FiniteDimensional

section MinMax

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem le_approximationNumber_of_lt_rank
    (T : E →L[𝕜] F) (n : ℕ) (V : Submodule 𝕜 E) {c : ℝ}
    (hVrank : (n : Cardinal) < Module.rank 𝕜 V)
    (hV : ∀ x : V, c * ‖(x : E)‖ ≤ ‖T (x : E)‖) :
    c ≤ approximationNumber T n := by
  sorry

end MinMax

section ComplexMinMaxConverse

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < approximationNumber T n) :
    ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
      ∀ x ∈ Submodule.span ℂ (Set.range v), s * ‖x‖ ≤ ‖T x‖ := by
  sorry

def finiteRestrictionApproximationNumbers (T : E →L[ℂ] F) (n : ℕ) : Set ℝ :=
  Set.range fun v : Fin (n + 1) → E =>
    approximationNumber (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL) n

theorem approximationNumber_isLUB_finiteRestrictions
    (T : E →L[ℂ] F) (n : ℕ) :
    IsLUB (finiteRestrictionApproximationNumbers T n) (approximationNumber T n) := by
  sorry

end ComplexMinMaxConverse

end TauCetiRoadmap.ApproximationNumbers
