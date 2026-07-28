/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Domain-aware infrastructure for partial linear maps

Reusable algebra for unbounded operators represented canonically by Mathlib's
`LinearPMap`: domain transport, extension, symmetry, graph norms, relative
bounds, and elementary real resolvent predicates.

The declarations deliberately take raw partial maps.  Closedness, dense domain,
and self-adjointness are separate hypotheses supplied by the theorem that needs
them; they are not bundled into a parallel operator structure.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean`.
* Extraction class: **representation migration**.  The original declarations
  were methods of a bundled `ClosedOperator`; this module restates their
  reusable content directly over Mathlib `LinearPMap`.
* Spectra influence: none.  This module imports only Mathlib.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Two partial linear maps have the same operator domain. -/
def SameDomain (A B : E →ₗ.[𝕜] E) : Prop :=
  A.domain = B.domain

/-- Equality of partial-map domains is reflexive. -/
@[refl] theorem SameDomain.refl (A : E →ₗ.[𝕜] E) : SameDomain A A := rfl

/-- Equality of partial-map domains is symmetric. -/
@[symm] theorem SameDomain.symm {A B : E →ₗ.[𝕜] E}
    (h : SameDomain A B) : SameDomain B A :=
  Eq.symm h

/-- Equality of partial-map domains is transitive. -/
@[trans] theorem SameDomain.trans {A B C : E →ₗ.[𝕜] E}
    (hAB : SameDomain A B) (hBC : SameDomain B C) : SameDomain A C :=
  Eq.trans hAB hBC

/-- A bounded map sends the domain of `B` into the domain of `A`. -/
def MapsDomainTo (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain, X (x : F) ∈ A.domain

/-- The identity bounded map preserves every partial-map domain. -/
theorem MapsDomainTo.id (A : E →ₗ.[𝕜] E) :
    MapsDomainTo A A (ContinuousLinearMap.id 𝕜 E) := by
  intro x
  simpa using x.property

/-- Domain transport composes with bounded maps. -/
theorem MapsDomainTo.comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {C : G →ₗ.[𝕜] G}
    {X : F →L[𝕜] E} {Y : G →L[𝕜] F}
    (hX : MapsDomainTo A B X) (hY : MapsDomainTo B C Y) :
    MapsDomainTo A C (X ∘L Y) := by
  intro z
  exact hX ⟨Y (z : G), hY z⟩

/-- A linear map on a submodule has a bounded extension to the ambient space. -/
structure BoundedExtension (D : Submodule 𝕜 F) (T : D →ₗ[𝕜] E) where
  operator : F →L[𝕜] E
  agrees : ∀ x : D, operator (x : F) = T x

/-- Extension relation for partial linear maps. -/
def Extends (A B : E →ₗ.[𝕜] E) : Prop :=
  ∃ hdom : A.domain ≤ B.domain,
    ∀ x : A.domain, B ⟨(x : E), hdom x.property⟩ = A x

/-- Every partial linear map extends itself. -/
@[refl] theorem Extends.refl (A : E →ₗ.[𝕜] E) : Extends A A := by
  refine ⟨le_rfl, ?_⟩
  intro x
  rfl

/-- Extension of partial linear maps is transitive. -/
@[trans] theorem Extends.trans {A B C : E →ₗ.[𝕜] E}
    (hAB : Extends A B) (hBC : Extends B C) : Extends A C := by
  rcases hAB with ⟨hdomAB, hactAB⟩
  rcases hBC with ⟨hdomBC, hactBC⟩
  refine ⟨hdomAB.trans hdomBC, ?_⟩
  intro x
  calc
    C ⟨(x : E), hdomBC (hdomAB x.property)⟩ =
        B ⟨(x : E), hdomAB x.property⟩ :=
      hactBC ⟨(x : E), hdomAB x.property⟩
    _ = A x := hactAB x

/-- A partial linear map is symmetric on its operator domain. -/
def IsSymmetric (A : E →ₗ.[𝕜] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫_𝕜 = ⟪(x : E), A y⟫_𝕜

/-- Graph norm associated with a partial linear map. -/
noncomputable def graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2)

/-- The graph norm is nonnegative. -/
theorem graphNorm_nonneg (A : E →ₗ.[𝕜] E) (x : A.domain) :
    0 ≤ graphNorm A x :=
  Real.sqrt_nonneg _

/-- Squaring the graph norm recovers its defining sum of squares. -/
theorem graphNorm_sq (A : E →ₗ.[𝕜] E) (x : A.domain) :
    graphNorm A x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
  unfold graphNorm
  exact Real.sq_sqrt (by positivity)

/-- The ambient norm is controlled by the graph norm. -/
theorem norm_coe_le_graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) :
    ‖(x : E)‖ ≤ graphNorm A x := by
  rw [graphNorm]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖A x‖])

/-- The operator-value norm is controlled by the graph norm. -/
theorem norm_apply_le_graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) :
    ‖A x‖ ≤ graphNorm A x := by
  rw [graphNorm]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖(x : E)‖])

/-- Relative boundedness of a domain-defined perturbation with respect to a
partial linear map. -/
def RelativelyBounded (A : E →ₗ.[𝕜] E)
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖

namespace RelativelyBounded

/-- The zero perturbation has zero relative bound. -/
theorem zero (A : E →ₗ.[𝕜] E) :
    RelativelyBounded A (0 : A.domain →ₗ[𝕜] E) 0 0 := by
  intro x
  simp

/-- Relative bounds may be weakened by increasing either coefficient. -/
theorem mono {A : E →ₗ.[𝕜] E}
    {V : A.domain →ₗ[𝕜] E} {a b a' b' : ℝ}
    (hV : RelativelyBounded A V a b)
    (haa' : a ≤ a') (hbb' : b ≤ b') :
    RelativelyBounded A V a' b' := by
  intro x
  exact (hV x).trans <| add_le_add
    (mul_le_mul_of_nonneg_right haa' (norm_nonneg (x : E)))
    (mul_le_mul_of_nonneg_right hbb' (norm_nonneg (A x)))

/-- Relative bounds add under addition of perturbations. -/
theorem add {A : E →ₗ.[𝕜] E}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V + W) (a + c) (b + d) := by
  intro x
  calc
    ‖(V + W) x‖ ≤ ‖V x‖ + ‖W x‖ := norm_add_le _ _
    _ ≤ (a * ‖(x : E)‖ + b * ‖A x‖) +
        (c * ‖(x : E)‖ + d * ‖A x‖) :=
      add_le_add (hV x) (hW x)
    _ = (a + c) * ‖(x : E)‖ + (b + d) * ‖A x‖ := by ring

/-- Relative bounds scale by the norm of the scalar. -/
theorem smul {A : E →ₗ.[𝕜] E}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) (c : 𝕜) :
    RelativelyBounded A (c • V) (‖c‖ * a) (‖c‖ * b) := by
  intro x
  rw [LinearMap.smul_apply, norm_smul]
  calc
    ‖c‖ * ‖V x‖ ≤ ‖c‖ * (a * ‖(x : E)‖ + b * ‖A x‖) :=
      mul_le_mul_of_nonneg_left (hV x) (norm_nonneg c)
    _ = (‖c‖ * a) * ‖(x : E)‖ + (‖c‖ * b) * ‖A x‖ := by ring

/-- Relative bounds are preserved by negation. -/
theorem neg {A : E →ₗ.[𝕜] E}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) :
    RelativelyBounded A (-V) a b := by
  simpa using hV.smul (-1 : 𝕜)

/-- Relative bounds add under subtraction of perturbations. -/
theorem sub {A : E →ₗ.[𝕜] E}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V - W) (a + c) (b + d) := by
  simpa [sub_eq_add_neg] using hV.add hW.neg

/-- Restricting a bounded ambient operator to the domain gives relative bound
`(‖V‖, 0)`. -/
theorem domRestrict (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    RelativelyBounded A (V.toLinearMap.domRestrict A.domain) ‖V‖ 0 := by
  intro x
  simpa using V.le_opNorm (x : E)

end RelativelyBounded

/-- Real resolvent set of a partial linear map.  A parameter belongs to the set
when the shifted map has a bounded two-sided inverse with explicit domain
transport for the right-inverse leg. -/
def realResolventSet (A : E →ₗ.[𝕜] E) : Set ℝ :=
  {lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A ⟨R y, h⟩ - (lam : 𝕜) • R y = y)}

/-- Real spectrum defined as the complement of `realResolventSet`. -/
def realSpectrum (A : E →ₗ.[𝕜] E) : Set ℝ :=
  (realResolventSet A)ᶜ

/-- Spectral-set separation for two partial maps, possibly on different Hilbert
spaces. -/
def SpectralSetsSeparated (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ realSpectrum A, a ∈ s →
    ∀ b ∈ realSpectrum B, b ∈ t → d ≤ |a - b|

/-- Spectral-set separation is symmetric in the two maps. -/
theorem SpectralSetsSeparated.symm
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d) :
    SpectralSetsSeparated B A t s d := by
  intro b hb ht a ha hs
  simpa [abs_sub_comm] using h a ha hs b hb ht

/-- Weakening the required gap preserves spectral-set separation. -/
theorem SpectralSetsSeparated.mono_gap
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d e : ℝ}
    (h : SpectralSetsSeparated A B s t d) (hed : e ≤ d) :
    SpectralSetsSeparated A B s t e := by
  intro a ha hs b hb ht
  exact hed.trans (h a ha hs b hb ht)

/-- Restricting either selected spectral set preserves separation. -/
theorem SpectralSetsSeparated.mono_sets
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s s' t t' : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d)
    (hs : s' ⊆ s) (ht : t' ⊆ t) :
    SpectralSetsSeparated A B s' t' d := by
  intro a ha has' b hb hbt'
  exact h a ha (hs has') b hb (ht hbt')

end LinearPMap
end TauCeti

end
