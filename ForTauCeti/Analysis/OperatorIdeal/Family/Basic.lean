/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Operator ideal families

An **operator ideal** in the sense of Pietsch is a rule assigning to every pair
of spaces `E`, `F` a linear subspace of `E →L[𝕜] F` that is stable under
composition with arbitrary bounded maps on either side, together with a norm on
that subspace dominating the operator norm and submultiplicative against outer
compositions.  Because Davis--Kahan compares operators *between different
spaces*, the ideal must be handled as a coherent family across all pairs at
once, not as a norm on a single endomorphism algebra.

The families here range over **Hilbert** spaces, with source and target still in
independent universes.  See "Why Hilbert and not Banach" below: the restriction
is forced by the examples, not by the laws.

## The single-field representation

The family is presented by exactly one datum, an extended-real-valued **gauge**

```
gauge : (E →L[𝕜] F) → ℝ≥0∞
```

defined on *all* operators, with the ideal recovered as its finiteness domain
`OperatorIdealFamily.carrier`.  This is the classical presentation of a symmetric
norming function (Gohberg--Krein): an operator lies in the ideal exactly when its
ideal norm is finite.  Three things follow.

* **Extensionality is structural.**  Two families with the same gauge are equal
  (`OperatorIdealFamily.ext`), because the gauge is the only field.  A
  representation carrying membership and a gauge as *independent* data cannot
  have such a theorem: the gauge is then unconstrained off the ideal, so two
  families can agree on every ideal element and still differ.
* **Every law is unconditional.**  In `ℝ≥0∞` the triangle inequality, the
  homogeneity `gauge (c • A) = ‖c‖ₑ * gauge A`, and the ideal bound
  `gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ` all hold verbatim at
  non-members, so no law needs a membership hypothesis and no lemma needs to
  carry one.
* **The axiom list is short.**  Four laws suffice.  Closure of the ideal under
  `0`, `+`, `•`, `-`, and finite sums is a *consequence* (it is
  `Submodule` membership for `carrier`), `gauge 0 = 0` follows from homogeneity
  at `c = 0`, and definiteness follows from `enorm_le_gauge`.

## Why Hilbert and not Banach

The four laws are statements about a norm, and every one of them is meaningful
verbatim for Banach `E`, `F`.  The *examples* are not.  Of the five gauges this
development has — the operator norm, the finite Ky Fan gauges, Schatten `p`,
trace class and Hilbert--Schmidt — only the first survives outside Hilbert
space, and the obstruction is `gauge_add_le`, not the definition.  Concretely,
for the finite Ky Fan gauge `∑_{n < k} aₙ(A)` the *gauge* is defined at full
Banach generality (`ContinuousLinearMap.approximationNumber` is stated for
seminormed spaces over a `NontriviallyNormedField`) while its subadditivity is
Hilbertian: the proof runs through singular values and majorization, and the
classical additivity of approximation numbers,
`a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`, does **not** recover it — already at `k = 2`
that bound only gives `a₀(S) + 2a₀(T) + a₁(S)`, which is not
`∑_{n<2} aₙ(S) + ∑_{n<2} aₙ(T)`.

So a Banach-wide version of this structure would be a notion with one instance
and no way to acquire the motivating ones.  The parameters are therefore Hilbert
throughout.  Re-widening is a purely mechanical edit should an instance ever
appear: no proof in this file uses the inner product, only the norm.

## Layering

`OperatorIdealFamily` keeps **independent source and target universes**.  Adjoint
symmetry cannot be added at that generality: `A✝` swaps the roles of source and
target, so a family closed under adjoints must be defined on a single universe.
That is `SymmetricOperatorIdealFamily`, which extends the diagonal
instantiation.

The two universes occur only through `max v w` in the type of the structure
itself, so `linter.checkUnivs` flags them; they are nevertheless genuinely
independent parameters of the *fields*, which is the point of the layer.

## Main definitions

* `TauCeti.OperatorIdealFamily`: the gauge and its four laws.
* `TauCeti.OperatorIdealFamily.carrier`: the ideal, as a `Submodule`.
* `TauCeti.OperatorIdealFamily.Elem`: the ideal as a normed space in its own
  right — a type synonym for the carrier carrying the *ideal* norm rather than
  the operator norm inherited from the ambient space.
* `TauCeti.OperatorIdealFamily.IsComplete`: completeness of the ideal, expressed
  as `CompleteSpace` for that norm rather than as a hand-rolled Cauchy criterion.
* `TauCeti.SymmetricOperatorIdealFamily`: the adjoint-invariant diagonal layer.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`
  (`RectangularSymmetricIdealFamily`, Jon Crall / OpenAI GPT-5.6 Thinking); Apache 2.0.
* Extraction class: **redesigned**.  Per the signature-polish backlog
  (`dev/tauceti-signature-polish-todo.md` §12.1) the free-data presentation
  (`Mem` plus a total real gauge constrained only on members, one universe,
  hand-rolled completeness, fourteen fields) is replaced here by the
  single-gauge presentation above.  The legacy structure is derivable from this
  one: see `DavisKahan/Interop/TauCeti/RectangularFamilyAdapter.lean`.
-/

@[expose] public section

namespace TauCeti

open scoped ENNReal

universe u v w

set_option linter.checkUnivs false in
/-- A **rectangular operator ideal family** over `𝕜`, presented by its gauge.

`gauge A` is the ideal norm of `A`, taken in `ℝ≥0∞` so that it is defined on
every bounded operator: `A` belongs to the ideal exactly when `gauge A ≠ ∞`
(`OperatorIdealFamily.carrier`).  Source and target are Hilbert spaces in
independent universes (see the module docstring for why Hilbert); adjoint
symmetry is added on the diagonal by `SymmetricOperatorIdealFamily`. -/
structure OperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  /-- The ideal norm, extended by `∞` off the ideal. -/
  gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ≥0∞
  /-- The gauge is subadditive. -/
  gauge_add_le : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A B : E →L[𝕜] F), gauge (A + B) ≤ gauge A + gauge B
  /-- The gauge is absolutely homogeneous.  At `c = 0` this forces
  `gauge 0 = 0`, ruling out the everywhere-infinite gauge. -/
  gauge_smul : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) (A : E →L[𝕜] F), gauge (c • A) = ‖c‖ₑ * gauge A
  /-- The gauge dominates the operator norm.  Together with `gauge_add_le` this
  makes the gauge a genuine norm on the ideal rather than a seminorm. -/
  enorm_le_gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), ‖A‖ₑ ≤ gauge A
  /-- The two-sided ideal law.  Finiteness of `‖L‖ₑ` and `‖R‖ₑ` makes this
  imply that the ideal is stable under outer composition. -/
  gauge_comp_le : ∀ {E H : Type v} {F G : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E),
      gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E H : Type v} {F G : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : OperatorIdealFamily.{u, v, w} 𝕜)

/-- Two ideal families with the same gauge are equal.

This is the theorem the free-data presentation cannot have: there, the gauge is
unconstrained off the ideal, so equality of the gauges *on members* — the only
thing the laws talk about — does not determine the structure. -/
@[ext]
theorem ext {N M : OperatorIdealFamily.{u, v, w} 𝕜}
    (h : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), N.gauge A = M.gauge A) : N = M := by
  cases N
  cases M
  congr 1
  funext E F _ _ _ _ _ _ A
  exact h A

/-- The gauge of the zero operator is zero. -/
@[simp]
theorem gauge_zero : N.gauge (0 : E →L[𝕜] F) = 0 := by
  have h := N.gauge_smul (0 : 𝕜) (0 : E →L[𝕜] F)
  simpa using h

/-- The gauge is definite: only the zero operator has gauge zero.  This is forced rather than
assumed -- it follows from `enorm_le_gauge`, since the operator norm is already definite. -/
theorem gauge_eq_zero {A : E →L[𝕜] F} (h : N.gauge A = 0) : A = 0 := by
  have hle : ‖A‖ₑ ≤ 0 := h ▸ N.enorm_le_gauge A
  have hz : ‖A‖ₑ = 0 := le_antisymm hle (by simp)
  rwa [enorm_eq_nnnorm, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hz

/-- Definiteness as an iff. -/
theorem gauge_eq_zero_iff {A : E →L[𝕜] F} : N.gauge A = 0 ↔ A = 0 :=
  ⟨N.gauge_eq_zero, fun h => h ▸ N.gauge_zero⟩

/-- The gauge is unchanged by negation. -/
@[simp]
theorem gauge_neg (A : E →L[𝕜] F) : N.gauge (-A) = N.gauge A := by
  have h := N.gauge_smul (-1 : 𝕜) A
  simpa using h

/-- Triangle inequality in subtracted form, the shape convergence arguments use. -/
theorem gauge_sub_le (A B : E →L[𝕜] F) : N.gauge (A - B) ≤ N.gauge A + N.gauge B := by
  simpa [sub_eq_add_neg] using N.gauge_add_le A (-B)

omit [CompleteSpace E] in
/-- The identity is a contraction for the extended norm. -/
private theorem enorm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.mpr ContinuousLinearMap.norm_id_le

/-- Subadditivity over a finite sum.

Unlike its counterpart for the historical record, this needs no membership
hypotheses: at a non-member the right-hand side is `∞`. -/
theorem gauge_sum_le {ι : Type*} (s : Finset ι) (A : ι → E →L[𝕜] F) :
    N.gauge (∑ i ∈ s, A i) ≤ ∑ i ∈ s, N.gauge (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (N.gauge_add_le _ _).trans (add_le_add le_rfl ih)

/-- Left composition by a bounded map, the `R = 1` case of the ideal law. -/
theorem gauge_comp_left_le (L : F →L[𝕜] G) (A : E →L[𝕜] F) :
    N.gauge (L ∘L A) ≤ ‖L‖ₑ * N.gauge A :=
  calc N.gauge (L ∘L A)
      = N.gauge (L ∘L A ∘L ContinuousLinearMap.id 𝕜 E) := by simp
    _ ≤ ‖L‖ₑ * N.gauge A * ‖ContinuousLinearMap.id 𝕜 E‖ₑ := N.gauge_comp_le _ _ _
    _ ≤ ‖L‖ₑ * N.gauge A * 1 := by gcongr; exact enorm_id_le
    _ = ‖L‖ₑ * N.gauge A := mul_one _

/-- Right composition by a bounded map, the `L = 1` case of the ideal law. -/
theorem gauge_comp_right_le (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    N.gauge (A ∘L R) ≤ N.gauge A * ‖R‖ₑ :=
  calc N.gauge (A ∘L R)
      = N.gauge (ContinuousLinearMap.id 𝕜 F ∘L A ∘L R) := by simp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ₑ * N.gauge A * ‖R‖ₑ := N.gauge_comp_le _ _ _
    _ ≤ 1 * N.gauge A * ‖R‖ₑ := by gcongr; exact enorm_id_le
    _ = N.gauge A * ‖R‖ₑ := by rw [one_mul]

/-- Left composition by a contraction does not increase the gauge. -/
theorem gauge_comp_left_le_of_norm_le_one {L : F →L[𝕜] G} (hL : ‖L‖ₑ ≤ 1) (A : E →L[𝕜] F) :
    N.gauge (L ∘L A) ≤ N.gauge A :=
  (N.gauge_comp_left_le L A).trans (by
    calc ‖L‖ₑ * N.gauge A ≤ 1 * N.gauge A := by gcongr
      _ = N.gauge A := one_mul _)

/-- Right composition by a contraction does not increase the gauge. -/
theorem gauge_comp_right_le_of_norm_le_one (A : E →L[𝕜] F) {R : H →L[𝕜] E} (hR : ‖R‖ₑ ≤ 1) :
    N.gauge (A ∘L R) ≤ N.gauge A :=
  (N.gauge_comp_right_le A R).trans (by
    calc N.gauge A * ‖R‖ₑ ≤ N.gauge A * 1 := by gcongr
      _ = N.gauge A := mul_one _)

/-- Two-sided composition by contractions does not increase the gauge. -/
theorem gauge_comp_le_of_norm_le_one {L : F →L[𝕜] G} {A : E →L[𝕜] F} {R : H →L[𝕜] E}
    (hL : ‖L‖ₑ ≤ 1) (hR : ‖R‖ₑ ≤ 1) : N.gauge (L ∘L A ∘L R) ≤ N.gauge A :=
  (N.gauge_comp_le L A R).trans (by
    calc ‖L‖ₑ * N.gauge A * ‖R‖ₑ ≤ 1 * N.gauge A * 1 := by gcongr
      _ = N.gauge A := by simp)

/-- The ideal itself: the operators of finite gauge, as a submodule.

Closure under `0`, `+` and `•` is a consequence of the gauge laws, so the
module structure of the ideal does not have to be assumed. -/
def carrier : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | N.gauge A ≠ ∞}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    refine ne_top_of_le_ne_top ?_ (N.gauge_add_le A B)
    exact ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  smul_mem' c A hA := by
    rw [Set.mem_setOf_eq, N.gauge_smul]
    exact ENNReal.mul_ne_top (by simp) hA

/-- Membership in the ideal is exactly finiteness of the gauge; the carrier is defined that way,
so this is `Iff.rfl` and exists only to spare call sites the unfolding. -/
@[simp]
theorem mem_carrier_iff {A : E →L[𝕜] F} : A ∈ N.carrier ↔ N.gauge A ≠ ∞ := Iff.rfl

/-- Members of the ideal have finite gauge. -/
theorem gauge_ne_top_of_mem {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.gauge A ≠ ∞ := hA

/-- Members of the ideal have gauge `< ∞`, the strict form. -/
theorem gauge_lt_top_of_mem {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.gauge A < ∞ :=
  lt_top_iff_ne_top.mpr hA

/-- Membership in the ideal is stable under outer composition. -/
theorem comp_mem_carrier (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E)
    (hA : A ∈ N.carrier) : L ∘L A ∘L R ∈ N.carrier := by
  refine ne_top_of_le_ne_top ?_ (N.gauge_comp_le L A R)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA) (by simp)

/-- The ideal is closed under finite sums — `Submodule.sum_mem` for the
carrier, with no separate closure axiom. -/
theorem sum_mem_carrier {ι : Type*} (s : Finset ι) {A : ι → E →L[𝕜] F}
    (hA : ∀ i ∈ s, A i ∈ N.carrier) : (∑ i ∈ s, A i) ∈ N.carrier :=
  Submodule.sum_mem _ hA

/-- The ideal between `E` and `F`, as a type carrying the **ideal** norm.

This is deliberately a type synonym rather than the subtype itself: the subtype
already inherits the *operator* norm from `E →L[𝕜] F`, and the two norms differ.
-/
def Elem (N : OperatorIdealFamily.{u, v, w} 𝕜) (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] : Type max v w :=
  _root_.Subtype fun A : E →L[𝕜] F => A ∈ N.carrier

namespace Elem

variable {N}

/-- The underlying operator of an ideal element. -/
def val (A : N.Elem E F) : E →L[𝕜] F := Subtype.val (p := fun A => A ∈ N.carrier) A

/-- The underlying operator of an ideal element lies in the ideal. -/
theorem val_mem (A : N.Elem E F) : A.val ∈ N.carrier := Subtype.property (p := _) A

/-- An ideal element has finite gauge -- the fact that makes `toReal` lossless on it, and hence
the reason the ideal norm can be real-valued while the gauge is `ℝ≥0∞`-valued. -/
theorem gauge_val_ne_top (A : N.Elem E F) : N.gauge A.val ≠ ∞ := A.val_mem

/-- An operator of finite gauge, as an element of the ideal. -/
def mk {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.Elem E F := ⟨A, hA⟩

@[simp] theorem val_mk {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : (mk (N := N) hA).val = A := rfl

@[ext] theorem ext {A B : N.Elem E F} (h : A.val = B.val) : A = B := Subtype.ext h

/-- The ideal is an additive subgroup of the bounded operators, inherited from its carrier. -/
instance : AddCommGroup (N.Elem E F) :=
  inferInstanceAs (AddCommGroup (N.carrier : Submodule 𝕜 (E →L[𝕜] F)))

/-- The ideal is a `𝕜`-submodule, inherited from its carrier. -/
instance : Module 𝕜 (N.Elem E F) :=
  inferInstanceAs (Module 𝕜 (N.carrier : Submodule 𝕜 (E →L[𝕜] F)))

@[simp] theorem val_zero : (0 : N.Elem E F).val = 0 := rfl
@[simp] theorem val_add (A B : N.Elem E F) : (A + B).val = A.val + B.val := rfl
@[simp] theorem val_neg (A : N.Elem E F) : (-A).val = -A.val := rfl
@[simp] theorem val_sub (A B : N.Elem E F) : (A - B).val = A.val - B.val := rfl
@[simp] theorem val_smul (c : 𝕜) (A : N.Elem E F) : (c • A).val = c • A.val := rfl

/-- The ideal norm, as a real-valued norm on the ideal. -/
noncomputable instance : NormedAddCommGroup (N.Elem E F) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun A => (N.gauge A.val).toReal
      map_zero' := by
        change (N.gauge (0 : N.Elem E F).val).toReal = 0
        rw [val_zero, N.gauge_zero, ENNReal.toReal_zero]
      add_le' := fun A B => by
        change (N.gauge (A + B).val).toReal ≤ (N.gauge A.val).toReal + (N.gauge B.val).toReal
        rw [val_add, ← ENNReal.toReal_add A.gauge_val_ne_top B.gauge_val_ne_top]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨A.gauge_val_ne_top, B.gauge_val_ne_top⟩)
          (N.gauge_add_le A.val B.val)
      neg' := fun A => by
        change (N.gauge (-A).val).toReal = (N.gauge A.val).toReal
        rw [val_neg, N.gauge_neg]
      eq_zero_of_map_eq_zero' := fun A hA => by
        refine ext ?_
        rw [val_zero]
        exact N.gauge_eq_zero
          (((ENNReal.toReal_eq_zero_iff _).mp hA).resolve_right A.gauge_val_ne_top) }

/-- The ideal norm is the gauge, brought down to `ℝ`.  Lossless because `gauge_val_ne_top`. -/
theorem norm_def (A : N.Elem E F) : ‖A‖ = (N.gauge A.val).toReal := rfl

/-- Going back up: the extended norm of an ideal element is its gauge exactly, with no `toReal`
round-trip loss. -/
theorem enorm_eq_gauge (A : N.Elem E F) : ‖A‖ₑ = N.gauge A.val := by
  rw [← ofReal_norm, norm_def, ENNReal.ofReal_toReal A.gauge_val_ne_top]

/-- The ideal norm is a norm on a `𝕜`-vector space; homogeneity transfers from `gauge_smul`
through `toReal`. -/
noncomputable instance : NormedSpace 𝕜 (N.Elem E F) where
  norm_smul_le c A := by
    rw [norm_def, norm_def, val_smul, N.gauge_smul, ENNReal.toReal_mul]
    simp

/-- The ideal embeds contractively into the bounded operators: the ideal norm
dominates the operator norm. -/
theorem norm_val_le (A : N.Elem E F) : ‖A.val‖ ≤ ‖A‖ := by
  have h := ENNReal.toReal_mono A.gauge_val_ne_top (N.enorm_le_gauge A.val)
  rwa [← norm_def, toReal_enorm] at h

end Elem

/-- Completeness of an ideal family, stated as `CompleteSpace` for the ideal
norm rather than as a hand-rolled Cauchy criterion.

Completeness of the target is available from the ambient assumptions, exactly as
for `E →L[𝕜] F`: an ideal norm cannot repair an incomplete target. -/
class IsComplete (N : OperatorIdealFamily.{u, v, w} 𝕜) : Prop where
  completeSpace : ∀ {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
    CompleteSpace (N.Elem E F)

/-- Unpacks `IsComplete` into the `CompleteSpace` instance that instance search needs; the class
quantifies over the two spaces, so it cannot be used directly. -/
instance [N.IsComplete] : CompleteSpace (N.Elem E F) :=
  IsComplete.completeSpace

end OperatorIdealFamily

/-- A **symmetric** (adjoint-invariant) operator ideal family on Hilbert spaces.

Adjoint invariance is stated on the diagonal instantiation of
`OperatorIdealFamily` because `ContinuousLinearMap.adjoint` exchanges the source
and target spaces: a family closed under adjoints cannot keep the two universes
independent. -/
structure SymmetricOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    extends OperatorIdealFamily.{u, v, v} 𝕜 where
  /-- The gauge is unchanged by passing to the adjoint. -/
  gauge_adjoint : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), toOperatorIdealFamily.gauge A.adjoint = toOperatorIdealFamily.gauge A

namespace SymmetricOperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)

/-- The ideal of a symmetric family is stable under adjoints. -/
theorem adjoint_mem_carrier {A : E →L[𝕜] F} (hA : A ∈ N.toOperatorIdealFamily.carrier) :
    A.adjoint ∈ N.toOperatorIdealFamily.carrier := by
  simpa [OperatorIdealFamily.mem_carrier_iff, N.gauge_adjoint A] using hA

end SymmetricOperatorIdealFamily

end TauCeti
