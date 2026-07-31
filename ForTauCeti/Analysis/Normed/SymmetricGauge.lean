/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import ForTauCeti.Analysis.Convex.Majorization

/-!
# Symmetric gauges on finitely supported nonnegative sequences

A **symmetric gauge** (Calkin's *symmetric norming function*) is a subadditive,
positively homogeneous, permutation-invariant and monotone functional on finitely
supported nonnegative sequences, normalized so that a single unit coordinate has
gauge one.  It is the scalar half of the theory of symmetrically normed operator
ideals: an ideal gauge is a symmetric gauge applied to a singular-value sequence.

* `TauCeti.SymmetricGauge` — the structure;
* `TauCeti.SymmetricGauge.single` — `Φ (single i c) = c`, the first consequence of
  normalization and permutation invariance together;
* `TauCeti.SymmetricGauge.le_apply` — `aᵢ ≤ Φ a` for every coordinate;
* `TauCeti.SymmetricGauge.apply_le_sum` — `Φ a ≤ ∑ aᵢ`;
* `TauCeti.SymmetricGauge.le_apply_and_le_sum` — the two-sided bound
  `sup aᵢ ≤ Φ a ≤ ∑ aᵢ` packaged together;
* `TauCeti.SymmetricGauge.extend` — the extension to arbitrary `ℝ≥0∞`-valued
  sequences, as a supremum over dominated finitely supported sequences;
* `TauCeti.SymmetricGauge.iSup_le_extend_le_tsum` — the same sandwich for the
  extension, `⨆ aₙ ≤ Φ.extend a ≤ ∑' aₙ`.

## Why this is not `FiniteSymmetricGauge`

`ForTauCeti.Analysis.Convex.Majorization` already has `FiniteSymmetricGauge n`, on
`(Fin n → ℝ) → ℝ`, with `real_smul'` and `neg_single'`.  That is the finite
*real-vector* gauge the majorization layer needs, and three concrete gauges are
built on it.  This structure is a different object: finitely supported sequences
indexed by `ℕ` rather than `Fin n`, values in `ℝ≥0` rather than `ℝ`, and `mono`
and `normalized` in place of the sign axioms.  Neither generalizes the other --
the finite one allows negative entries and does not fix a scale; this one fixes a
scale and takes monotonicity in the termwise order as an axiom, which is what the
two-sided bound below needs.

## The two-sided bound

`normalized` is what makes the sandwich `sup aᵢ ≤ Φ a ≤ ∑ aᵢ` available, and the
sandwich is what every later result is stated against.  Both halves come straight
from the axioms:

* **lower** -- `single i (a i) ≤ a` termwise, so `mono` and `single` give
  `a i ≤ Φ a`;
* **upper** -- `a` is the finite sum `∑ i ∈ a.support, single i (a i)`, so
  subadditivity and `single` give `Φ a ≤ ∑ i ∈ a.support, a i`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written for this repository against the target
  signature recorded in `ForTauCetiRoadmap/OperatorIdeals/Suggested.lean`, which
  states the structure and the two-sided bound; the field names and the shape of
  `SymmetricGauge` follow that file so the roadmap statement and the delivered
  one agree literally.
* Roadmap topic: `OperatorIdeals` (the symmetrically normed ideal layer).
* Original authors / copyright: Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/

open scoped NNReal ENNReal

namespace TauCeti

/-- A **symmetric gauge** on finitely supported nonnegative sequences: Calkin's
symmetric norming function.

`symm` is stated against `Equiv.Perm ℕ` acting by precomposition on the finitely
supported sequence, which is what makes "symmetric" a property of `Φ` rather than
a property of the sequences it is applied to. -/
structure SymmetricGauge where
  /-- The underlying gauge on finitely supported nonnegative sequences. -/
  toFun : (ℕ →₀ ℝ≥0) → ℝ≥0
  /-- Subadditivity. -/
  add_le : ∀ a b : ℕ →₀ ℝ≥0, toFun (a + b) ≤ toFun a + toFun b
  /-- Positive homogeneity. -/
  smul : ∀ (c : ℝ≥0) (a : ℕ →₀ ℝ≥0), toFun (c • a) = c * toFun a
  /-- Permutation invariance -- the "symmetric" in symmetric norming function. -/
  symm : ∀ (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0),
    toFun (Finsupp.equivMapDomain σ a) = toFun a
  /-- Monotonicity in the termwise order. -/
  mono : ∀ ⦃a b : ℕ →₀ ℝ≥0⦄, a ≤ b → toFun a ≤ toFun b
  /-- Normalization: the first basis vector has gauge one.  This fixes the scale,
  and with it the two-sided bound `‖a‖_∞ ≤ Φ a ≤ ∑ aₙ`. -/
  normalized : toFun (Finsupp.single 0 1) = 1

namespace SymmetricGauge

/-- Apply a symmetric gauge directly to a sequence, writing `Φ a` for `Φ.toFun a`. -/
instance : CoeFun SymmetricGauge fun _ => (ℕ →₀ ℝ≥0) → ℝ≥0 :=
  ⟨SymmetricGauge.toFun⟩

variable (Φ : SymmetricGauge)

/-- The coercion agrees with the underlying field, so `simp` can move between
`Φ.toFun a` and `Φ a` without unfolding the structure. -/
@[simp]
theorem coe_toFun (a : ℕ →₀ ℝ≥0) : Φ.toFun a = Φ a := rfl

/-- The gauge of the zero sequence is zero.  Immediate from homogeneity at `c = 0`,
and needed before any sum argument can start from an empty support. -/
@[simp]
theorem map_zero : Φ 0 = 0 := by
  have h := Φ.smul 0 0
  simpa using h

/-- Every unit basis vector has gauge one: permutation invariance transports the
normalization at `0` to an arbitrary index.

This is the first place the `symm` axiom does real work, and it is why
`normalized` may be stated at the single index `0` rather than for all of them. -/
@[simp]
theorem single_one (i : ℕ) : Φ (Finsupp.single i 1) = 1 := by
  classical
  -- The transposition swapping `0` and `i` carries `single 0 1` to `single i 1`.
  have hmap : Finsupp.equivMapDomain (Equiv.swap 0 i) (Finsupp.single 0 (1 : ℝ≥0))
      = Finsupp.single i 1 := by
    ext j
    simp [Finsupp.single_apply]
  calc Φ (Finsupp.single i 1)
      = Φ (Finsupp.equivMapDomain (Equiv.swap 0 i) (Finsupp.single 0 1)) := by
        rw [hmap]
    _ = Φ (Finsupp.single 0 1) := Φ.symm _ _
    _ = 1 := Φ.normalized

/-- A single coordinate is measured by its value: `Φ (single i c) = c`. -/
@[simp]
theorem single (i : ℕ) (c : ℝ≥0) : Φ (Finsupp.single i c) = c := by
  have hsmul : c • Finsupp.single i (1 : ℝ≥0) = Finsupp.single i c := by
    ext j; simp [Finsupp.single_apply]
  calc Φ (Finsupp.single i c)
      = Φ (c • Finsupp.single i 1) := by rw [hsmul]
    _ = c * Φ (Finsupp.single i 1) := Φ.smul _ _
    _ = c := by rw [single_one]; exact mul_one c

/-- **Lower half of the two-sided bound.**  Every coordinate is dominated by the
gauge: `aᵢ ≤ Φ a`.

`single i (a i) ≤ a` holds termwise -- the two agree at `i` and the left side is
zero elsewhere -- so this is `mono` followed by `single`. -/
theorem le_apply (a : ℕ →₀ ℝ≥0) (i : ℕ) : a i ≤ Φ a := by
  have hle : Finsupp.single i (a i) ≤ a := by
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  calc a i = Φ (Finsupp.single i (a i)) := (single Φ i (a i)).symm
    _ ≤ Φ a := Φ.mono hle

/-- **Upper half of the two-sided bound.**  The gauge is dominated by the sum:
`Φ a ≤ ∑ aᵢ`.

`a` is the finite sum of its single-coordinate pieces over its support, so this is
subadditivity along that decomposition followed by `single`. -/
theorem apply_le_sum (a : ℕ →₀ ℝ≥0) : Φ a ≤ ∑ i ∈ a.support, a i := by
  classical
  -- Rebuild `a` from its support, then push the gauge through the finite sum.
  have hsum : a = ∑ i ∈ a.support, Finsupp.single i (a i) := by
    ext j; simp [Finsupp.single_apply]
  have hstep : ∀ (s : Finset ℕ),
      Φ (∑ i ∈ s, Finsupp.single i (a i)) ≤ ∑ i ∈ s, a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s his ih =>
        rw [Finset.sum_insert his, Finset.sum_insert his]
        calc Φ (Finsupp.single i (a i) + ∑ j ∈ s, Finsupp.single j (a j))
            ≤ Φ (Finsupp.single i (a i)) + Φ (∑ j ∈ s, Finsupp.single j (a j)) :=
              Φ.add_le _ _
          _ ≤ a i + ∑ j ∈ s, a j := by
              gcongr
              · exact le_of_eq (single Φ i (a i))
  calc Φ a = Φ (∑ i ∈ a.support, Finsupp.single i (a i)) := by rw [← hsum]
    _ ≤ ∑ i ∈ a.support, a i := hstep _

/-- **The two-sided bound**, packaged: every coordinate is below the gauge and the
gauge is below the sum.

This sandwich is what later results -- the extension to non-finitely-supported
sequences, the induced ideal family, and Ky Fan dominance -- are stated against,
and it is the reason `normalized` is an axiom rather than a convention. -/
theorem le_apply_and_le_sum (a : ℕ →₀ ℝ≥0) :
    (∀ i, a i ≤ Φ a) ∧ Φ a ≤ ∑ i ∈ a.support, a i :=
  ⟨fun i => le_apply Φ a i, apply_le_sum Φ a⟩

/-! ## Extension to arbitrary `ℝ≥0∞`-valued sequences -/

/-- The finitely supported nonnegative sequences dominated termwise by `a`.

This is the index set of the supremum defining `extend`.  It is nonempty for
every `a` -- the zero sequence always qualifies -- which is what makes the
extension total. -/
def Dominated (a : ℕ → ℝ≥0∞) : Type :=
  {b : ℕ →₀ ℝ≥0 // ∀ i, (b i : ℝ≥0∞) ≤ a i}

/-- The index set is never empty: the zero sequence is dominated by every `a`.

This is what makes `extend` total — a supremum over an empty index set would be
`0` regardless of `a`, which would break the lower bound. -/
instance (a : ℕ → ℝ≥0∞) : Nonempty (Dominated a) :=
  ⟨⟨0, by intro i; simp⟩⟩

/-- The extension of a symmetric gauge to arbitrary `ℝ≥0∞`-valued sequences: the
supremum of `Φ` over the finitely supported sequences dominated by `a`.

**A supremum, not a `tsum`.**  The gauge must be total and genuinely `∞` off its
ideal, and a supremum of an increasing net is total by construction; any route
through summability reintroduces the side conditions the interface avoids.

**On the decreasing rearrangement.**  The supremum is taken over *all* dominated
finitely supported sequences, with no rearrangement.  That is equivalent to
truncating the decreasing rearrangement, because `Φ` is permutation-invariant
(`symm`) and monotone (`mono`), so the supremum is already rearrangement-
independent; the rearrangement is a device for *computing* the value rather than
part of its specification, and avoiding it here keeps this file free of a
rearrangement API it would otherwise have to build first. -/
noncomputable def extend (Φ : SymmetricGauge) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ b : Dominated a, (Φ b.1 : ℝ≥0∞)

/-- Each dominated finitely supported sequence bounds the extension from below. -/
theorem le_extend_of_dominated (a : ℕ → ℝ≥0∞) (b : ℕ →₀ ℝ≥0)
    (hb : ∀ i, (b i : ℝ≥0∞) ≤ a i) : (Φ b : ℝ≥0∞) ≤ Φ.extend a :=
  le_iSup (f := fun b : Dominated a => (Φ b.1 : ℝ≥0∞)) ⟨b, hb⟩

/-- **Lower half of the extended bound.**  Every coordinate is below the extension.

This reaches `∞` correctly: when `a n = ∞` the argument supplies `single n c` for
every finite `c`, so the supremum is not bounded by any real. -/
theorem le_extend (a : ℕ → ℝ≥0∞) (n : ℕ) : a n ≤ Φ.extend a := by
  -- It suffices to beat every finite `c` strictly below `a n`; when `a n = ∞`
  -- that ranges over all of `ℝ≥0`, so the supremum is forced to `∞` as well.
  refine ENNReal.le_of_forall_nnreal_lt fun c hc => ?_
  have hdom : ∀ i, ((Finsupp.single n c) i : ℝ≥0∞) ≤ a i := by
    intro i
    by_cases hin : i = n
    · subst hin; simpa using hc.le
    · simp [hin]
  have hb := le_extend_of_dominated Φ a (Finsupp.single n c) hdom
  rwa [single Φ n c] at hb

/-- **Upper half of the extended bound.**  The extension is below the total sum. -/
theorem extend_le_tsum (a : ℕ → ℝ≥0∞) : Φ.extend a ≤ ∑' n, a n := by
  refine iSup_le fun b => ?_
  calc (Φ b.1 : ℝ≥0∞)
      ≤ ((∑ i ∈ b.1.support, b.1 i : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast apply_le_sum Φ b.1
    _ = ∑ i ∈ b.1.support, ((b.1 i : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ∑ i ∈ b.1.support, a i := Finset.sum_le_sum fun i _ => b.2 i
    _ ≤ ∑' n, a n := ENNReal.sum_le_tsum _

/-- **Both ends of the scale**, and the reason the normalization is not a
restriction: the extension sits between the supremum and the sum. -/
theorem iSup_le_extend_le_tsum (a : ℕ → ℝ≥0∞) :
    (⨆ n, a n) ≤ Φ.extend a ∧ Φ.extend a ≤ ∑' n, a n :=
  ⟨iSup_le fun n => le_extend Φ a n, extend_le_tsum Φ a⟩

/-! ## Bridge to the finite majorization theory

`ForTauCeti.Analysis.Convex.Majorization` proves the Hardy--Littlewood--Pólya
transfer descent for `FiniteSymmetricGauge`, on `(Fin n → ℝ) → ℝ`.  That layer is
not directly usable here -- this gauge lives on `(ℕ →₀ ℝ≥0) → ℝ≥0` and takes
`mono` and `normalized` as axioms where the finite one takes sign conditions --
so the descent is imported through an adapter rather than reproved.

The adapter sends `x : Fin n → ℝ` to `Φ` applied to the componentwise absolute
value, read as a finitely supported sequence on `ℕ`.
-/

/-- The componentwise absolute value of a finite real vector, as a finitely
supported nonnegative sequence on `ℕ`.

Uses `Real.nnabs` rather than an anonymous `⟨|x i|, _⟩`: the latter carries a
proof inside the term, so every rewrite has to happen under a dependent pair and
`rw` reports the motive as ill-typed.  `Real.nnabs` is a `MonoidWithZeroHom`, so
`map_mul` also supplies the scaling law below for free. -/
noncomputable def ofFin {n : ℕ} (x : Fin n → ℝ) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range n)
    (fun i => if h : i < n then Real.nnabs (x ⟨i, h⟩) else 0)
    (by
      intro i hi
      by_cases h : i < n
      · exact Finset.mem_range.mpr h
      · simp [h] at hi)

/-- `ofFin` reads off `Real.nnabs` at an in-range index. -/
@[simp]
theorem ofFin_apply {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : i < n) :
    (ofFin x) i = Real.nnabs (x ⟨i, h⟩) := by
  simp only [ofFin, Finsupp.onFinset_apply, h, dif_pos]

/-- `ofFin` vanishes outside the range. -/
@[simp]
theorem ofFin_apply_of_le {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : ¬ i < n) :
    (ofFin x) i = 0 := by
  simp only [ofFin, Finsupp.onFinset_apply, h, dif_neg, not_false_iff]

/-- `ofFin` is monotone in the componentwise order on absolute values. -/
theorem ofFin_le_ofFin {n : ℕ} {x y : Fin n → ℝ}
    (h : ∀ i, |x i| ≤ |y i|) : ofFin x ≤ ofFin y := by
  intro i
  by_cases hi : i < n
  · rw [ofFin_apply x hi, ofFin_apply y hi, ← NNReal.coe_le_coe,
      Real.coe_nnabs, Real.coe_nnabs]
    exact h ⟨i, hi⟩
  · simp [ofFin_apply_of_le, hi]

/-- The absolute value of a sum is dominated termwise by the sum of the absolute
values, transported to `ofFin`.  This is the step that needs `mono`. -/
theorem ofFin_add_le {n : ℕ} (x y : Fin n → ℝ) :
    ofFin (x + y) ≤ ofFin x + ofFin y := by
  intro i
  by_cases hi : i < n
  · rw [ofFin_apply (x + y) hi, Finsupp.add_apply, ofFin_apply x hi,
      ofFin_apply y hi, ← NNReal.coe_le_coe]
    push_cast
    simpa using abs_add_le (x ⟨i, hi⟩) (y ⟨i, hi⟩)
  · simp [ofFin_apply_of_le, hi]

/-- Scaling a finite vector scales its `ofFin` image by the absolute value. -/
theorem ofFin_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    ofFin (c • x) = Real.nnabs c • ofFin x := by
  ext i
  by_cases hi : i < n
  · rw [ofFin_apply (c • x) hi, Finsupp.smul_apply, ofFin_apply x hi,
      smul_eq_mul]
    simp [map_mul]
  · simp [ofFin_apply_of_le, hi]

/-- Flipping the sign of a single coordinate leaves the `ofFin` image unchanged. -/
theorem ofFin_update_neg {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    ofFin (Function.update x j (-(x j))) = ofFin x := by
  ext i
  by_cases hi : i < n
  · rw [ofFin_apply _ hi, ofFin_apply x hi]
    by_cases hij : (⟨i, hi⟩ : Fin n) = j
    · rw [hij, Function.update_self]
      simp
    · rw [Function.update_of_ne hij]
  · simp [ofFin_apply_of_le, hi]

/-- A permutation of `Fin n` as a permutation of `ℕ`, fixing everything outside
the range.

Built by hand rather than through `Equiv.Perm.extendDomain` so that the transport
equation below can be proved by direct computation on indices. -/
def natPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (π ⟨i, h⟩ : ℕ) else i
  invFun i := if h : i < n then (π.symm ⟨i, h⟩ : ℕ) else i
  left_inv i := by
    by_cases h : i < n
    · simp only [dif_pos h, dif_pos (π ⟨i, h⟩).isLt]
      simp
    · simp [h]
  right_inv i := by
    by_cases h : i < n
    · simp only [dif_pos h, dif_pos (π.symm ⟨i, h⟩).isLt]
      simp
    · simp [h]

/-- `natPerm` acts as `π` inside the range. -/
@[simp]
theorem natPerm_apply_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    natPerm π i = (π ⟨i, h⟩ : ℕ) := by
  simp [natPerm, h]

/-- `natPerm`'s inverse acts as `π.symm` inside the range. -/
@[simp]
theorem natPerm_symm_apply_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i : ℕ}
    (h : i < n) : (natPerm π).symm i = (π.symm ⟨i, h⟩ : ℕ) := by
  simp [natPerm, h]

/-- **The transport equation.**  Permuting the coordinates of a finite vector
corresponds to relabelling its `ofFin` image along `natPerm`.

This is the step that makes `SymmetricGauge.symm` -- an axiom about
`Equiv.Perm ℕ` -- usable against `FiniteSymmetricGauge.perm'`, which quantifies
over `Equiv.Perm (Fin n)`. -/
theorem ofFin_comp_perm {n : ℕ} (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ofFin (x ∘ π) = Finsupp.equivMapDomain (natPerm π).symm (ofFin x) := by
  ext i
  rw [Finsupp.equivMapDomain_apply]
  by_cases hi : i < n
  · have h2 : ((natPerm π).symm).symm i = (π ⟨i, hi⟩ : ℕ) := by
      simp [natPerm, hi]
    rw [ofFin_apply _ hi, h2, ofFin_apply x (π ⟨i, hi⟩).isLt]
    rfl
  · have h2 : ((natPerm π).symm).symm i = i := by simp [natPerm, hi]
    rw [h2, ofFin_apply_of_le _ hi, ofFin_apply_of_le _ hi]

/-- **The adapter.**  A symmetric gauge restricts to a `FiniteSymmetricGauge` on
each `Fin n`, by applying it to the componentwise absolute value.

This is what lets the Hardy--Littlewood--Pólya transfer descent of
`ForTauCeti.Analysis.Convex.Majorization` be *used* here rather than reproved.
Each field is one axiom of `SymmetricGauge` composed with one `ofFin` lemma:

* `add_le'` -- `ofFin_add_le`, then `mono`, then `add_le`.  **This is the one
  field where `mono` does work that is invisible in the finite theory**, where
  the corresponding monotonicity is a consequence of the descent rather than an
  assumption;
* `real_smul'` -- `ofFin_smul` then `smul`;
* `perm'` -- `ofFin_comp_perm` then `symm`.  The axiom speaks of `Equiv.Perm ℕ`
  and the field of `Equiv.Perm (Fin n)`; the transport equation is what makes
  them meet, and it was the last obstruction;
* `neg_single'` -- `ofFin_update_neg`, which needs nothing about `Φ` at all. -/
noncomputable def toFiniteSymmetricGauge (Φ : SymmetricGauge) (n : ℕ) :
    FiniteSymmetricGauge n where
  toFun x := (Φ (ofFin x) : ℝ)
  add_le' x y := by
    have h : Φ (ofFin (x + y)) ≤ Φ (ofFin x) + Φ (ofFin y) :=
      (Φ.mono (ofFin_add_le x y)).trans (Φ.add_le _ _)
    exact_mod_cast h
  real_smul' c x := by
    rw [ofFin_smul, Φ.smul]
    simp [Real.coe_nnabs]
  perm' x π := by rw [ofFin_comp_perm, Φ.symm]
  neg_single' x j := by rw [ofFin_update_neg]

/-- **The transfer descent, available for `SymmetricGauge`.**  If `z` is antitone
and nonnegative and every prefix sum of `z` is dominated by that of `y`, then
`Φ (ofFin z) ≤ Φ (ofFin y)`.

This is `FiniteSymmetricGauge.le_of_prefixSum_le` pulled back along the adapter:
no part of the Hardy--Littlewood--Pólya argument is repeated here, which was the
point of building the adapter rather than reproving the descent. -/
theorem le_of_prefixSum_le (Φ : SymmetricGauge) {n : ℕ} {z y : Fin n → ℝ}
    (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, y i) :
    Φ (ofFin z) ≤ Φ (ofFin y) := by
  have h := (Φ.toFiniteSymmetricGauge n).le_of_prefixSum_le hz_anti hz0 hy0 hpre
  exact_mod_cast h

/-- Weak majorization implies domination under every symmetric gauge. -/
theorem mono_weaklyMajorized (Φ : SymmetricGauge) {n : ℕ} {x y : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x y) : Φ (ofFin x) ≤ Φ (ofFin y) := by
  have := (Φ.toFiniteSymmetricGauge n).mono_weaklyMajorized h
  exact_mod_cast this

/-- If any coordinate is infinite, so is the extension.

This is the case that makes the `⨆`-definition of `extend` behave: the gauge is
`∞` off its ideal without any summability hypothesis. -/
theorem extend_eq_top_of_eq_top {a : ℕ → ℝ≥0∞} {n : ℕ} (h : a n = ⊤) :
    Φ.extend a = ⊤ :=
  top_unique (h ▸ le_extend Φ a n)

/-- Truncation of a finite-valued sequence to the first `N` coordinates, as a
finitely supported nonnegative sequence.

Stated for `a : ℕ → ℝ≥0∞` together with a proof that every coordinate is finite,
because that is the shape the majorization argument produces after its infinite
cases are discharged. -/
noncomputable def truncate (a : ℕ → ℝ≥0∞) (_ha : ∀ n, a n ≠ ⊤) (N : ℕ) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range N)
    (fun i => if i < N then (a i).toNNReal else 0)
    (by
      intro i hi
      by_cases h : i < N
      · exact Finset.mem_range.mpr h
      · simp [h] at hi)

/-- The truncation is dominated by the sequence it truncates. -/
theorem truncate_le (a : ℕ → ℝ≥0∞) (ha : ∀ n, a n ≠ ⊤) (N : ℕ) (i : ℕ) :
    ((truncate a ha N) i : ℝ≥0∞) ≤ a i := by
  by_cases h : i < N
  · simp only [truncate, Finsupp.onFinset_apply, h, if_pos]
    rw [ENNReal.coe_toNNReal (ha i)]
  · simp [truncate, h]

/-- **Finiteness transfers backwards along prefix-sum domination.**

If every prefix sum of `a` is dominated by that of `b` and `b` is finite in every
coordinate, then so is `a`.  A single infinite coordinate of `a` would make its
prefix sum at `n + 1` equal `⊤`, which the hypothesis would force onto a prefix
sum of `b` that is a finite sum of finite terms.

This is the step that lets the majorization argument discharge `ℝ≥0∞` and work
with honest finitely supported truncations. -/
theorem ne_top_of_forall_sum_le {a b : ℕ → ℝ≥0∞}
    (hbtop : ∀ n, b n ≠ ⊤)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    ∀ n, a n ≠ ⊤ := by
  intro n hn
  have hsum : ∑ m ∈ Finset.range (n + 1), a m = ⊤ :=
    ENNReal.sum_eq_top.mpr ⟨n, Finset.self_mem_range_succ n, hn⟩
  have hle := h (n + 1)
  rw [hsum, top_le_iff] at hle
  obtain ⟨m, _, hm⟩ := ENNReal.sum_eq_top.mp hle
  exact hbtop m hm

/-! ### The remaining step of `extend_le_extend_of_forall_sum_le`

The roadmap target (`ForTauCetiRoadmap/OperatorIdeals/Suggested.lean`) is

```
theorem extend_le_extend_of_forall_sum_le (Φ : SymmetricGauge)
    {a b : ℕ → ℝ≥0∞} (ha : Antitone a) (hb : Antitone b)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    Φ.extend a ≤ Φ.extend b
```

and it splits into three cases, of which **two are proved above**:

* if some `b n = ⊤` then `extend_eq_top_of_eq_top` makes the right side `⊤`;
* otherwise `ne_top_of_forall_sum_le` shows `a` is finite everywhere too;
* **remaining:** with both finite, bound each `c` dominated by `a` using
  `truncate a _ N` for `N` past `c`'s support -- `c ≤ truncate a _ N` termwise
  gives `Φ c ≤ Φ (truncate a _ N)` by `mono`, and `truncate a _ N` is antitone
  because `a` is -- then apply `le_of_prefixSum_le` against `truncate b _ N` and
  finish with `le_extend_of_dominated` and `truncate_le`.

The one piece of friction in that last step, recorded so it is not rediscovered:
`le_of_prefixSum_le` states its hypothesis with
`∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)`, whereas the sequence
hypothesis here is over `Finset.range k`, so the two prefix-sum shapes must be
reconciled before the descent can be applied.
-/

end SymmetricGauge

end TauCeti
