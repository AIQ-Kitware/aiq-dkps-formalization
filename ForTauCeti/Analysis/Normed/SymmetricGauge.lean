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

end SymmetricGauge

end TauCeti
