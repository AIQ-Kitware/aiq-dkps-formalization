/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib.Data.Finsupp.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Symmetric norming functions on sequences

A **symmetric norming function** in the sense of Gohberg–Kreĭn: a subadditive,
positively homogeneous, permutation-invariant, monotone, normalized gauge on
finitely supported nonnegative sequences, together with its extension to
arbitrary `ℝ≥0∞`-valued sequences.

## Main definitions

* `TauCeti.SymmetricGauge` — the structure.
* `TauCeti.SymmetricGauge.extend` — the extension to `ℕ → ℝ≥0∞`, as a supremum
  over finitely supported truncations.

## Main results

* `TauCeti.SymmetricGauge.single` — the gauge of a basis vector is its value;
  this is what `normalized'` and `symm'` buy together, and everything needing a
  scale goes through it.
* `TauCeti.SymmetricGauge.extend_mono` — monotone in the sequence.
* `TauCeti.SymmetricGauge.iSup_le_extend_le_tsum` — the two ends of the scale,
  `‖a‖_∞ ≤ Φ∞ a ≤ ∑ aₙ`, which is where `normalized` earns its place.

## Design

This is the `ℕ`-indexed, `ℝ≥0`-valued counterpart of
`TauCeti.FiniteSymmetricGauge` in `ForTauCeti/Analysis/Convex/Majorization.lean`,
and it mirrors that structure field for field where the two agree. The
differences are forced rather than chosen: values are `ℝ≥0`, so the finite
version's `real_smul'` with its `|c|` becomes plain multiplication and
`neg_single'` disappears; and `mono` and `normalized` are added, both of which
are vacuous or meaningless at a fixed finite index type.

**`extend` is a supremum, not a `tsum`.** The gauge has to be total and genuinely
`∞` off its ideal, and a supremum of an increasing net is total by construction,
where any route through summability reintroduces the side conditions this
interface exists to avoid. The same choice is what lets `schattenENorm` live at
`ℝ≥0∞` without side conditions.

**The supremum is over `Finset.range k` truncations rather than over all finitely
supported minorants.** Those give the same value — `mono` plus `symm` is exactly
what makes a truncation of the decreasing rearrangement extremal among minorants
of the same support size — but the `range k` form is a *monotone* net indexed by
`ℕ`, which is what a limit argument can use. Nothing in this file needs that
equivalence, and the family construction that does should prove it rather than
inherit it as a definition.

## Not proved here, deliberately

`extend_coe_finsupp` — that `extend` restricted to a finitely supported sequence
is the gauge itself — is **not** in this file. It is true and it is the obvious
next lemma, but it needs the extremality of `range k` truncations noted above,
which is the same fact `symmetricGaugeFamily` needs. Proving it twice, or proving
it here and having the family slice restate it, is how one fact ends up with two
names. It belongs to the second slice of `{lane:FTC-SYMGAUGE}`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
  The signatures are `ForTauCetiRoadmap/OperatorIdeals/Suggested.lean`'s, which
  recorded them as Milestone B1 targets; this is their first implementation.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: none.
-/

open scoped ENNReal NNReal

namespace TauCeti

/-- A **symmetric norming function** (Gohberg–Kreĭn): a monotone,
permutation-invariant, normalized gauge on finitely supported nonnegative
sequences.

`symm'` is stated against `Equiv.Perm ℕ` acting by precomposition, which is what
makes "symmetric" a property of `Φ` rather than a property of the sequences it is
applied to. -/
structure SymmetricGauge where
  /-- The underlying gauge on finitely supported nonnegative sequences. -/
  toFun : (ℕ →₀ ℝ≥0) → ℝ≥0
  /-- Subadditivity. -/
  add_le' : ∀ a b : ℕ →₀ ℝ≥0, toFun (a + b) ≤ toFun a + toFun b
  /-- Positive homogeneity. -/
  smul' : ∀ (c : ℝ≥0) (a : ℕ →₀ ℝ≥0), toFun (c • a) = c * toFun a
  /-- Permutation invariance — the "symmetric" in symmetric norming function. -/
  symm' : ∀ (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0),
    toFun (Finsupp.equivMapDomain σ a) = toFun a
  /-- Monotonicity in the termwise order. -/
  mono' : ∀ ⦃a b : ℕ →₀ ℝ≥0⦄, a ≤ b → toFun a ≤ toFun b
  /-- Normalization: the first basis vector has gauge one.  This fixes the scale,
  and with it the two-sided bound `‖a‖_∞ ≤ Φ a ≤ ∑ aₙ`. -/
  normalized' : toFun (Finsupp.single 0 1) = 1

namespace SymmetricGauge

/-- Apply a symmetric gauge directly, writing `Φ a` for `Φ.toFun a`. -/
instance : CoeFun SymmetricGauge fun _ => (ℕ →₀ ℝ≥0) → ℝ≥0 :=
  ⟨SymmetricGauge.toFun⟩

variable (Φ : SymmetricGauge)

/-- Subadditivity, as a theorem rather than a structure field. -/
@[simp] theorem add_le (a b : ℕ →₀ ℝ≥0) : Φ (a + b) ≤ Φ a + Φ b := Φ.add_le' a b

/-- Positive homogeneity. -/
@[simp] theorem smul (c : ℝ≥0) (a : ℕ →₀ ℝ≥0) : Φ (c • a) = c * Φ a := Φ.smul' c a

/-- Permutation invariance. -/
@[simp] theorem symm (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0) :
    Φ (Finsupp.equivMapDomain σ a) = Φ a := Φ.symm' σ a

/-- Monotonicity in the termwise order. -/
theorem mono {a b : ℕ →₀ ℝ≥0} (h : a ≤ b) : Φ a ≤ Φ b := Φ.mono' h

/-- The first basis vector has gauge one. -/
@[simp] theorem normalized : Φ (Finsupp.single 0 1) = 1 := Φ.normalized'

/-- A gauge kills zero, by homogeneity at `c = 0`. -/
@[simp] theorem map_zero : Φ 0 = 0 := by
  have h := Φ.smul 0 0
  simpa using h

/-- **Every basis vector has gauge one, not just the first.**

This is the whole content of `normalized'` together with `symm'`: normalizing at
index `0` looks like an arbitrary choice, and permutation invariance is what makes
it not one.  Everything downstream that needs a scale — both ends of
`iSup_le_extend_le_tsum` — goes through this. -/
@[simp] theorem single_one (n : ℕ) : Φ (Finsupp.single n 1) = 1 := by
  have h : Finsupp.equivMapDomain (Equiv.swap 0 n) (Finsupp.single 0 1)
      = Finsupp.single n (1 : ℝ≥0) := by
    -- `equivMapDomain σ` reindexes by `σ⁻¹`; for a transposition `σ⁻¹ = σ`.
    ext j
    by_cases hj : j = n
    · subst hj; simp
    · rcases eq_or_ne j 0 with rfl | hj0
      · simp [Ne.symm hj]
      · rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap,
          Equiv.swap_apply_of_ne_of_ne hj0 hj]
        simp [Ne.symm hj0, Ne.symm hj]
  calc Φ (Finsupp.single n 1) = Φ (Finsupp.equivMapDomain (Equiv.swap 0 n)
          (Finsupp.single 0 1)) := by rw [h]
    _ = Φ (Finsupp.single 0 1) := Φ.symm _ _
    _ = 1 := Φ.normalized

/-- The gauge of a single basis vector is its value. -/
@[simp] theorem single (n : ℕ) (c : ℝ≥0) : Φ (Finsupp.single n c) = c := by
  have hsm : c • Finsupp.single n (1 : ℝ≥0) = Finsupp.single n c := by
    ext j; by_cases hj : j = n <;> simp [hj]
  calc Φ (Finsupp.single n c) = Φ (c • Finsupp.single n (1 : ℝ≥0)) := by rw [hsm]
    _ = c * Φ (Finsupp.single n 1) := Φ.smul _ _
    _ = c := by rw [Φ.single_one n, mul_one]

/-- The `k`-term truncation of `a`, capped at `m`, as a finitely supported
`ℝ≥0`-valued sequence.

Built with `Finsupp.onFinset` rather than as a sum of `Finsupp.single`s so that
`truncate_apply` below is definitional: every fact about `extend` is a pointwise
fact about this function, and a sum of singles would put `Finset.sum_apply'`
between the two. -/
noncomputable def truncate (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range k)
    (fun n => if n < k then (min (a n) (m : ℝ≥0∞)).toNNReal else 0)
    (fun n hn => by
      by_cases h : n < k
      · simpa using h
      · simp [h] at hn)

/-- The truncation, pointwise.  Definitional -- see `truncate`. -/
@[simp] theorem truncate_apply (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) (n : ℕ) :
    truncate a k m n = if n < k then (min (a n) (m : ℝ≥0∞)).toNNReal else 0 := rfl

/-- The extension of a symmetric gauge to arbitrary `ℝ≥0∞`-valued sequences: the
supremum of `Φ` over the truncations.

The supremum is over both the length `k` and a cap `m` on the values, and **the
cap is applied in `ℝ≥0∞`, before the conversion, not after**.  That is not a
stylistic choice: `ENNReal.toNNReal ∞ = 0`, so `min (a n).toNNReal m` reads an
infinite entry as *zero* and is not monotone in `a`.  Capping first sends `∞` to
`m`, and the supremum over `m` then recovers `∞` as the supremum of the finite
cuts, which is the value the gauge should take. -/
noncomputable def extend (Φ : SymmetricGauge) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ k : ℕ, ⨆ m : ℝ≥0, (Φ (truncate a k m) : ℝ≥0∞)

/-- Truncation is monotone in the sequence, at fixed length and cap. -/
theorem truncate_mono {a b : ℕ → ℝ≥0∞} (h : ∀ n, a n ≤ b n) (k : ℕ) (m : ℝ≥0) :
    truncate a k m ≤ truncate b k m := by
  refine Finsupp.le_def.2 fun n => ?_
  simp only [truncate_apply]
  split
  · refine ENNReal.toNNReal_mono ?_ (min_le_min (h n) le_rfl)
    exact ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := m)) (min_le_right _ _)
  · exact le_rfl

/-- The extension is monotone in the sequence. -/
theorem extend_mono {a b : ℕ → ℝ≥0∞} (h : ∀ n, a n ≤ b n) :
    Φ.extend a ≤ Φ.extend b :=
  iSup_mono fun k => iSup_mono fun m => by
    exact_mod_cast Φ.mono (truncate_mono h k m)

/-- **The low end of the scale**: every entry is bounded by the gauge.

This is the direction that needs `single_one`, hence `normalized'` and `symm'`
together: the truncation dominates the single basis vector at `n`, and that
vector's gauge is its value. -/
theorem le_extend (a : ℕ → ℝ≥0∞) (n : ℕ) : a n ≤ Φ.extend a := by
  refine ENNReal.le_of_forall_nnreal_lt fun c hc => ?_
  -- Capping at `c` leaves the `n`-th entry equal to `c`, because `c < a n`.
  have hmin : min (a n) ((c : ℝ≥0∞)) = (c : ℝ≥0∞) := min_eq_right hc.le
  have hsingle : Finsupp.single n c ≤ truncate a (n + 1) c := by
    refine Finsupp.le_def.2 fun j => ?_
    rcases eq_or_ne j n with rfl | hj
    · simp [hmin]
    · simp [Ne.symm hj]
  calc (c : ℝ≥0∞) = ((Φ (Finsupp.single n c) : ℝ≥0) : ℝ≥0∞) := by rw [Φ.single]
    _ ≤ ((Φ (truncate a (n + 1) c) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast Φ.mono hsingle
    _ ≤ Φ.extend a :=
        le_iSup_of_le (n + 1) (le_iSup (fun m : ℝ≥0 =>
          ((Φ (truncate a (n + 1) m) : ℝ≥0) : ℝ≥0∞)) c)

/-- **The low end, packaged**: `‖a‖_∞ ≤ Φ∞ a`. -/
theorem iSup_le_extend (a : ℕ → ℝ≥0∞) : (⨆ n, a n) ≤ Φ.extend a :=
  iSup_le (Φ.le_extend a)

/-- Subadditivity over a finitely supported sequence: `Φ f ≤ ∑ fₙ`.

Induction on the support, with `add_le'` at each step and `single` at the leaves.
This is the finite half of the high end of the scale. -/
theorem le_sum (f : ℕ →₀ ℝ≥0) : Φ f ≤ f.sum fun _ v => v := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add n b g hng hb ih =>
      rw [Finsupp.sum_add_index' (by simp) (by simp)]
      refine (Φ.add_le _ _).trans ?_
      gcongr
      simp [Finsupp.sum_single_index]

/-- **The high end of the scale**: `Φ∞ a ≤ ∑ aₙ`.

Every truncation is termwise below `a`, so its gauge is below the corresponding
partial sum, which is below the whole sum. -/
theorem extend_le_tsum (a : ℕ → ℝ≥0∞) : Φ.extend a ≤ ∑' n, a n := by
  refine iSup_le fun k => iSup_le fun m => ?_
  have hle : ((Φ (truncate a k m) : ℝ≥0) : ℝ≥0∞)
      ≤ ((truncate a k m).sum fun _ v => v : ℝ≥0) := by
    exact_mod_cast Φ.le_sum (truncate a k m)
  refine hle.trans ?_
  rw [Finsupp.sum, ENNReal.ofNNReal_finsetSum]
  refine (Finset.sum_le_sum fun n _ => ?_).trans (ENNReal.sum_le_tsum _)
  simp only [truncate_apply]
  split
  · exact (ENNReal.coe_toNNReal (ne_top_of_le_ne_top
      (ENNReal.coe_ne_top (r := m)) (min_le_right _ _))).le.trans (min_le_left _ _)
  · simp

/-- **Both ends of the scale**, and the reason the normalization is not a
restriction: `‖a‖_∞ ≤ Φ∞ a ≤ ∑ aₙ`. -/
theorem iSup_le_extend_le_tsum (a : ℕ → ℝ≥0∞) :
    (⨆ n, a n) ≤ Φ.extend a ∧ Φ.extend a ≤ ∑' n, a n :=
  ⟨Φ.iSup_le_extend a, Φ.extend_le_tsum a⟩

/-- The extension of the zero sequence is zero. -/
@[simp] theorem extend_zero : Φ.extend (fun _ => 0) = 0 := by
  simp [extend, show ∀ k m, truncate (fun _ : ℕ => (0 : ℝ≥0∞)) k m = 0 from
    fun k m => by ext n; simp]

/-- The extension of the everywhere-infinite sequence is `∞`.

Worth stating because it is the property `extend` was built as a supremum to
have: a definition routed through `tsum` would need the sequence summable before
it said anything, and would then say nothing here. -/
@[simp] theorem extend_top : Φ.extend (fun _ => ⊤) = ⊤ := by
  refine top_le_iff.1 ?_
  refine le_trans ?_ (Φ.iSup_le_extend (fun _ => ⊤))
  simp

/-! ### Homogeneity — not proved here

`extend_smul`, `Φ∞ (c • a) = c * Φ∞ a`, is the remaining input
`symmetricGaugeFamily.gauge_smul` needs, and it is **harder than the finite
`smul'` field it lifts**.  The obstruction is the cap: `truncate` caps in
`ℝ≥0∞` before converting, so scaling by `c` has to be matched by scaling the cap,
and the two suprema then range over `m` and `m / c`.  That is true but it needs
`min` to commute with multiplication in `ℝ≥0∞` at `c ≠ 0, ∞`, which Mathlib does
not appear to state directly.

Recorded rather than half-proved: `{lane:FTC-SYMGAUGE}` slice 2 needs it, and an
`extend_smul` that only holds for `c ≠ 0` because nobody checked the edge is
worse than none.
-/

end SymmetricGauge

end TauCeti
