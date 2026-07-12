/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Positive
import ForMathlib.Analysis.InnerProductSpace.CourantFischer

/-!
# Rectangular singular values and adjoint-product spectra

> **Comparison variant — not preferred, not built.** This is the `dk-work`-branch proof of the
> rectangular adjoint-spectrum layer (GPT-5.6 High), preserved **verbatim** for side-by-side
> comparison of proof strategy. It is intentionally **not** imported by `ForMathlib.lean`.
> The **preferred** implementation — the one the Perfect Quench build depends on — is the
> sibling file `RectangularSingularValues.lean` (Claude Fable 5).
>
> The two proofs share the same public API and differ in only three spots: this variant marks
> `eigenvalues_congr'` `private` (the preferred file keeps it public because `FiniteFrame` and
> `GramSpectrumBridge` reference `ForMathlib.eigenvalues_congr'`), and it uses `calc`/compact
> proof forms in `sq_singularValues_selfCompAdjoint` and
> `hasEigenvalue_selfCompAdjoint_sq_singularValues`.
>
> WARNING: this variant does **not** elaborate on the pinned toolchain — the `calc` form of
> `sq_singularValues_selfCompAdjoint` provokes a `whnf` heartbeat blow-up that does not clear
> even at `maxHeartbeats 1000000`. That is precisely why the preferred file rewrote the proof.
> This file is kept as a readable record of the alternative approach, not as a build target.

For a linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner-product spaces, the two
Gram operators `A†A` (on `E`) and `AA†` (on `F`) share their nonzero spectrum, including
multiplicity.  Mathlib defines the zero-padded singular-value sequence
`LinearMap.singularValues` through `A†A` only; this file supplies the canonical bridge to the
codomain-side Gram operator.

## Main results

* `ForMathlib.nonzeroEigenspaceEquivAdjointCompSelfSelfCompAdjoint`: the linear equivalence
  `x ↦ A x` (inverse `y ↦ μ⁻¹ • A† y`) between the nonzero `μ`-eigenspaces of `A†A` and `AA†`;
* `ForMathlib.eigenvalues_adjointCompSelf_eq_selfCompAdjoint`: the sorted eigenvalue lists of
  `A†A` and `AA†` agree at every index below both dimensions;
* `LinearMap.singularValues_adjoint`: zero-padded adjoint invariance
  `A†.singularValues = A.singularValues`;
* `ForMathlib.sq_singularValues_selfCompAdjoint`: the sorted eigenvalues of `AA†` are the
  squared singular values of `A`, zero-padded past the rank;
* `ForMathlib.le_eigenvalues_selfCompAdjoint_of_norm_sq_floor`: a quadratic floor
  `α‖x‖² ≤ ‖Ax‖²` forces the first `finrank 𝕜 E` sorted eigenvalues of `AA†` to be at least
  `α`, and `ForMathlib.norm_sq_floor_of_le_eigenvalues_adjointCompSelf` is the converse
  direction used to descend from spectral floors back to quadratic floors.

The combinatorial engine is `ForMathlib.antitone_eq_of_card_filter_eq`: two antitone
nonnegative finite sequences with equal fiber cardinalities over every nonzero value agree at
every index where both are defined.

## Proof sources

The eigenspace equivalence and the counting argument are original to this file.  The vendored
Apache-2.0 excerpt `vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean`
(Zhang–Lee–Liu) constructs explicit left singular vectors for Euclidean matrix maps and was
consulted as a cross-check for the spectral bookkeeping; no code was copied from it here.
-/

namespace ForMathlib

open Module LinearMap Finset
open scoped InnerProductSpace

/-! ### Sorted sequences determined by fiber cardinalities

Pure finite combinatorics: an antitone nonnegative sequence is determined below any index by
the cardinalities of its positive fibers. -/

section Counting

/-- For an antitone real sequence on `Fin d`, the `k`-th entry is at least `c` exactly when
more than `k` entries are at least `c`. -/
theorem antitone_le_apply_iff_lt_card_filter {d : ℕ} {f : Fin d → ℝ} (hf : Antitone f)
    (c : ℝ) (k : Fin d) :
    c ≤ f k ↔ (k : ℕ) < #{i | c ≤ f i} := by
  constructor
  · intro hc
    have hsub : Finset.Iic k ⊆ ({i | c ≤ f i} : Finset (Fin d)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.trans (hf hj)⟩
    calc (k : ℕ) < #(Finset.Iic k) := by rw [Fin.card_Iic]; omega
      _ ≤ _ := Finset.card_le_card hsub
  · intro hcard
    by_contra hc
    have hsub : ({i | c ≤ f i} : Finset (Fin d)) ⊆ Finset.Iio k := by
      intro j hj
      rw [Finset.mem_Iio]
      by_contra hjk
      exact hc (((Finset.mem_filter.mp hj).2).trans (hf (le_of_not_gt hjk)))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- If two real sequences have fibers of equal cardinality over every nonzero value, their
super-level sets over every positive threshold have equal cardinality. -/
theorem card_filter_le_eq_of_card_filter_eq {d n : ℕ} {f : Fin d → ℝ} {g : Fin n → ℝ}
    (hcard : ∀ c : ℝ, c ≠ 0 → #{i | f i = c} = #{j | g j = c})
    {c : ℝ} (hc : 0 < c) :
    #{i | c ≤ f i} = #{j | c ≤ g j} := by
  classical
  set V : Finset ℝ := {v ∈ Finset.univ.image f ∪ Finset.univ.image g | c ≤ v} with hV
  have hfib : ∀ {m : ℕ} (v : Fin m → ℝ),
      (∀ i, v i ∈ Finset.univ.image f ∪ Finset.univ.image g) →
      #{i | c ≤ v i} = ∑ w ∈ V, #{i | v i = w} := by
    intro m v hv
    rw [Finset.card_eq_sum_card_fiberwise (f := v) (t := V)
      (fun i hi => Finset.mem_filter.mpr ⟨hv i, (Finset.mem_filter.mp hi).2⟩)]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hcw : c ≤ w := (Finset.mem_filter.mp hw).2
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hcw, h⟩⟩
  have hmemf : ∀ i, f i ∈ Finset.univ.image f ∪ Finset.univ.image g := fun i =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ i))
  have hmemg : ∀ j, g j ∈ Finset.univ.image f ∪ Finset.univ.image g := fun j =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ j))
  rw [hfib f hmemf, hfib g hmemg]
  refine Finset.sum_congr rfl fun w hw => ?_
  exact hcard w (ne_of_gt (hc.trans_le (Finset.mem_filter.mp hw).2))

private theorem le_apply_of_card_filter_eq {d n : ℕ} {f : Fin d → ℝ} {g : Fin n → ℝ}
    (hf : Antitone f) (hg : Antitone g) (hg0 : ∀ j, 0 ≤ g j)
    (hcard : ∀ c : ℝ, c ≠ 0 → #{i | f i = c} = #{j | g j = c})
    {k : ℕ} (hkd : k < d) (hkn : k < n) :
    f ⟨k, hkd⟩ ≤ g ⟨k, hkn⟩ := by
  by_contra hlt
  push Not at hlt
  set c : ℝ := f ⟨k, hkd⟩ with hc
  have hcpos : 0 < c := (hg0 ⟨k, hkn⟩).trans_lt hlt
  have h1 : (k : ℕ) < #{i | c ≤ f i} :=
    (antitone_le_apply_iff_lt_card_filter hf c ⟨k, hkd⟩).mp le_rfl
  rw [card_filter_le_eq_of_card_filter_eq hcard hcpos] at h1
  exact absurd ((antitone_le_apply_iff_lt_card_filter hg c ⟨k, hkn⟩).mpr h1) (not_le.mpr hlt)

/-- Two antitone nonnegative finite real sequences with equal fiber cardinalities over every
nonzero value agree at every index where both are defined.  The zero fibers may have different
cardinalities: they absorb the length difference of the two sequences. -/
theorem antitone_eq_of_card_filter_eq {d n : ℕ} {f : Fin d → ℝ} {g : Fin n → ℝ}
    (hf : Antitone f) (hg : Antitone g) (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ j, 0 ≤ g j)
    (hcard : ∀ c : ℝ, c ≠ 0 → #{i | f i = c} = #{j | g j = c})
    {k : ℕ} (hkd : k < d) (hkn : k < n) :
    f ⟨k, hkd⟩ = g ⟨k, hkn⟩ :=
  le_antisymm
    (le_apply_of_card_filter_eq hf hg hg0 hcard hkd hkn)
    (le_apply_of_card_filter_eq hg hf hf0 (fun c hc => (hcard c hc).symm) hkn hkd)

end Counting

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### The nonzero eigenspace equivalence between `A†A` and `AA†` -/

/-- The codomain Gram operator `AA†` is symmetric. -/
theorem isSymmetric_self_comp_adjoint (A : E →ₗ[𝕜] F) : (A ∘ₗ A.adjoint).IsSymmetric :=
  A.isPositive_self_comp_adjoint.isSymmetric

/-- `A` maps each eigenspace of `A†A` into the same eigenspace of `AA†`. -/
theorem apply_mem_eigenspace_selfCompAdjoint (A : E →ₗ[𝕜] F) {μ : 𝕜} {x : E}
    (hx : x ∈ Module.End.eigenspace (A.adjoint.comp A) μ) :
    A x ∈ Module.End.eigenspace (A.comp A.adjoint) μ := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  calc (A.comp A.adjoint) (A x) = A ((A.adjoint.comp A) x) := rfl
    _ = μ • A x := by rw [hx, map_smul]

/-- `A†` maps each eigenspace of `AA†` into the same eigenspace of `A†A`. -/
theorem adjoint_apply_mem_eigenspace_adjointCompSelf (A : E →ₗ[𝕜] F) {μ : 𝕜} {y : F}
    (hy : y ∈ Module.End.eigenspace (A.comp A.adjoint) μ) :
    A.adjoint y ∈ Module.End.eigenspace (A.adjoint.comp A) μ := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  calc (A.adjoint.comp A) (A.adjoint y) = A.adjoint ((A.comp A.adjoint) y) := rfl
    _ = μ • A.adjoint y := by rw [hy, map_smul]

/-- The nonzero `μ`-eigenspaces of `A†A` and `AA†` are linearly equivalent, via `x ↦ A x`
with inverse `y ↦ μ⁻¹ • A† y`.  This is the multiplicity-preserving form of the statement
that `A†A` and `AA†` have the same nonzero spectrum. -/
noncomputable def nonzeroEigenspaceEquivAdjointCompSelfSelfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.eigenspace (A.adjoint.comp A) μ ≃ₗ[𝕜]
      Module.End.eigenspace (A.comp A.adjoint) μ := by
  refine LinearEquiv.ofLinear
    (A.restrict fun x hx => apply_mem_eigenspace_selfCompAdjoint A hx)
    ((μ⁻¹ • A.adjoint).restrict fun y hy => Submodule.smul_mem _ _
      (adjoint_apply_mem_eigenspace_adjointCompSelf A hy)) ?_ ?_
  · ext y
    have hy := y.2
    rw [Module.End.mem_eigenspace_iff] at hy
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply]
    calc A (μ⁻¹ • A.adjoint y.1) = μ⁻¹ • (A.comp A.adjoint) y.1 := by
          rw [map_smul]; rfl
      _ = μ⁻¹ • μ • y.1 := by rw [hy]
      _ = y.1 := inv_smul_smul₀ hμ y.1
  · ext x
    have hx := x.2
    rw [Module.End.mem_eigenspace_iff] at hx
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply]
    calc μ⁻¹ • A.adjoint (A x.1) = μ⁻¹ • (A.adjoint.comp A) x.1 := rfl
      _ = μ⁻¹ • μ • x.1 := by rw [hx]
      _ = x.1 := inv_smul_smul₀ hμ x.1

/-- Corresponding nonzero eigenspaces of `A†A` and `AA†` have equal dimension. -/
theorem finrank_eigenspace_adjointCompSelf_eq_selfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    finrank 𝕜 (Module.End.eigenspace (A.adjoint.comp A) μ) =
      finrank 𝕜 (Module.End.eigenspace (A.comp A.adjoint) μ) :=
  (nonzeroEigenspaceEquivAdjointCompSelfSelfCompAdjoint A μ hμ).finrank_eq

/-- A nonzero scalar is an eigenvalue of `A†A` exactly when it is an eigenvalue of `AA†`. -/
theorem hasEigenvalue_adjointCompSelf_iff_selfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (A.adjoint.comp A) μ ↔
      Module.End.HasEigenvalue (A.comp A.adjoint) μ := by
  have h := finrank_eigenspace_adjointCompSelf_eq_selfCompAdjoint A μ hμ
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff, ne_eq, ne_eq,
    ← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, h]

/-! ### Equality of the sorted nonzero spectra -/

private theorem eigenvalues_congr' {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] {S₁ S₂ : G →ₗ[𝕜] G} (h : S₁ = S₂)
    (hS₁ : S₁.IsSymmetric) (hS₂ : S₂.IsSymmetric) {m : ℕ} (hm : finrank 𝕜 G = m) :
    hS₁.eigenvalues hm = hS₂.eigenvalues hm := by
  subst h; rfl

private theorem card_filter_eigenvalues_real_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] {S : G →ₗ[𝕜] G} (hS : S.IsSymmetric)
    {m : ℕ} (hm : finrank 𝕜 G = m) (c : ℝ) :
    #{i | hS.eigenvalues hm i = c} =
      finrank 𝕜 (Module.End.eigenspace S ((c : ℝ) : 𝕜)) := by
  rw [← hS.card_filter_eigenvalues_eq hm ((c : ℝ) : 𝕜)]
  congr 1
  ext i
  simp

/-- For every nonzero real value, the sorted eigenvalue lists of `A†A` and `AA†` have fibers
of equal cardinality. -/
theorem card_filter_eigenvalues_adjointCompSelf_eq_selfCompAdjoint
    (A : E →ₗ[𝕜] F) {d n : ℕ} (hd : finrank 𝕜 E = d) (hn : finrank 𝕜 F = n)
    {c : ℝ} (hc : c ≠ 0) :
    #{i : Fin d | A.isSymmetric_adjoint_comp_self.eigenvalues hd i = c} =
      #{j : Fin n | (isSymmetric_self_comp_adjoint A).eigenvalues hn j = c} := by
  have hμ : ((c : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hc
  rw [card_filter_eigenvalues_real_eq A.isSymmetric_adjoint_comp_self hd c,
    card_filter_eigenvalues_real_eq (isSymmetric_self_comp_adjoint A) hn c]
  exact finrank_eigenspace_adjointCompSelf_eq_selfCompAdjoint A ((c : ℝ) : 𝕜) hμ

/-- **Rectangular spectral bridge.**  The sorted (descending) eigenvalue lists of `A†A` and
`AA†` agree at every index below both space dimensions.  Beyond the rank of `A` both lists
are zero, so no hypothesis relating `d` and `n` is required. -/
theorem eigenvalues_adjointCompSelf_eq_selfCompAdjoint
    (A : E →ₗ[𝕜] F) {d n : ℕ} (hd : finrank 𝕜 E = d) (hn : finrank 𝕜 F = n)
    {k : ℕ} (hkd : k < d) (hkn : k < n) :
    A.isSymmetric_adjoint_comp_self.eigenvalues hd ⟨k, hkd⟩ =
      (isSymmetric_self_comp_adjoint A).eigenvalues hn ⟨k, hkn⟩ :=
  antitone_eq_of_card_filter_eq
    (A.isSymmetric_adjoint_comp_self.eigenvalues_antitone hd)
    ((isSymmetric_self_comp_adjoint A).eigenvalues_antitone hn)
    (A.isPositive_adjoint_comp_self.nonneg_eigenvalues hd)
    (A.isPositive_self_comp_adjoint.nonneg_eigenvalues hn)
    (fun _ hc => card_filter_eigenvalues_adjointCompSelf_eq_selfCompAdjoint A hd hn hc)
    hkd hkn

/-! ### Adjoint invariance of singular values -/

/-- Singular values are invariant under adjoint.  Both sequences are zero-padded past the
common rank, so the statement needs no relation between the two dimensions. -/
theorem _root_.LinearMap.singularValues_adjoint (A : E →ₗ[𝕜] F) :
    A.adjoint.singularValues = A.singularValues := by
  ext k
  rcases lt_or_ge k (finrank 𝕜 F) with hkn | hkn
  · rcases lt_or_ge k (finrank 𝕜 E) with hkd | hkd
    · have h3 : A.adjoint.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨k, hkn⟩ =
          (isSymmetric_self_comp_adjoint A).eigenvalues rfl ⟨k, hkn⟩ :=
        congrFun (eigenvalues_congr' (by rw [adjoint_adjoint])
          A.adjoint.isSymmetric_adjoint_comp_self (isSymmetric_self_comp_adjoint A) rfl) _
      rw [A.adjoint.singularValues_of_lt rfl hkn, A.singularValues_of_lt rfl hkd, h3,
        ← eigenvalues_adjointCompSelf_eq_selfCompAdjoint A rfl rfl hkd hkn]
    · have h1 : A.adjoint.singularValues k = 0 :=
        A.adjoint.singularValues_eq_zero_iff_le_finrank_range.mpr
          (by rw [finrank_range_adjoint]; exact A.finrank_range_le.trans hkd)
      rw [h1, A.singularValues_of_finrank_le hkd]
  · have h1 : A.singularValues k = 0 :=
      A.singularValues_eq_zero_iff_le_finrank_range.mpr
        ((Submodule.finrank_le A.range).trans hkn)
    rw [h1, A.adjoint.singularValues_of_finrank_le hkn]

/-- Pointwise adjoint invariance, convenient for rewriting a fixed index. -/
theorem _root_.LinearMap.singularValues_adjoint_apply (A : E →ₗ[𝕜] F) (k : ℕ) :
    A.adjoint.singularValues k = A.singularValues k := by
  rw [A.singularValues_adjoint]

/-- The sorted eigenvalues of the codomain Gram operator `AA†` are the squared singular
values of `A`, zero-padded past the rank of `A`. -/
theorem sq_singularValues_selfCompAdjoint (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 F = n) (i : Fin n) :
    A.singularValues i ^ 2 = (isSymmetric_self_comp_adjoint A).eigenvalues hn i :=
  calc A.singularValues i ^ 2
      = A.adjoint.singularValues i ^ 2 := by rw [A.singularValues_adjoint_apply]
    _ = A.adjoint.isSymmetric_adjoint_comp_self.eigenvalues hn i :=
        A.adjoint.sq_singularValues_fin hn i
    _ = (isSymmetric_self_comp_adjoint A).eigenvalues hn i :=
        congrFun (eigenvalues_congr' (by rw [adjoint_adjoint])
          A.adjoint.isSymmetric_adjoint_comp_self (isSymmetric_self_comp_adjoint A) hn) i

/-- Every positive squared singular value of `A` is an eigenvalue of `AA†`. -/
theorem hasEigenvalue_selfCompAdjoint_sq_singularValues
    (A : E →ₗ[𝕜] F) {i : ℕ} (hi : i < finrank 𝕜 A.range) :
    Module.End.HasEigenvalue (A.comp A.adjoint) ((A.singularValues i ^ 2 : ℝ) : 𝕜) := by
  have hiE : i < finrank 𝕜 E := hi.trans_le A.finrank_range_le
  have hpos : 0 < A.singularValues i := A.singularValues_pos_iff_lt_finrank_range.mpr hi
  have hne : ((A.singularValues i ^ 2 : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (by positivity)
  exact (hasEigenvalue_adjointCompSelf_iff_selfCompAdjoint A _ hne).mp
    (A.hasEigenvalue_adjoint_comp_self_sq_singularValues hiE)

/-! ### Quadratic floors and Gram spectra -/

/-- The Gram quadratic form is the squared image norm:
`re ⟪(A†A) x, x⟫ = ‖A x‖²`. -/
theorem re_inner_adjointCompSelf_self (A : E →ₗ[𝕜] F) (x : E) :
    RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) x) = ‖A x‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  exact (norm_sq_eq_re_inner (𝕜 := 𝕜) (A x)).symm

/-- A quadratic floor `α‖x‖² ≤ ‖Ax‖²` bounds every sorted eigenvalue of `A†A` below by `α`. -/
theorem le_eigenvalues_adjointCompSelf_of_norm_sq_floor
    (A : E →ₗ[𝕜] F) {α : ℝ} (hfloor : ∀ x, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    {d : ℕ} (hd : finrank 𝕜 E = d) (i : Fin d) :
    α ≤ A.isSymmetric_adjoint_comp_self.eigenvalues hd i := by
  set hS := A.isSymmetric_adjoint_comp_self with hSdef
  set v := hS.eigenvectorBasis hd i with hv
  have hnorm : ‖v‖ = 1 := (hS.eigenvectorBasis hd).orthonormal.1 i
  have hquad : RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) v) v) = hS.eigenvalues hd i := by
    rw [hS.apply_eigenvectorBasis hd i, inner_smul_left, RCLike.conj_ofReal]
    have hvv : inner 𝕜 v v = ((1 : ℝ) : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) v, hnorm]
      norm_num
    rw [hvv, ← RCLike.ofReal_mul, RCLike.ofReal_re, mul_one]
  have := hfloor v
  rw [← re_inner_adjointCompSelf_self A v, hquad, hnorm] at this
  simpa using this

/-- Converse direction: if every sorted eigenvalue of `A†A` is at least `α`, the quadratic
floor `α‖x‖² ≤ ‖Ax‖²` holds. -/
theorem norm_sq_floor_of_le_eigenvalues_adjointCompSelf
    (A : E →ₗ[𝕜] F) {α : ℝ} {d : ℕ} (hd : finrank 𝕜 E = d)
    (hlow : ∀ i : Fin d, α ≤ A.isSymmetric_adjoint_comp_self.eigenvalues hd i)
    (x : E) :
    α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 := by
  set hS := A.isSymmetric_adjoint_comp_self with hSdef
  set b := hS.eigenvectorBasis hd with hb
  have hpars : ∑ i : Fin d, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
    simp_rw [b.repr_apply_apply]
    exact b.sum_sq_norm_inner_right x
  calc α * ‖x‖ ^ 2 = ∑ i : Fin d, α * ‖b.repr x i‖ ^ 2 := by
        rw [← Finset.mul_sum, hpars]
    _ ≤ ∑ i : Fin d, hS.eigenvalues hd i * ‖b.repr x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hlow i) (sq_nonneg _)
    _ = RCLike.re (inner 𝕜 ((A.adjoint ∘ₗ A) x) x) :=
        (re_inner_map_self_eq_sum_eigenvalues_mul_sq hS hd x).symm
    _ = ‖A x‖ ^ 2 := re_inner_adjointCompSelf_self A x

omit [FiniteDimensional 𝕜 E] in
/-- A positive quadratic floor forces injectivity, hence `finrank E ≤ finrank F`. -/
theorem finrank_le_of_norm_sq_floor
    (A : E →ₗ[𝕜] F) {α : ℝ} (hα : 0 < α) (hfloor : ∀ x, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) :
    finrank 𝕜 E ≤ finrank 𝕜 F := by
  refine LinearMap.finrank_le_finrank_of_injective (f := A) ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h1 := hfloor x
  rw [hx, norm_zero] at h1
  have h2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
  have h3 : ‖x‖ = 0 := by nlinarith [norm_nonneg x, sq_nonneg ‖x‖]
  exact norm_eq_zero.mp h3

/-- **Quadratic floor to codomain-Gram spectral floor.**  If `α‖x‖² ≤ ‖Ax‖²` for every `x`,
then the first `finrank 𝕜 E` sorted eigenvalues of `AA†` are at least `α`.  The dimension
comparison `finrank E ≤ finrank F` is not assumed: it is automatic when `α > 0`, and for
`α ≤ 0` the claim follows from positivity of the Gram operator. -/
theorem le_eigenvalues_selfCompAdjoint_of_norm_sq_floor
    (A : E →ₗ[𝕜] F) {α : ℝ} (hfloor : ∀ x, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    {n : ℕ} (hn : finrank 𝕜 F = n) (i : Fin n) (hi : (i : ℕ) < finrank 𝕜 E) :
    α ≤ (isSymmetric_self_comp_adjoint A).eigenvalues hn i := by
  rcases le_or_gt α 0 with hα | hα
  · exact hα.trans (A.isPositive_self_comp_adjoint.nonneg_eigenvalues hn i)
  · rw [← eigenvalues_adjointCompSelf_eq_selfCompAdjoint A rfl hn hi i.2]
    exact le_eigenvalues_adjointCompSelf_of_norm_sq_floor A hfloor rfl ⟨i, hi⟩

end ForMathlib
