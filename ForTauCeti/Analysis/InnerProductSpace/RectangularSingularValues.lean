/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# Quadratic floors and rectangular Gram operators

TauCeti supplies the eigenspace equivalence for the two compositions and the sorted
source and target Gram spectra in `Module.End.eigenspaceCompEquiv` and
`TauCeti.Analysis.InnerProductSpace.SingularValues`. The results here relate spectral
floors of those Gram operators to pointwise quadratic floors and compare the singular
values of maps with identical Gram operators.

The counting lemmas cover antitone tuples of different lengths with equal nonzero
fiber counts.

## Provenance

Extracted from `ForMathlib.Analysis.InnerProductSpace.RectangularSingularValues`
at DKPS commit `82d20de`. Authors Jon Crall, GPT-5.6 High and Claude Fable 5,
Kitware copyright, Apache-2.0. The previous eigenspace equivalence and sorted
Gram-spectrum proofs are in Git history. The independently implemented
TauCeti #13839 now supplies those results.
-/

public section

namespace TauCeti

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
        (LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hS hd x).symm
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
    α ≤ A.isSymmetric_self_comp_adjoint.eigenvalues hn i := by
  rcases le_or_gt α 0 with hα | hα
  · exact hα.trans (A.isPositive_self_comp_adjoint.nonneg_eigenvalues hn i)
  · rw [← A.eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint rfl hn hi i.isLt]
    exact le_eigenvalues_adjointCompSelf_of_norm_sq_floor A hfloor rfl ⟨i, hi⟩

/-- Singular values only depend on the Gram operator. -/
theorem singularValues_eq_of_gram_eq {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F'] {A : E →ₗ[𝕜] F} {B : E →ₗ[𝕜] F'}
    (h : A.adjoint ∘ₗ A = B.adjoint ∘ₗ B) : A.singularValues = B.singularValues := by
  ext i
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  · rw [A.singularValues_of_lt rfl hi, B.singularValues_of_lt rfl hi]
    congr 1
    exact congrFun (LinearMap.IsSymmetric.eigenvalues_congr h A.isSymmetric_adjoint_comp_self
      B.isSymmetric_adjoint_comp_self rfl) _
  · rw [A.singularValues_of_finrank_le hi, B.singularValues_of_finrank_le hi]

end TauCeti
