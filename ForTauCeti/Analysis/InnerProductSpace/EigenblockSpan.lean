/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`,
next to `LinearMap.IsSymmetric.eigenvectorBasis`.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BasisSpan
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Identifying spans of the sorted eigenvector basis with eigenspaces

Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` is a *choice* of orthonormal
eigenbasis, sorted by decreasing eigenvalue.  Statements phrased as
`(hT.eigenvectorBasis hn).spanIndices s` are therefore easy to consume and hard
to *produce*: a reader with a concrete operator in hand knows its eigenspaces,
not Mathlib's internal diagonalization.

This file supplies the missing direction.  The span of the basis vectors at a
level set of the eigenvalue function is the corresponding eigenspace
(`spanIndices_eigenvalueLevel`), which is canonical even though the basis is
not; and because the eigenvalues are sorted, the level set of the *largest*
eigenvalue is the initial segment `{i | i < d}` where `d` is that eigenvalue's
multiplicity (`eigenvalues_top_level_eq_Iio`).  Together these identify the
paper-facing "top-`d` eigenspace" with a `spanIndices` block
(`spanIndices_Iio_eq_topEigenspace`).

## Main results

* `LinearMap.IsSymmetric.spanIndices_eigenvalueLevel`: the span of the
  eigenbasis vectors whose eigenvalue is `μ` is `eigenspace T μ`.
* `LinearMap.IsSymmetric.eigenvalues_top_level_eq_Iio`: the index set of the
  largest eigenvalue is an initial segment of length its multiplicity.
* `LinearMap.IsSymmetric.spanIndices_Iio_eq_topEigenspace`: the top-`d`
  `spanIndices` block is the top eigenspace, when `d` is its multiplicity.
-/

public section

open Module (finrank)
open Module.End (eigenspace)

namespace LinearMap.IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- **The span of an eigenvalue level set is the eigenspace.**

`hT.eigenvectorBasis hn` is only one of many orthonormal eigenbases, but the
span of the vectors sharing a given eigenvalue does not depend on the choice:
it is `eigenspace T μ`.  This is what makes a `spanIndices` hypothesis
constructible from concrete spectral data.

The inclusion `⊆` is immediate from `hasEigenvector_eigenvectorBasis`; the
reverse is a dimension count, since `card_filter_eigenvalues_eq` says the level
set has exactly `finrank 𝕜 (eigenspace T μ)` elements. -/
theorem spanIndices_eigenvalueLevel (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (μ : 𝕜) :
    (hT.eigenvectorBasis hn).spanIndices {i | (hT.eigenvalues hn i : 𝕜) = μ} =
      eigenspace T μ := by
  classical
  have hle :
      (hT.eigenvectorBasis hn).spanIndices {i | (hT.eigenvalues hn i : 𝕜) = μ} ≤
        eigenspace T μ := by
    rw [OrthonormalBasis.spanIndices_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    have := (hT.hasEigenvector_eigenvectorBasis hn i).1
    rwa [(by exact hi : (hT.eigenvalues hn i : 𝕜) = μ)] at this
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_)
  rw [OrthonormalBasis.finrank_spanIndices_set]
  rw [← hT.card_filter_eigenvalues_eq hn μ]
  congr 1
  ext i
  simp

/-- **A downward-closed subset of `Fin n` is the initial segment of its own
length.**  The counting step behind `eigenvalues_top_level_eq_Iio`, isolated
because it has nothing to do with operators. -/
private theorem mem_iff_lt_card_of_lower {n : ℕ} {s : Finset (Fin n)}
    (hs : ∀ {i j : Fin n}, i ≤ j → j ∈ s → i ∈ s) (i : Fin n) :
    i ∈ s ↔ (i : ℕ) < s.card := by
  classical
  constructor
  · intro hi
    -- Everything at or below `i` lies in `s`, and there are `i + 1` such indices.
    have hIic : Finset.Iic i ⊆ s := fun j hj => hs (Finset.mem_Iic.mp hj) hi
    have := Finset.card_le_card hIic
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hi
    -- If `i ∉ s` then `s` cannot reach `i`, so `s ⊆ Iio i`.
    have hIio : s ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hi (hs (not_lt.mp hji) hj)
    have := Finset.card_le_card hIio
    rw [Fin.card_Iio] at this
    omega

/-- **The largest eigenvalue occupies an initial segment of indices.**

`hT.eigenvalues hn` is antitone, so the level set of a value that no eigenvalue
exceeds is downward closed; a downward-closed subset of `Fin n` is determined by
its cardinality, which `card_filter_eigenvalues_eq` identifies as the geometric
multiplicity. -/
theorem eigenvalues_top_level_eq_Iio (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    {μ : ℝ} (hmax : ∀ i, hT.eigenvalues hn i ≤ μ) :
    {i : Fin n | hT.eigenvalues hn i = μ} =
      {i : Fin n | (i : ℕ) < finrank 𝕜 (eigenspace T (μ : 𝕜))} := by
  classical
  -- The level set, as a `Finset`, has cardinality the geometric multiplicity.
  have hcard : ({i : Fin n | hT.eigenvalues hn i = μ} : Finset (Fin n)).card =
      finrank 𝕜 (eigenspace T (μ : 𝕜)) := by
    rw [← hT.card_filter_eigenvalues_eq hn (μ : 𝕜)]
    congr 1
    ext i
    simp
  -- It is downward closed: below a maximizer the antitone function cannot drop.
  have hlower : ∀ {i j : Fin n}, i ≤ j →
      j ∈ ({i : Fin n | hT.eigenvalues hn i = μ} : Finset (Fin n)) →
      i ∈ ({i : Fin n | hT.eigenvalues hn i = μ} : Finset (Fin n)) := by
    intro i j hij hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact le_antisymm (hmax i) (hj ▸ hT.eigenvalues_antitone hn hij)
  ext i
  have := mem_iff_lt_card_of_lower hlower i
  rw [hcard] at this
  simpa using this

/-- **The top-`d` block of the sorted eigenbasis is the top eigenspace.**

This is the bridge the statistical Davis--Kahan literature needs: the paper's
"leading `d` eigenvectors" is a `spanIndices` block over the initial segment,
and it equals the eigenspace of the largest eigenvalue exactly when `d` is that
eigenvalue's multiplicity. -/
theorem spanIndices_Iio_eq_topEigenspace (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {μ : ℝ} {d : ℕ} (hmax : ∀ i, hT.eigenvalues hn i ≤ μ)
    (hmult : finrank 𝕜 (eigenspace T (μ : 𝕜)) = d) :
    (hT.eigenvectorBasis hn).spanIndices {i : Fin n | (i : ℕ) < d} =
      eigenspace T (μ : 𝕜) := by
  rw [← hmult, ← hT.eigenvalues_top_level_eq_Iio hn hmax]
  rw [← hT.spanIndices_eigenvalueLevel hn (μ : 𝕜)]
  congr 1
  ext i
  simp

end LinearMap.IsSymmetric
