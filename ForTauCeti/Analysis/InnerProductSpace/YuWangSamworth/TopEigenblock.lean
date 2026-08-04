/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BasisDiagonal
public import ForTauCeti.Analysis.InnerProductSpace.EigenblockSpan
public import ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics

/-! # Constructing the corresponding-eigenblock hypothesis

`TauCeti.CorrespondingEigenblock` is the branch-selection datum of the
Yu--Wang--Samworth population-gap theorems: the population block `U` and the
perturbed block `V` are spanned by the *same ordered indices* of the two sorted
eigenvector bases.  Every theorem in
`ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Statistics.lean` consumes
it, and until this file nothing produced one — the hypothesis had no instance
anywhere in the repository, so no concrete pair of covariance operators had ever
been checked against it.

`correspondingEigenblock_topEigenspace` supplies the case the statistical
literature actually uses: `U` and `V` are the *leading eigenspaces* of `A` and
`B`, and they correspond because "leading" is the same initial segment of
indices for both once the eigenvalues are sorted.  The only inputs are spectral
facts a reader can check on a concrete operator — an upper bound attained, and
its multiplicity.

## Main results

* `TauCeti.correspondingEigenblock_topEigenspace`: leading eigenspaces of equal
  multiplicity correspond.
* `TauCeti.correspondingEigenblock_basisDiagonal`: the same for two operators
  presented diagonally, with the hypotheses reduced to arithmetic on the data.
-/

public section

open Module (finrank)
open Module.End (eigenspace)

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Leading eigenspaces of equal multiplicity are corresponding eigenblocks.**

If `α` bounds every eigenvalue of `A` and `β` bounds every eigenvalue of `B`,
and both attained eigenspaces have dimension `d`, then those eigenspaces are
selected by the same index set `{i | i < d}` in the two sorted eigenvector
bases — which is exactly `CorrespondingEigenblock`. -/
theorem correspondingEigenblock_topEigenspace {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n)
    {α β : ℝ} {d : ℕ}
    (hAmax : ∀ i, hA.eigenvalues hn i ≤ α)
    (hAmult : finrank 𝕜 (eigenspace A (α : 𝕜)) = d)
    (hBmax : ∀ i, hB.eigenvalues hn i ≤ β)
    (hBmult : finrank 𝕜 (eigenspace B (β : 𝕜)) = d) :
    CorrespondingEigenblock hA hB (eigenspace A (α : 𝕜))
      (eigenspace B (β : 𝕜)) := by
  classical
  refine correspondingEigenblock_of_spanIndices hn {i : Fin n | (i : ℕ) < d} ?_ ?_
  · rw [← hA.spanIndices_Iio_eq_topEigenspace hn hAmax hAmult]
    congr 1
    ext i
    simp
  · rw [← hB.spanIndices_Iio_eq_topEigenspace hn hBmax hBmult]
    congr 1
    ext i
    simp

open scoped Classical in
/-- **The diagonal case.**  For operators presented in orthonormal bases the
hypotheses of `correspondingEigenblock_topEigenspace` become arithmetic: `α` and
`β` bound the coefficient lists, and the two level sets have `d` elements. -/
theorem correspondingEigenblock_basisDiagonal {n : ℕ}
    (b b' : OrthonormalBasis (Fin n) 𝕜 E) (c c' : Fin n → ℝ)
    (hn : finrank 𝕜 E = n) {α β : ℝ} {d : ℕ}
    (hc : ∀ i, c i ≤ α) (hc' : ∀ i, c' i ≤ β)
    (hcard : ({i | (c i : 𝕜) = (α : 𝕜)} : Finset (Fin n)).card = d)
    (hcard' : ({i | (c' i : 𝕜) = (β : 𝕜)} : Finset (Fin n)).card = d) :
    CorrespondingEigenblock (isSymmetric_basisDiagonal b c)
      (isSymmetric_basisDiagonal b' c')
      (eigenspace (basisDiagonal b c) (α : 𝕜))
      (eigenspace (basisDiagonal b' c') (β : 𝕜)) :=
  correspondingEigenblock_topEigenspace _ _ hn
    (eigenvalues_basisDiagonal_le b c hc hn)
    (by rw [finrank_eigenspace_basisDiagonal, hcard])
    (eigenvalues_basisDiagonal_le b' c' hc' hn)
    (by rw [finrank_eigenspace_basisDiagonal, hcard'])

end TauCeti
