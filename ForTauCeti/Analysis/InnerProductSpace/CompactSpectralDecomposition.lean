/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues

/-!
# Spectral decomposition of compact self-adjoint operators

A compact self-adjoint operator on a real or complex Hilbert space is the Hilbert sum of its
mutually orthogonal eigenspaces.  For a compact positive operator, the positive eigenvalues are
exactly the positive values of its approximation-number sequence.

The eigenspace Hilbert sum is the coordinate-free spectral decomposition.  It includes the kernel
as the zero eigenspace and therefore applies without an injectivity assumption or a separability
assumption on the ambient Hilbert space.  Compactness makes every nonzero eigenspace finite
dimensional; the zero eigenspace may have arbitrary Hilbert dimension.

## Main results

* `TauCeti.isHilbertSum_eigenspaces_of_compact_selfAdjoint`: the eigenspaces form a Hilbert sum.
* `TauCeti.compactSelfAdjointEigenspaceEquiv`: the canonical isometric equivalence from the
  ambient space to the `ℓ²`-sum of its eigenspaces.
* `TauCeti.compactSelfAdjointEigenspaceEquiv_apply`: the equivalence sends an eigenvector to the
  corresponding one-coordinate vector.
* `TauCeti.hasEigenvalue_approximationNumber_of_pos`: every positive approximation-number value of
  a compact positive self-adjoint operator is an eigenvalue.
* `TauCeti.exists_approximationNumber_eq_of_hasEigenvalue_pos`: every positive eigenvalue occurs in
  the approximation-number sequence.
* `TauCeti.hasEigenvalue_ofReal_pos_iff_exists_approximationNumber_eq`: the positive spectrum is
  exactly the range of the positive approximation-number sequence.

Together with `TauCeti.finrank_eigenspace_eq_card_approximationNumber_eq`, the last statement says
that approximation numbers enumerate the positive eigenvalues with their full multiplicities.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section SelfAdjoint

variable {A : E →L[𝕜] E}

/-- Eigenspaces of bounded operators are closed, hence complete in a complete source space. -/
private theorem completeSpace_eigenspace (A : E →L[𝕜] E) (μ : 𝕜) :
    CompleteSpace (eigenspace A.toLinearMap μ) := by
  let B : E →L[𝕜] E := A - μ • ContinuousLinearMap.id 𝕜 E
  have heq : eigenspace A.toLinearMap μ = LinearMap.ker B.toLinearMap := by
    ext x
    constructor
    · intro hx
      apply LinearMap.mem_ker.mpr
      change A x - μ • x = 0
      exact sub_eq_zero.mpr (Module.End.mem_eigenspace_iff.mp hx)
    · intro hx
      apply Module.End.mem_eigenspace_iff.mpr
      have hz := LinearMap.mem_ker.mp hx
      change A x - μ • x = 0 at hz
      exact sub_eq_zero.mp hz
  rw [heq]
  exact B.isClosed_ker.completeSpace_coe

/-- The eigenspaces of a compact self-adjoint operator form an orthogonal Hilbert sum of the
ambient Hilbert space. -/
theorem isHilbertSum_eigenspaces_of_compact_selfAdjoint
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) :
    IsHilbertSum 𝕜 (fun μ : 𝕜 => eigenspace A.toLinearMap μ)
      (fun μ : 𝕜 => (eigenspace A.toLinearMap μ).subtypeₗᵢ) := by
  have hcomplete : ∀ μ : 𝕜, CompleteSpace (eigenspace A.toLinearMap μ) :=
    fun μ => completeSpace_eigenspace A μ
  let V : ∀ μ : 𝕜, eigenspace A.toLinearMap μ →ₗᵢ[𝕜] E :=
    fun μ => (eigenspace A.toLinearMap μ).subtypeₗᵢ
  have hrange : ∀ μ : 𝕜, LinearMap.range (V μ).toLinearMap =
      eigenspace A.toLinearMap μ := by
    intro μ
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, rfl⟩
      exact x.2
    · intro y hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hortho : OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace A.toLinearMap μ) V := by
    intro μ ν hμν x y
    exact hAs.isSymmetric.orthogonalFamily_eigenspaces hμν x y
  have htotal : ⊤ ≤ (⨆ μ : 𝕜, LinearMap.range (V μ).toLinearMap).topologicalClosure := by
    simp only [hrange]
    exact le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc
        hAs.isSymmetric)).symm
  have hsum : IsHilbertSum 𝕜 (fun μ : 𝕜 => eigenspace A.toLinearMap μ) V :=
    IsHilbertSum.mk hortho htotal
  simpa only [V] using hsum

/-- Canonical spectral coordinates for a compact self-adjoint operator: the ambient Hilbert space
is isometrically equivalent to the `ℓ²`-sum of its eigenspaces. -/
noncomputable def compactSelfAdjointEigenspaceEquiv
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) :
    E ≃ₗᵢ[𝕜] lp (fun μ : 𝕜 => eigenspace A.toLinearMap μ) 2 :=
  (isHilbertSum_eigenspaces_of_compact_selfAdjoint hAc hAs).linearIsometryEquiv

/-- Spectral coordinates send a vector in the `μ`-eigenspace to the one-coordinate vector
supported at `μ`. -/
theorem compactSelfAdjointEigenspaceEquiv_apply
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) (μ : 𝕜)
    (x : eigenspace A.toLinearMap μ) :
    compactSelfAdjointEigenspaceEquiv hAc hAs x = lp.single 2 μ x := by
  classical
  let hsum := isHilbertSum_eigenspaces_of_compact_selfAdjoint hAc hAs
  have hsingle : hsum.linearIsometryEquiv.symm (lp.single 2 μ x) = x :=
    hsum.linearIsometryEquiv_symm_apply_single x
  rw [compactSelfAdjointEigenspaceEquiv, ← hsingle,
    LinearIsometryEquiv.apply_symm_apply]

end SelfAdjoint

section Positive

variable {A : E →L[𝕜] E}

/-- Every positive approximation-number value of a compact positive self-adjoint operator is an
eigenvalue. -/
theorem hasEigenvalue_approximationNumber_of_pos
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) (n : ℕ)
    (hn : 0 < A.approximationNumber n) :
    Module.End.HasEigenvalue A.toLinearMap ((A.approximationNumber n : ℝ) : 𝕜) := by
  rw [Module.End.hasEigenvalue_iff]
  intro hbot
  have hclosed : n < finrank 𝕜 (eigenSpan A (Set.Ici (A.approximationNumber n))) :=
    (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hn n).mp le_rfl
  have hopen : ¬ n < finrank 𝕜 (eigenSpan A (Set.Ioi (A.approximationNumber n))) := by
    intro hlt
    have hstrict :=
      (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi hAc hAs hApos hn n).mpr hlt
    exact (lt_irrefl (A.approximationNumber n)) hstrict
  have hsplit := finrank_eigenSpan_Ici hAc hAs hn
  rw [hbot, finrank_bot, add_zero] at hsplit
  rw [hsplit] at hclosed
  exact hopen hclosed

/-- Every positive eigenvalue of a compact positive self-adjoint operator occurs as an
approximation number. -/
theorem exists_approximationNumber_eq_of_hasEigenvalue_pos
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ)
    (hEig : Module.End.HasEigenvalue A.toLinearMap (μ : 𝕜)) :
    ∃ n : ℕ, A.approximationNumber n = μ := by
  have hfdIci : FiniteDimensional 𝕜 (eigenSpan A (Set.Ici μ)) :=
    finiteDimensional_eigenSpan hAc hAs hμ fun s hs => hs
  have hfdEig : FiniteDimensional 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) :=
    Submodule.finiteDimensional_of_le
      (eigenspace_le_eigenSpan A (Set.mem_Ici.mpr le_rfl))
  have hEigSpace : eigenspace A.toLinearMap (μ : 𝕜) ≠ ⊥ :=
    (Module.End.hasEigenvalue_iff.mp hEig)
  have hEigRank : 0 < finrank 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hEigSpace (Submodule.finrank_eq_zero.mp hzero)
  let n : ℕ := finrank 𝕜 (eigenSpan A (Set.Ioi μ))
  have hsplit := finrank_eigenSpan_Ici hAc hAs hμ
  have hnclosed : n < finrank 𝕜 (eigenSpan A (Set.Ici μ)) := by
    rw [hsplit]
    omega
  have hge : μ ≤ A.approximationNumber n :=
    (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hμ n).mpr hnclosed
  have hnstrict : ¬ μ < A.approximationNumber n := by
    intro hlt
    have hopen :=
      (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi hAc hAs hApos hμ n).mp hlt
    exact (Nat.lt_irrefl n) (by simpa only [n] using hopen)
  exact ⟨n, le_antisymm (not_lt.mp hnstrict) hge⟩

/-- The positive eigenvalues of a compact positive self-adjoint operator are exactly the positive
values of its approximation-number sequence. -/
theorem hasEigenvalue_ofReal_pos_iff_exists_approximationNumber_eq
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ) :
    Module.End.HasEigenvalue A.toLinearMap (μ : 𝕜) ↔
      ∃ n : ℕ, A.approximationNumber n = μ := by
  constructor
  · exact exists_approximationNumber_eq_of_hasEigenvalue_pos hAc hAs hApos hμ
  · rintro ⟨n, hn⟩
    have hpos : 0 < A.approximationNumber n := hn.symm ▸ hμ
    have hEig := hasEigenvalue_approximationNumber_of_pos hAc hAs hApos n hpos
    simpa only [hn] using hEig

end Positive

end

end TauCeti
