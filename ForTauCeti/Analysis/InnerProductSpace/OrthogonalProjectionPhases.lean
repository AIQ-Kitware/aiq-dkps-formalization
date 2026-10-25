/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A phase basis for two orthogonal projection spaces

Two phase operators whose distinguished projections have zero product
admit a common orthonormal eigenbasis. Only the small/small,
large/small and small/large phase pairs occur. This elementary spectral
fact is shared by the Schatten and Charbonnier transport proofs.
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Orthogonal phase projections give a common eigenbasis with three
possible phase pairs, including on a zero-dimensional carrier. -/
theorem exists_orthogonal_two_phase_basis_complex
    (a b : ℝ) (V W : E ≃ₗᵢ[ℂ] E) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B) (hAB : A * B = 0)
    (hV : (V : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hW : (W : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (alpha beta : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, (alpha i = a ∧ beta i = a) ∨
        (alpha i = b ∧ beta i = a) ∨ (alpha i = a ∧ beta i = b)) ∧
      (∀ i, V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i) ∧
      (∀ i, W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i) := by
  classical
  have hBA : B * A = 0 := by
    have h := congrArg star hAB
    simpa only [star_mul, hA.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq, star_zero]
      using h
  have hcomm : Commute A.toLinearMap B.toLinearMap := by
    change (A * B).toLinearMap = (B * A).toLinearMap
    rw [hAB, hBA]
  obtain ⟨e, mu, nu, hmu, hnu⟩ :=
    hA.isSelfAdjoint.isSymmetric.exists_joint_orthonormalBasis
      hB.isSelfAdjoint.isSymmetric hcomm
  replace hmu : ∀ i, A (e i) = mu i • e i := fun i => hmu i
  replace hnu : ∀ i, B (e i) = nu i • e i := fun i => hnu i
  have hmu01 (i) : mu i = 0 ∨ mu i = 1 := by
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    apply smul_left_injective ℂ (e.orthonormal.ne_zero i)
    have h := congrArg (fun T : E →L[ℂ] E => T (e i)) hA.isIdempotentElem.eq
    change A (A (e i)) = A (e i) at h
    rwa [hmu, map_smul, hmu, smul_smul] at h
  have hnu01 (i) : nu i = 0 ∨ nu i = 1 := by
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    apply smul_left_injective ℂ (e.orthonormal.ne_zero i)
    have h := congrArg (fun T : E →L[ℂ] E => T (e i)) hB.isIdempotentElem.eq
    change B (B (e i)) = B (e i) at h
    rwa [hnu, map_smul, hnu, smul_smul] at h
  have hnoboth (i) : ¬ (mu i = 1 ∧ nu i = 1) := by
    rintro ⟨hm, hn⟩
    have h := congrArg (fun T : E →L[ℂ] E => T (e i)) hAB
    change A (B (e i)) = 0 at h
    rw [hnu, hn, one_smul, hmu, hm, one_smul] at h
    exact e.orthonormal.ne_zero i h
  let alpha (i) := if mu i = 0 then a else b
  let beta (i) := if nu i = 0 then a else b
  refine ⟨e, alpha, beta, ?_, ?_, ?_⟩
  · intro i
    rcases hmu01 i with hm | hm <;> rcases hnu01 i with hn | hn
    · exact Or.inl ⟨by simp [alpha, hm], by simp [beta, hn]⟩
    · exact Or.inr (Or.inr ⟨by simp [alpha, hm], by simp [beta, hn]⟩)
    · exact Or.inr (Or.inl ⟨by simp [alpha, hm], by simp [beta, hn]⟩)
    · exact (hnoboth i ⟨hm, hn⟩).elim
  · intro i
    change (V : E →L[ℂ] E) (e i) = _
    rw [hV]
    rcases hmu01 i with hm | hm
    · simp [alpha, hm, hmu]
    · simp [alpha, hm, hmu, sub_smul]
  · intro i
    change (W : E →L[ℂ] E) (e i) = _
    rw [hW]
    rcases hnu01 i with hn | hn
    · simp [beta, hn, hnu]
    · simp [beta, hn, hnu, sub_smul]

end TauCeti
