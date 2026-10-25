/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Diagonal compression of a fixed/right reflection

If a spanning family consists of source-invariant blocks on which an
involution is fixed or exchanges the source and complementary sectors,
its source-diagonal compression is an orthogonal projection. Orthogonality
of the family and finite dimension of the ambient space are not needed.
## Provenance

This is classical projection algebra. The Lean proof is independently
written here and uses Mathlib's orthogonal-projection and adjoint APIs.
No dimension, angle, or optimizer assertion is imported into the lemma.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A self-adjoint operator acting as zero or identity on every block
of a spanning family is an orthogonal projection. -/
theorem isStarProjection_of_spanning_fixed_or_zero
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H) (F : Finset (Submodule 𝕜 E))
    (hspan : F.sup id = ⊤)
    (hblocks : ∀ N ∈ F, (∀ x ∈ N, H x = x) ∨ (∀ x ∈ N, H x = 0)) :
    IsStarProjection H := by
  have hN : ∀ N ∈ F, N ≤ (H * H - H).toLinearMap.ker := by
    intro N hNF x hx
    change H (H x) - H x = 0
    rcases hblocks N hNF with hfix | hzero
    · rw [hfix x hx, hfix x hx, sub_self]
    · rw [hzero x hx, map_zero, sub_self]
  have htop : (⊤ : Submodule 𝕜 E) ≤ (H * H - H).toLinearMap.ker := by
    rw [← hspan]
    exact Finset.sup_le hN
  refine ⟨?_, hH⟩
  apply ContinuousLinearMap.ext
  intro x
  have hx := htop (Submodule.mem_top (x := x))
  change H (H x) - H x = 0 at hx
  exact sub_eq_zero.mp hx

/-- The diagonal compression of a fixed/right involution is an
orthogonal projection: it is identity on fixed blocks and zero on the
blocks exchanging source and complement. The spanning family need
not be orthogonal, and the ambient Hilbert space need not be finite. -/
theorem isStarProjection_diagonalCompression_of_fixed_or_exchange_blocks
    (P R : E →L[𝕜] E) (hP : IsStarProjection P) (hR : IsSelfAdjoint R)
    (hRR : ∀ x, R (R x) = x) (F : Finset (Submodule 𝕜 E)) (hspan : F.sup id = ⊤)
    (hblocks : ∀ N ∈ F, (∀ x ∈ N, P x ∈ N) ∧ (∀ x ∈ N, R x ∈ N) ∧
      ((∀ x ∈ N, R x = x) ∨ (∀ x ∈ N, R (P (R x)) = x - P x))) :
    IsStarProjection (P * R * P + (1 - P) * R * (1 - P)) := by
  let H := P * R * P + (1 - P) * R * (1 - P)
  have hH : IsSelfAdjoint H :=
    (hR.conjugate_self hP.isSelfAdjoint).add
      (hR.conjugate_self ((IsSelfAdjoint.one _).sub hP.isSelfAdjoint))
  apply isStarProjection_of_spanning_fixed_or_zero H hH F hspan
  have hPP (x : E) : P (P x) = P x :=
    congrArg (fun A : E →L[𝕜] E => A x) hP.isIdempotentElem.eq
  intro N hNF
  obtain ⟨hPN, hRN, hcase⟩ := hblocks N hNF
  rcases hcase with hfix | hexchange
  · left
    intro x hx
    change P (R (P x)) + (R (x - P x) - P (R (x - P x))) = x
    rw [hfix (P x) (hPN x hx), hfix (x - P x) (N.sub_mem hx (hPN x hx))]
    simp only [map_sub, hPP]
    module
  · right
    intro x hx
    have hRP : R (P x) = R x - P (R x) := by
      have h := hexchange (R x) (hRN x hx)
      rwa [hRR] at h
    change P (R (P x)) + (R (x - P x) - P (R (x - P x))) = 0
    simp only [map_sub, hRP, hPP]
    module

end TauCeti
