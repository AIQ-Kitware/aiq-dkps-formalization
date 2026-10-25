/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Complete a scaled orthogonal family at its zero columns

Normalize the nonzero columns and apply the accepted orthonormal extension
theorem with the original index type. Zero columns place no condition on
their basis vectors. This supplies both halves of cosine--sine coordinates
without deleting fixed or right-angle indices or sorting them again.
-/

public section

noncomputable section

namespace OrthonormalBasis

open scoped InnerProductSpace

/-- A diagonal Gram family in a space of matching dimension
is a prescribed scaling of an orthonormal basis, with the original labels
retained even at zero scales. The index type may be empty. -/
theorem exists_smul_eq_of_inner_eq_ite
    {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [Fintype ι] [DecidableEq ι]
    (hdim : Module.finrank 𝕜 E = Fintype.card ι)
    (f : ι → E) (r : ι → ℝ)
    (hinner : ∀ i j, ⟪f i, f j⟫_𝕜 = if i = j then ((r i ^ 2 : ℝ) : 𝕜) else 0) :
    ∃ b : OrthonormalBasis ι 𝕜 E, ∀ i, f i = (r i : 𝕜) • b i := by
  classical
  let S : Set ι := {i | r i ≠ 0}
  let u : ι → E := fun i => (r i : 𝕜)⁻¹ • f i
  have hon : Orthonormal 𝕜 (S.domRestrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪(r i.1 : 𝕜)⁻¹ • f i.1, (r j.1 : 𝕜)⁻¹ • f j.1⟫_𝕜 = _
    rw [inner_smul_left, inner_smul_right, hinner]
    simp only [map_inv₀, RCLike.conj_ofReal]
    by_cases hij : i = j
    · subst j
      have hi : (r i.1 : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr i.property
      simp only [ite_true, RCLike.ofReal_pow]
      field_simp
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp only [hij, hij', ite_false, mul_zero]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hdim
  refine ⟨b, fun i => ?_⟩
  by_cases hi : r i = 0
  · have hf : f i = 0 := by simpa [hi] using hinner i i
    simp only [hf, hi, RCLike.ofReal_zero, zero_smul]
  · rw [hb i hi]
    have hri : (r i : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hi
    simp only [u, smul_smul, mul_inv_cancel₀ hri, one_smul]

end OrthonormalBasis
