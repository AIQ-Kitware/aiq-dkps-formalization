/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A joint orthonormal eigenbasis for commuting symmetric operators

This is a basis form of Mathlib's orthogonal joint-eigenspace decomposition.
The finite nonzero-summand assembly follows the accepted Tau Ceti proof of
`LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`.
It applies over real or complex scalars and makes no novelty claim.
-/

public section

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Commuting symmetric maps have a common orthonormal eigenbasis. -/
theorem exists_joint_orthonormalBasis
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
      (mu nu : Fin (Module.finrank 𝕜 E) → 𝕜),
      (∀ i, A (e i) = mu i • e i) ∧ (∀ i, B (e i) = nu i • e i) := by
  classical
  let K : 𝕜 × 𝕜 → Submodule 𝕜 E := fun p =>
    Module.End.eigenspace A p.2 ⊓ Module.End.eigenspace B p.1
  have hsum : DirectSum.IsInternal K := hA.directSum_isInternal_of_commute hB hAB
  have horth := hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  let J := {p : 𝕜 × 𝕜 // K p ≠ ⊥}
  let : Fintype J := hsum.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hsumJ : DirectSum.IsInternal fun p : J => K p :=
    DirectSum.isInternal_ne_bot_iff.mpr hsum
  have horthJ := horth.comp (Subtype.val_injective (p := fun p => K p ≠ ⊥))
  let e := hsumJ.subordinateOrthonormalBasis rfl horthJ
  let p (i : Fin (Module.finrank 𝕜 E)) :=
    hsumJ.subordinateOrthonormalBasisIndex rfl i horthJ
  refine ⟨e, fun i => (p i).1.2, fun i => (p i).1.1, ?_, ?_⟩
  · intro i
    have hm := hsumJ.subordinateOrthonormalBasis_subordinate rfl i horthJ
    exact Module.End.mem_eigenspace_iff.mp hm.1
  · intro i
    have hm := hsumJ.subordinateOrthonormalBasis_subordinate rfl i horthJ
    exact Module.End.mem_eigenspace_iff.mp hm.2

end LinearMap.IsSymmetric
