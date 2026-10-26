/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.BlockSum

/-!
# Eigenspaces of block sums without finite ambient dimension

The actual eigenspace equivalence holds in arbitrary dimension. Only
the eigenspaces need be finite to add their finite dimensions. The
proof adapts the accepted Tau Ceti finite-dimensional block-sum proof,
retaining its canonical `WithLp` representation and removing the
unnecessary finite-ambient hypothesis.
-/

public section

noncomputable section

namespace LinearMap

open Module.End

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The eigenspace of a block sum is the product of its eigenspaces,
with no ambient finite-dimensional or topological hypothesis. -/
def eigenspace_prodMap_withLpMap_equiv (A : V →ₗ[K] V) (B : W →ₗ[K] W) (mu : K) :
    eigenspace ((A.prodMap B).withLpMap 2) mu ≃ₗ[K]
      eigenspace A mu × eigenspace B mu := by
  have hmem {x : WithLp 2 (V × W)} :
      x ∈ eigenspace ((A.prodMap B).withLpMap 2) mu ↔
        x.fst ∈ eigenspace A mu ∧ x.snd ∈ eigenspace B mu := by
    simp only [mem_eigenspace_iff, coe_withLpMap]
    constructor
    · intro h
      exact ⟨by simpa [WithLp.map, prodMap_apply] using congrArg WithLp.fst h,
        by simpa [WithLp.map, prodMap_apply] using congrArg WithLp.snd h⟩
    · rintro ⟨h₁, h₂⟩
      simp [WithLp.map, WithLp.ext_iff, Prod.ext_iff, prodMap_apply, h₁, h₂]
  exact
    { toFun := fun x => (⟨x.1.fst, (hmem.mp x.2).1⟩, ⟨x.1.snd, (hmem.mp x.2).2⟩)
      invFun := fun y => ⟨WithLp.toLp 2 (y.1.1, y.2.1), hmem.mpr ⟨by simp, by simp⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => Subtype.ext (WithLp.toLp_ofLp 2 x.1)
      right_inv := fun _ => rfl }

/-- Eigenspace multiplicities add for an infinite-dimensional block
sum whenever those individual eigenspaces are finite-dimensional. -/
theorem finrank_eigenspace_prodMap_withLpMap_of_finite_eigenspaces
    (A : V →ₗ[K] V) (B : W →ₗ[K] W) (mu : K)
    [FiniteDimensional K (eigenspace A mu)] [FiniteDimensional K (eigenspace B mu)] :
    Module.finrank K (eigenspace ((A.prodMap B).withLpMap 2) mu) =
      Module.finrank K (eigenspace A mu) + Module.finrank K (eigenspace B mu) := by
  rw [(eigenspace_prodMap_withLpMap_equiv A B mu).finrank_eq, Module.finrank_prod]

end LinearMap
