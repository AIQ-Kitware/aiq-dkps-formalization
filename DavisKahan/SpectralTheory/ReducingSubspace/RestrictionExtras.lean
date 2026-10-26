/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import DavisKahan.SpectralTheory.ReducingSubspace.Restriction

/-!
# Convenience laws for reducing restrictions

This leaf keeps optional compatibility lemmas separate from the compiler-accepted
core restriction construction.  In particular, it records orthogonal-complement
closure and agreement with the ordinary bounded restriction.
-/

public section

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace PartialMap

omit [CompleteSpace E] in
/-- A bounded reducing-subspace law induces the domain-aware law for the
full-domain closed operator. -/
theorem ofBounded_reducesSubspace
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : Submodule.IsReducing U A) :
    _root_.LinearPMap.IsReducing (A.toLinearMap.toPMap ⊤) U := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp
  · rw [_root_.LinearPMap.isInvariant_iff]
    intro x hx
    show A (x : E) ∈ U
    exact hred.mem_invtSubmodule hx
  · rw [_root_.LinearPMap.isInvariant_iff]
    intro x hx
    show A (x : E) ∈ Uᗮ
    exact hred.orthogonal_mem_invtSubmodule hx

/-- The block of a bounded operator on a subspace it reduces, as a partial map.

The Section 6 whole-space statements compare two such blocks through
`FormBoundedSylvesterGap`.  Writing the composite out inline is what made those
hypotheses unreadable, and is why callers were handed a record to fill in
instead of a theorem to apply. -/
@[expose]
noncomputable def boundedReducingBlock
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : Submodule.IsReducing U A) : U →ₗ.[𝕜] U :=
  (A.toLinearMap.toPMap ⊤).restrict
    (ofBounded_reducesSubspace A U hred).isInvariant

/-- The block of a bounded operator on the orthogonal complement of a subspace
it reduces.  A reducing subspace's complement is reducing, so this needs no
hypothesis beyond `hred`. -/
@[expose]
noncomputable def boundedReducingBlockCompl
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : Submodule.IsReducing U A) : Uᗮ →ₗ.[𝕜] Uᗮ :=
  (A.toLinearMap.toPMap ⊤).restrict
    ((ofBounded_reducesSubspace A U hred).orthogonal.isInvariant)

end PartialMap
end DavisKahanExt
end TauCeti
