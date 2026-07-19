/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.ReducingRestriction

/-!
# Convenience laws for reducing restrictions

This leaf keeps optional compatibility lemmas separate from the compiler-accepted
core restriction construction.  In particular, it records orthogonal-complement
closure and agreement with the ordinary bounded restriction.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace ClosedOperator
namespace ReducesSubspace

/-- Orthogonal complementation preserves the reducing-subspace property. -/
theorem orthogonal
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) : A.ReducesSubspace Uᗮ := by
  refine ⟨h.orthogonalProjection_mem_domain, ?_,
    h.orthogonal_invariant, ?_⟩
  · intro x
    simpa only [Submodule.orthogonal_orthogonal] using
      h.projection_mem_domain x
  · intro x hx
    simpa only [Submodule.orthogonal_orthogonal] using
      h.invariant x hx

end ReducesSubspace

/-- A bounded reducing-subspace law induces the domain-aware law for the
full-domain closed operator. -/
theorem ofBounded_reducesSubspace
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.Reduces U) : (ofBounded A).ReducesSubspace U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    simp
  · intro x hx
    simpa [InvariantSubspace] using hred.1 (x : E) hx
  · intro x hx
    simpa [InvariantSubspace] using hred.2 (x : E) hx

/-- For a bounded operator, the closed reducing restriction has the same
pointwise action as the ordinary bounded restriction. -/
@[simp]
theorem reducingRestriction_ofBounded_apply
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.Reduces U)
    (x : (reducingRestriction (ofBounded A) U
      (ofBounded_reducesSubspace A U hred)).domain) :
    (reducingRestriction (ofBounded A) U
      (ofBounded_reducesSubspace A U hred)).toLinearMap x =
        A.restrict hred.1 (x : U) := by
  apply Subtype.ext
  rfl

end ClosedOperator
end DavisKahanExt
end ForMathlib
