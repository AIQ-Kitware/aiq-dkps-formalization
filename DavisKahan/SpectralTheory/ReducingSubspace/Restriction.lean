/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import DavisKahan.BoundedOperator.Problem
public import DavisKahan.SpectralTheory.AbstractSpectrum
public import TauCeti.Analysis.InnerProductSpace.Projection.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-!
# Restrictions of closed operators to reducing subspaces

This module gives the source-facing inclusion, domain, and intertwining API for
the canonical restriction of a closed partial map to an orthogonally
complemented reducing subspace. The restriction, its closedness, and
self-adjointness preservation are supplied by Tau Ceti's `LinearPMap` API.
-/

public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

-- Use the native theorem locally; a global instance would create an instance cycle.
attribute [local instance] Submodule.completeSpace_coe_of_hasOrthogonalProjection

namespace PartialMap

/-- The canonical inclusion of a reducing subspace. -/
def reducingSubspaceInclusion (U : Submodule 𝕜 E) : U →L[𝕜] E :=
  U.subtypeL

omit [CompleteSpace E] in
/-- The reducing-subspace inclusion is isometric. -/
theorem reducingSubspaceInclusion_isometric (U : Submodule 𝕜 E) :
    IsometricEmbedding (reducingSubspaceInclusion U) :=
  fun _ => rfl

omit [CompleteSpace E] in
/-- The inclusion maps the restricted domain into the ambient domain. -/
theorem reducingRestriction_inclusion_mem_domain
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : _root_.LinearPMap.IsReducing A U)
    (x : (TauCeti.LinearPMap.reducingRestriction A U hred).domain) :
    reducingSubspaceInclusion U (x : U) ∈ A.domain :=
  (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A U hred (x : U)).mp
    x.property

omit [CompleteSpace E] in
/-- The inclusion intertwines the restricted and ambient operators. -/
theorem reducingRestriction_inclusion_intertwines
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : _root_.LinearPMap.IsReducing A U)
    (x : (TauCeti.LinearPMap.reducingRestriction A U hred).domain) :
    A ⟨reducingSubspaceInclusion U (x : U),
        reducingRestriction_inclusion_mem_domain A U hred x⟩ =
      reducingSubspaceInclusion U
        (TauCeti.LinearPMap.reducingRestriction A U hred x) := by
  simpa only [reducingSubspaceInclusion, Submodule.subtypeL_apply] using
    (TauCeti.LinearPMap.coe_reducingRestriction_apply A U hred (x : U)
      (reducingRestriction_inclusion_mem_domain A U hred x)).symm

end PartialMap
end DavisKahanExt
end TauCeti
