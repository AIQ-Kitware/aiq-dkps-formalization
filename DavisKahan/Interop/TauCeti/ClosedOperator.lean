/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Terra
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic

/-!
# Transitional ClosedOperator boundary

The historical `TauCeti.DavisKahanExt.ClosedOperator` bundle remains available
only while source-facing records and Spectra bridges are converted to raw
`LinearPMap` inputs. Its reusable domain, graph, extension, and Sylvester
mathematics is implemented in the dependency-clean `ForTauCeti` LinearPMap
layer; this module is the downstream import boundary for consumers that still
need the historical bundle.

Do not add new generic theorems to this module. A consumer should import the
canonical `ForTauCeti` API directly whenever its statement can use raw partial
maps. Delete this boundary after the final source/Spectra consumer migrates.
-/

namespace TauCeti
namespace DavisKahanExt
namespace ClosedOperator

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Compatibility packaging of a raw partial map when a legacy source-facing
result still requires the historical bundle. -/
noncomputable def ofLinearPMap
    (A : E →ₗ.[𝕜] E)
    (hdense : Dense (A.domain : Set E))
    (hclosed : A.IsClosed) :
    ClosedOperator (𝕜 := 𝕜) (E := E) where
  domain := A.domain
  toLinearMap := A.toFun
  dense_domain := hdense
  closed_graph := by
    have hgraph : (A.graph : Set (E × E)) =
        Set.range fun x : A.domain => ((x : E), A.toFun x) := by
      ext p
      change p ∈ A.graph ↔ p ∈ Set.range fun x : A.domain => ((x : E), A.toFun x)
      rw [LinearPMap.mem_graph_iff']
      rfl
    rw [← hgraph]
    exact hclosed

@[simp] theorem ofLinearPMap_toLinearPMap
    (A : E →ₗ.[𝕜] E)
    (hdense : Dense (A.domain : Set E))
    (hclosed : A.IsClosed) :
    (ofLinearPMap A hdense hclosed).toLinearPMap = A := rfl

end ClosedOperator
end DavisKahanExt
end TauCeti
