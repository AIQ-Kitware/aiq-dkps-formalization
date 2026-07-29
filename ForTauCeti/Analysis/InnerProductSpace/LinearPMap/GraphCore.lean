/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Graph cores of a partial linear map

A *graph core* of `A` is a submodule of its domain from which every domain
vector can be reached by a sequence converging in the graph norm — that is,
converging in the ambient space with its `A`-images converging too.

The sequence formulation is deliberate: it records exactly the two convergences
the closed-graph argument consumes, without installing a second topology on the
domain subtype.

## Provenance

* Original module: `DavisKahan/Sources/DavisKahan1970/SineTheta/CommonCore.lean`,
  where it was stated for the bundled DKPS `ClosedOperator`.
* Extraction class: **representation migration** onto Mathlib's `LinearPMap`,
  per the U1 lane (`dev/tauceti/u1-linearpmap-migration.md`).  Generalised on
  the way: the original was stated for an endomorphism, this is stated for
  `E →ₗ.[𝕜] F`.
* Spectra influence: none.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A submodule of the operator domain that is sequentially dense in the graph
norm: every domain vector is the limit of a sequence from the core whose
`A`-images also converge to its image. -/
def IsGraphCore (A : E →ₗ.[𝕜] F) (D : Submodule 𝕜 A.domain) : Prop :=
  ∀ x : A.domain, ∃ u : ℕ → D,
    Tendsto (fun n => (((u n : D) : A.domain) : E)) atTop (𝓝 (x : E)) ∧
    Tendsto (fun n => A ((u n : D) : A.domain)) atTop (𝓝 (A x))

namespace IsGraphCore

/-- The whole domain is a graph core. -/
theorem top (A : E →ₗ.[𝕜] F) : IsGraphCore A ⊤ := by
  intro x
  exact ⟨fun _ => ⟨x, Submodule.mem_top⟩, by simp, by simp⟩

/-- A graph core is ambiently dense in the operator domain. -/
theorem ambient_approximation {A : E →ₗ.[𝕜] F} {D : Submodule 𝕜 A.domain}
    (hD : IsGraphCore A D) (x : A.domain) :
    ∃ u : ℕ → D,
      Tendsto (fun n => (((u n : D) : A.domain) : E)) atTop (𝓝 (x : E)) := by
  obtain ⟨u, hu, -⟩ := hD x
  exact ⟨u, hu⟩

end IsGraphCore

end LinearPMap
end TauCeti
