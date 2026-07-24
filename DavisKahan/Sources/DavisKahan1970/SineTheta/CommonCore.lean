/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomain

/-!
# Graph-core form of the unbounded residual hypothesis

The unbounded appendix may be read as specifying the residual identity on a
common dense operator core rather than requiring equality of the two full
composition domains.  The mathematically sufficient condition is graph-density
for the trial operator: every vector in `dom A₀` is approximated both in the
ambient norm and after applying `A₀`.

This module proves the closed-graph extension step explicitly.  If the bounded
residual identity holds on such a graph core, then the trial map sends all of
`dom A₀` into `dom A` and the same identity holds on the full trial domain.
Thus the accepted unbounded sine-theta theorem applies without strengthening a
source statement that was intended only on a core.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter Topology

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

open TauCeti.DavisKahanExt

namespace ClosedOperator

/-- A linear subspace of the operator domain that is sequentially dense in the
graph norm.  The sequence formulation avoids installing a second topology on
the domain subtype while recording exactly the two convergences needed by the
closed-graph argument. -/
def IsGraphCore
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (D : Submodule 𝕜 A.domain) : Prop :=
  ∀ x : A.domain, ∃ u : ℕ → D,
    Tendsto (fun n => ((((u n : D) : A.domain) : E))) atTop (𝓝 (x : E)) ∧
    Tendsto (fun n => A.toLinearMap ((u n : D) : A.domain))
      atTop (𝓝 (A.toLinearMap x))

namespace IsGraphCore

omit [CompleteSpace E] in
/-- The full operator domain is a graph core. -/
theorem top (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    ClosedOperator.IsGraphCore A ⊤ := by
  intro x
  refine ⟨fun _ => ⟨x, Submodule.mem_top⟩, ?_, ?_⟩
  · simpa using tendsto_const_nhds
  · simpa using tendsto_const_nhds

omit [CompleteSpace E] in
/-- A graph core is ambiently dense in the operator domain: every domain vector
is an ambient-norm limit of vectors from the core. -/
theorem ambient_approximation
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {D : Submodule 𝕜 A.domain} (hD : ClosedOperator.IsGraphCore A D)
    (x : A.domain) :
    ∃ u : ℕ → D,
      Tendsto (fun n => ((((u n : D) : A.domain) : E))) atTop (𝓝 (x : E)) := by
  obtain ⟨u, hu, _⟩ := hD x
  exact ⟨u, hu⟩

end IsGraphCore
end ClosedOperator

/-- Residual data on a graph core of the trial operator. -/
structure PaperCommonCoreResidualData
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (A₀ : ClosedOperator (𝕜 := 𝕜) (E := F))
    (X : F →L[𝕜] E) (R : F →L[𝕜] E) where
  core : Submodule 𝕜 A₀.domain
  graph_core : ClosedOperator.IsGraphCore A₀ core
  maps_core : ∀ x : core, X (((x : core) : A₀.domain) : F) ∈ A.domain
  residual_on_core : ∀ x : core,
    A.toLinearMap
        ⟨X (((x : core) : A₀.domain) : F), maps_core x⟩ -
      X (A₀.toLinearMap ((x : core) : A₀.domain)) =
        R (((x : core) : A₀.domain) : F)

namespace PaperCommonCoreResidualData

/-- The core residual identity extends to every vector in the trial domain.
This is the load-bearing closed-graph argument behind the literal appendix
formulation. -/
theorem extends_to_domain
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {A₀ : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {X : F →L[𝕜] E} {R : F →L[𝕜] E}
    (C : PaperCommonCoreResidualData A A₀ X R)
    (x : A₀.domain) :
    ∃ hx : X (x : F) ∈ A.domain,
      A.toLinearMap ⟨X (x : F), hx⟩ - X (A₀.toLinearMap x) = R (x : F) := by
  obtain ⟨u, hu, hAu⟩ := C.graph_core x
  let xu : ℕ → A.domain := fun n =>
    ⟨X ((((u n : C.core) : A₀.domain) : F)), C.maps_core (u n)⟩
  have hX : Tendsto (fun n => ((xu n : A.domain) : E))
      atTop (𝓝 (X (x : F))) := by
    change Tendsto
      (fun n => X ((((u n : C.core) : A₀.domain) : F)))
      atTop (𝓝 (X (x : F)))
    exact (X.continuous.tendsto (x : F)).comp hu
  have hR : Tendsto
      (fun n => R ((((u n : C.core) : A₀.domain) : F)))
      atTop (𝓝 (R (x : F))) :=
    (R.continuous.tendsto (x : F)).comp hu
  have hXA₀ : Tendsto
      (fun n => X (A₀.toLinearMap ((u n : C.core) : A₀.domain)))
      atTop (𝓝 (X (A₀.toLinearMap x))) :=
    (X.continuous.tendsto (A₀.toLinearMap x)).comp hAu
  have hAseq : Tendsto (fun n => A.toLinearMap (xu n))
      atTop (𝓝 (R (x : F) + X (A₀.toLinearMap x))) := by
    have hsum := hR.add hXA₀
    convert hsum using 1
    funext n
    change A.toLinearMap
        ⟨X ((((u n : C.core) : A₀.domain) : F)), C.maps_core (u n)⟩ =
      R ((((u n : C.core) : A₀.domain) : F)) +
        X (A₀.toLinearMap ((u n : C.core) : A₀.domain))
    exact sub_eq_iff_eq_add.mp (C.residual_on_core (u n))
  have hgraph :
      (X (x : F), R (x : F) + X (A₀.toLinearMap x)) ∈
        Set.range (fun z : A.domain => ((z : E), A.toLinearMap z)) :=
    A.closed_graph.mem_of_tendsto (hX.prodMk_nhds hAseq)
      (Eventually.of_forall fun n => ⟨xu n, rfl⟩)
  rcases hgraph with ⟨z, hz⟩
  have hzX : (z : E) = X (x : F) := congrArg Prod.fst hz
  have hzA : A.toLinearMap z = R (x : F) + X (A₀.toLinearMap x) :=
    congrArg Prod.snd hz
  have hx : X (x : F) ∈ A.domain := by
    rw [← hzX]
    exact z.property
  refine ⟨hx, ?_⟩
  have hsubtype : z = (⟨X (x : F), hx⟩ : A.domain) := Subtype.ext hzX
  have haction : A.toLinearMap ⟨X (x : F), hx⟩ =
      R (x : F) + X (A₀.toLinearMap x) := by
    rw [← hsubtype]
    exact hzA
  rw [haction]
  abel

/-- Full-domain compatibility obtained from the graph-core hypothesis. -/
theorem maps_domain
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {A₀ : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {X : F →L[𝕜] E} {R : F →L[𝕜] E}
    (C : PaperCommonCoreResidualData A A₀ X R) :
    ∀ x : A₀.domain, X (x : F) ∈ A.domain := by
  intro x
  exact (C.extends_to_domain x).choose

/-- Full-domain residual identity obtained from the graph-core hypothesis. -/
theorem residual_eq
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {A₀ : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {X : F →L[𝕜] E} {R : F →L[𝕜] E}
    (C : PaperCommonCoreResidualData A A₀ X R)
    (x : A₀.domain) :
    A.toLinearMap ⟨X (x : F), C.maps_domain x⟩ -
      X (A₀.toLinearMap x) = R (x : F) := by
  obtain ⟨hx, hEq⟩ := C.extends_to_domain x
  have hsub :
      (⟨X (x : F), hx⟩ : A.domain) =
        ⟨X (x : F), C.maps_domain x⟩ := Subtype.ext rfl
  simpa [hsub] using hEq

end PaperCommonCoreResidualData

/-- Construct the accepted sine-theta bookkeeping package from a residual
identity available only on a graph core. -/
noncomputable def unboundedSinThetaDataOfPaperCommonCore
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (A₀ : ClosedOperator (𝕜 := 𝕜) (E := F))
    (Λ₁ : ClosedOperator (𝕜 := 𝕜) (E := G))
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (C : PaperCommonCoreResidualData A A₀ X R)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hintertwines : ∀ y : Λ₁.domain,
      A.toLinearMap ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁.toLinearMap y)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) where
  A := A
  A₀ := A₀
  Λ₁ := Λ₁
  X := X
  F₁ := F₁
  residual := R
  X_maps_domain := C.maps_domain
  F₁_maps_domain := hF₁
  residual_eq := C.residual_eq
  intertwines := hintertwines

/-- The constructed data carries the supplied residual unchanged.

Downstream statements quote the source residual `R`, while the accepted engine
returns the residual field of the constructed package; without this projection
the two do not match syntactically. -/
@[simp]
theorem unboundedSinThetaDataOfPaperCommonCore_residual
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (A₀ : ClosedOperator (𝕜 := 𝕜) (E := F))
    (Λ₁ : ClosedOperator (𝕜 := 𝕜) (E := G))
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (C : PaperCommonCoreResidualData A A₀ X R)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hintertwines : ∀ y : Λ₁.domain,
      A.toLinearMap ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁.toLinearMap y)) :
    (unboundedSinThetaDataOfPaperCommonCore A A₀ Λ₁ X F₁ R C hF₁
      hintertwines).residual = R := rfl

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti