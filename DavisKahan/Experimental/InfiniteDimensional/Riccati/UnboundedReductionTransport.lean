/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.UnboundedRotationTransport

/-!
# Transport of reducing subspaces through an unbounded graph rotation

This leaf proves the domain-sensitive reduction theorem needed for unbounded
block diagonalization.  A closed operator pulled back through a continuous
linear equivalence reduces a subspace whenever the original operator reduces
the transported subspace and the equivalence intertwines their orthogonal
projections.

The specialization to the canonical graph rotation shows that the pulled-back
unbounded block operator reduces the first coordinate summand and its
orthogonal complement.  This is the precise sense in which the transported
operator is block diagonal before its two closed coordinate restrictions are
constructed explicitly.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace ClosedOperator

/-- Intertwining the orthogonal projections onto `U` and `V` also intertwines
those onto their orthogonal complements. -/
theorem intertwines_orthogonal_projection_of_intertwines_projection
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap) :
    e.toContinuousLinearMap ∘L Uᗮ.starProjection =
      Vᗮ.starProjection ∘L e.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change e (Uᗮ.starProjection x) = Vᗮ.starProjection (e x)
  rw [Submodule.starProjection_orthogonal_apply,
    Submodule.starProjection_orthogonal_apply, map_sub]
  have hx := congrArg (fun T : E →L[𝕜] E => T x) hproj
  change e (U.starProjection x) = V.starProjection (e x) at hx
  rw [hx]

/-- A projection-intertwining equivalence maps membership in the source
subspace to membership in the target subspace. -/
theorem map_mem_of_intertwines_projection
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap)
    {x : E} (hx : x ∈ U) : e x ∈ V := by
  rw [← Submodule.starProjection_eq_self_iff]
  have hintertwine := congrArg (fun T : E →L[𝕜] E => T x) hproj
  change e (U.starProjection x) = V.starProjection (e x) at hintertwine
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at hintertwine
  exact hintertwine.symm

/-- The inverse of a projection-intertwining equivalence maps membership in the
target subspace back to membership in the source subspace. -/
theorem symm_map_mem_of_intertwines_projection
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap)
    {y : E} (hy : y ∈ V) : e.symm y ∈ U := by
  rw [← Submodule.starProjection_eq_self_iff]
  apply e.injective
  have hintertwine := congrArg (fun T : E →L[𝕜] E => T (e.symm y)) hproj
  change e (U.starProjection (e.symm y)) =
    V.starProjection (e (e.symm y)) at hintertwine
  rw [e.apply_symm_apply, Submodule.starProjection_eq_self_iff.mpr hy] at hintertwine
  simpa using hintertwine

/-- Reduction, including both projection-domain conditions, transports through
a closed-operator pullback when the equivalence intertwines the corresponding
orthogonal projections. -/
theorem pullback_reducesSubspace_of_intertwines_projection
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap)
    (hred : A.ReducesSubspace V) :
    (pullback A e).ReducesSubspace U := by
  have hprojOrth : e.toContinuousLinearMap ∘L Uᗮ.starProjection =
      Vᗮ.starProjection ∘L e.toContinuousLinearMap :=
    intertwines_orthogonal_projection_of_intertwines_projection e U V hproj
  rcases hred with ⟨hVdom, hVOrthDom, hVinv, hVOrthInv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change e (U.starProjection (x : E)) ∈ A.domain
    have hintertwine := congrArg (fun T : E →L[𝕜] E => T (x : E)) hproj
    change e (U.starProjection (x : E)) =
      V.starProjection (e (x : E)) at hintertwine
    rw [hintertwine]
    simpa only [pullbackDomainToOriginal_coe] using
      hVdom (pullbackDomainToOriginal A e x)
  · intro x
    change e (Uᗮ.starProjection (x : E)) ∈ A.domain
    have hintertwine := congrArg (fun T : E →L[𝕜] E => T (x : E)) hprojOrth
    change e (Uᗮ.starProjection (x : E)) =
      Vᗮ.starProjection (e (x : E)) at hintertwine
    rw [hintertwine]
    simpa only [pullbackDomainToOriginal_coe] using
      hVOrthDom (pullbackDomainToOriginal A e x)
  · intro x hx
    rw [pullback_apply]
    apply symm_map_mem_of_intertwines_projection e U V hproj
    apply hVinv (pullbackDomainToOriginal A e x)
    exact map_mem_of_intertwines_projection e U V hproj hx
  · intro x hx
    rw [pullback_apply]
    apply symm_map_mem_of_intertwines_projection e Uᗮ Vᗮ hprojOrth
    apply hVOrthInv (pullbackDomainToOriginal A e x)
    exact map_mem_of_intertwines_projection e Uᗮ Vᗮ hprojOrth hx

end ClosedOperator

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Reduction of a Riccati graph transports to reduction of the first
coordinate summand by the graph-rotated pullback operator. -/
theorem unboundedGraphRotationPullback_reduces_zeroGraph
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    (unboundedGraphRotationPullback H X).ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) := by
  exact ClosedOperator.pullback_reducesSubspace_of_intertwines_projection
    (unboundedBlockOperatorCore H) (unboundedGraphRotationEquiv X)
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (unboundedGraphRotationEquiv_intertwines_projection X) hred

/-- The coordinate-block-diagonal representative of the full unbounded block
operator.  Its domain is the exact graph-rotation pullback of the original
product domain. -/
noncomputable def unboundedBlockDiagonalOperatorCore
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    ClosedOperator (𝕜 := ℂ) (E := WithLp 2 (E0 × E1)) :=
  unboundedGraphRotationPullback H X

@[simp] theorem mem_unboundedBlockDiagonalOperatorCore_domain_iff
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedBlockDiagonalOperatorCore H X).domain ↔
      unboundedGraphRotation X z ∈ (unboundedBlockOperatorCore H).domain := by
  rfl

/-- The diagonal representative reduces both coordinate summands whenever the
original unbounded block operator reduces the Riccati graph. -/
theorem unboundedBlockDiagonalOperatorCore_reduces_zeroGraph
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    (unboundedBlockDiagonalOperatorCore H X).ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) := by
  exact unboundedGraphRotationPullback_reduces_zeroGraph H X hred

/-- Correctly oriented exact unitary equivalence: the graph rotation carries
the coordinate-diagonal pullback to the original unbounded block operator. -/
theorem unboundedBlockDiagonalOperatorCore_unitaryEquivalent
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    ClosedOperator.UnitaryEquivalent
      (unboundedBlockDiagonalOperatorCore H X)
      (unboundedBlockOperatorCore H)
      (unboundedGraphRotationEquiv X).toContinuousLinearMap
      (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap := by
  exact unboundedGraphRotationPullback_unitaryEquivalent H X

end DavisKahanExt
end ForMathlib
