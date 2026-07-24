/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedTransport
import DavisKahan.Experimental.InfiniteDimensional.Riccati.BoundedGraphAcute

/-!
# Canonical graph-rotation transport for unbounded block operators

This leaf specializes the generic closed-operator pullback construction to the
completed complex direct rotation from the zero block graph to a bounded graph.
It keeps the transported operator domain explicit and records the projection
intertwining needed before the transformed operator can be identified with a
closed block-diagonal direct sum.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The zero graph and every bounded unbounded-block graph form an acute pair.
The adjective `unbounded` refers to the operator acting on the graph, not to
its bounded angular parametrization. -/
theorem zeroUnboundedGraph_isAcute_unboundedBlockGraph
    (X : E0 →L[ℂ] E1) :
    IsAcute
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
      (unboundedBlockGraph X) := by
  simpa [unboundedBlockGraph, blockGraph] using
    (zeroGraph_isAcute_blockGraph X)

/-- Canonical complex rotation from the first coordinate graph to the graph of
`X`. -/
noncomputable def unboundedGraphRotation (X : E0 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  complexDirectRotation
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (zeroUnboundedGraph_isAcute_unboundedBlockGraph X)

/-- The canonical graph rotation is norm preserving and onto. -/
theorem unboundedGraphRotation_unitary (X : E0 →L[ℂ] E1) :
    IsUnitaryOperator (unboundedGraphRotation X) := by
  exact complexDirectRotation_unitary
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (zeroUnboundedGraph_isAcute_unboundedBlockGraph X)

/-- Kernel and range form of bijectivity, suitable for constructing a
continuous linear equivalence from the canonical graph rotation. -/
theorem unboundedGraphRotation_ker_bot_range_top
    (X : E0 →L[ℂ] E1) :
    LinearMap.ker (unboundedGraphRotation X).toLinearMap = ⊥ ∧
      LinearMap.range (unboundedGraphRotation X).toLinearMap = ⊤ := by
  let W := unboundedGraphRotation X
  have hW : IsUnitaryOperator W := unboundedGraphRotation_unitary X
  constructor
  · rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hxyW : W x = W y := by
      change unboundedGraphRotation X x = unboundedGraphRotation X y
      exact hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    calc
      ‖x - y‖ = ‖W (x - y)‖ := (hW.1 (x - y)).symm
      _ = ‖W x - W y‖ := by rw [map_sub]
      _ = 0 := by rw [hxyW, sub_self, norm_zero]
  · rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := hW.2 y
    exact ⟨x, hx⟩

/-- The canonical graph rotation bundled as a continuous linear equivalence. -/
noncomputable def unboundedGraphRotationEquiv (X : E0 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) ≃L[ℂ] WithLp 2 (E0 × E1) :=
  ContinuousLinearEquiv.ofBijective (unboundedGraphRotation X)
    (unboundedGraphRotation_ker_bot_range_top X).1
    (unboundedGraphRotation_ker_bot_range_top X).2

@[simp] theorem unboundedGraphRotationEquiv_apply
    (X : E0 →L[ℂ] E1) (z : WithLp 2 (E0 × E1)) :
    unboundedGraphRotationEquiv X z = unboundedGraphRotation X z :=
  rfl

/-- The equivalence underlying the graph rotation remains unitary. -/
theorem unboundedGraphRotationEquiv_unitary (X : E0 →L[ℂ] E1) :
    IsUnitaryOperator
      (unboundedGraphRotationEquiv X).toContinuousLinearMap := by
  change IsUnitaryOperator (unboundedGraphRotation X)
  exact unboundedGraphRotation_unitary X

/-- The graph-rotation equivalence intertwines the coordinate projection with
the projection onto the graph of `X`. -/
theorem unboundedGraphRotationEquiv_intertwines_projection
    (X : E0 →L[ℂ] E1) :
    (unboundedGraphRotationEquiv X).toContinuousLinearMap ∘L
        projection (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) =
      projection (unboundedBlockGraph X) ∘L
        (unboundedGraphRotationEquiv X).toContinuousLinearMap := by
  change unboundedGraphRotation X ∘L
        projection (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) =
      projection (unboundedBlockGraph X) ∘L unboundedGraphRotation X
  exact complexDirectRotation_intertwines
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (zeroUnboundedGraph_isAcute_unboundedBlockGraph X)

/-- The closed operator obtained by transporting the full unbounded block
operator back along the canonical graph rotation. -/
noncomputable def unboundedGraphRotationPullback
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    ClosedOperator (𝕜 := ℂ) (E := WithLp 2 (E0 × E1)) :=
  ClosedOperator.pullback (unboundedBlockOperatorCore H)
    (unboundedGraphRotationEquiv X)

/-- Exact domain of the graph-rotated unbounded block operator. -/
@[simp] theorem mem_unboundedGraphRotationPullback_domain_iff
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedGraphRotationPullback H X).domain ↔
      unboundedGraphRotation X z ∈ (unboundedBlockOperatorCore H).domain := by
  rfl

/-- Action of the rotated operator, stated after applying the forward graph
rotation so that no inverse-domain coercions are hidden. -/
theorem unboundedGraphRotationPullback_action
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (z : (unboundedGraphRotationPullback H X).domain) :
    unboundedGraphRotation X
        ((unboundedGraphRotationPullback H X).toLinearMap z) =
      (unboundedBlockOperatorCore H).toLinearMap
        (ClosedOperator.pullbackDomainToOriginal
          (unboundedBlockOperatorCore H)
          (unboundedGraphRotationEquiv X) z) := by
  change (unboundedGraphRotationEquiv X)
        ((ClosedOperator.pullback (unboundedBlockOperatorCore H)
          (unboundedGraphRotationEquiv X)).toLinearMap z) = _
  rw [ClosedOperator.pullback_apply,
    (unboundedGraphRotationEquiv X).apply_symm_apply]

/-- The canonical rotation gives a genuine two-way unitary equivalence between
the transported closed operator and the original unbounded block operator. -/
theorem unboundedGraphRotationPullback_unitaryEquivalent
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    ClosedOperator.UnitaryEquivalent
      (unboundedGraphRotationPullback H X)
      (unboundedBlockOperatorCore H)
      (unboundedGraphRotationEquiv X).toContinuousLinearMap
      (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap := by
  exact ClosedOperator.pullback_unitaryEquivalent
    (unboundedBlockOperatorCore H)
    (unboundedGraphRotationEquiv X)
    (unboundedGraphRotationEquiv_unitary X)

end DavisKahanExt
end TauCeti