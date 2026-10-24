/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import ForTauCeti.Analysis.InnerProductSpace.Positive.SquareRoot.Eigenspace

/-!
# Orthogonal projections and principal sines on invariant subspaces

If the orthogonal projection onto `K` preserves `Z`, its restriction to `Z`
is the orthogonal projection onto `K.comap Z.subtype`. The characterization
of an orthogonal projection by membership and an orthogonal residual proves
this without a choice of coordinates.

For a pair of such reducing projections, a nonnegative sine eigenvalue on
the restricted pair is also a sine eigenvalue on the ambient pair. Compute
the square using the restricted projection difference, then use positivity
of the ambient sine operator. This supplies the kernel contribution when
assembling spectral principal-angle sums.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An invariant ambient orthogonal projection restricts to the projection
onto the intersection, expressed on the subspace carrier. -/
theorem starProjection_comap_subtype_apply_of_invariant
    (K Z : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection]
    (hinv : ∀ x ∈ Z, K.starProjection x ∈ Z) (x : Z) :
    (((K.comap Z.subtype).starProjection x : Z) : E) = K.starProjection x := by
  let v : Z := ⟨K.starProjection x, hinv x x.property⟩
  have hproj : (K.comap Z.subtype).starProjection x = v := by
    apply eq_starProjection_of_mem_of_inner_eq_zero
    · exact K.starProjection_apply_mem x
    · intro y hy
      change inner 𝕜 ((x : E) - K.starProjection x) (y : E) = 0
      exact K.starProjection_inner_eq_zero x y hy
  exact congrArg (fun y : Z => (y : E)) hproj

/-- A nonnegative principal-sine eigenvalue of an invariant subspace pair
is also a sine eigenvalue for the ambient pair. -/
theorem sinAngleOperator_apply_of_comap_eigenvector [CompleteSpace E]
    (K L Z : Submodule 𝕜 E) [CompleteSpace Z]
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection] [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z)
    (x : Z) (s : ℝ) (hs : 0 ≤ s)
    (hx : (K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype) x = (s : 𝕜) • x) :
    K.sinAngleOperator L (x : E) = (s : 𝕜) • (x : E) := by
  let S := K.sinAngleOperator L
  let D := K.starProjection - L.starProjection
  let S₀ := (K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype)
  let D₀ := (K.comap Z.subtype).starProjection - (L.comap Z.subtype).starProjection
  have hD (y : Z) : (D₀ y : E) = D (y : E) := by
    change ((K.comap Z.subtype).starProjection y : E) -
      ((L.comap Z.subtype).starProjection y : E) = _
    rw [starProjection_comap_subtype_apply_of_invariant K Z hK,
      starProjection_comap_subtype_apply_of_invariant L Z hL]
    rfl
  have hDsq : (D₀ (D₀ x) : E) = D (D (x : E)) := by rw [hD, hD]
  have hS₀sq : S₀ * S₀ = D₀ * D₀ := by
    simpa only [sq] using (K.comap Z.subtype).sinAngleOperator_sq (L.comap Z.subtype)
  have hscalar : D (D (x : E)) = ((s : 𝕜) * (s : 𝕜)) • (x : E) := by
    rw [← hDsq]
    have h := congrArg (fun T : Z →L[𝕜] Z => (T x : E)) hS₀sq
    change (S₀ (S₀ x) : E) = (D₀ (D₀ x) : E) at h
    rw [← h]
    change ((S₀ (S₀ x) : Z) : E) = _
    change S₀ x = (s : 𝕜) • x at hx
    rw [hx, map_smul, hx, smul_smul]
    rfl
  have hS : S.toLinearMap.IsPositive := (K.isPositive_sinAngleOperator L).toLinearMap
  apply hS.apply_eq_smul_of_apply_apply_eq_smul hs
  have h := congrArg (fun T : E →L[𝕜] E => T (x : E)) (K.sinAngleOperator_sq L)
  change S (S (x : E)) = D (D (x : E)) at h
  exact h.trans hscalar

end Submodule
