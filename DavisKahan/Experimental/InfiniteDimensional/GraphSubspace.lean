/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.OperatorAngle
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Graph subspaces and angular operators

An arbitrary ambient operator is first angularized to
`P_{Uᗮ} X P_U`.  The graph is the closed range of `P_U + P_{Uᗮ} X P_U`.
This makes the compatibility definition total while agreeing with the ordinary
graph whenever `X` already satisfies `IsAngularOperator U X`.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Angular block extracted from an ambient operator. -/
noncomputable def angularize (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : E →L[𝕜] E :=
  complementaryProjection U ∘L X ∘L projection U

/-- Graph embedding associated with an ambient operator. -/
noncomputable def graphEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : E →L[𝕜] E :=
  projection U + angularize U X

/-- Closed graph subspace. -/
noncomputable def graphSubspace (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Submodule 𝕜 E :=
  (LinearMap.range (graphEmbedding U X).toLinearMap).topologicalClosure

noncomputable instance graphSubspace_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : (graphSubspace U X).HasOrthogonalProjection := by
  exact Submodule.topologicalClosure_hasOrthogonalProjection _

/-- For an angular operator, angularization changes nothing. -/
@[simp] theorem angularize_eq
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    angularize U X = X := by
  unfold angularize
  rw [← hX.1, ContinuousLinearMap.comp_assoc]
  have hPcX : complementaryProjection U ∘L X = X := by
    rw [Submodule.starProjection_orthogonal']
    calc
      (1-projection U) ∘L X = X - projection U ∘L X := by module
      _ = X := by rw [hX.2, sub_zero]
  exact hPcX

/-- The graph embedding is one-antilipschitz on the base subspace. -/
theorem graphEmbedding_norm_sq
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (u : U) :
    ‖graphEmbedding U X u‖^2 = ‖(u:E)‖^2 + ‖angularize U X u‖^2 := by
  have hu : projection U (u:E) = u :=
    U.starProjection_eq_self_iff.mpr u.property
  have horth : ⟪projection U (u:E), angularize U X (u:E)⟫_𝕜 = 0 := by
    apply Submodule.inner_left_of_mem_orthogonal
    · simpa [hu] using u.property
    · exact Uᗮ.starProjection_apply_mem _
  simpa [graphEmbedding, hu, norm_add_sq, horth]

/-- Under angularity, the raw graph range is already closed. -/
theorem isClosed_range_graphEmbedding
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    IsClosed (LinearMap.range (graphEmbedding U X).toLinearMap : Set E) := by
  let T : U →L[𝕜] E := (graphEmbedding U X).compContinuous U.subtypeL
  have hanti : AntilipschitzWith 1 T := by
    rw [antilipschitzWith_iff_le_dist]
    intro x y
    have hsq := graphEmbedding_norm_sq U X (x-y)
    have hnonneg := sq_nonneg ‖angularize U X (x-y)‖
    simpa [dist_eq_norm, map_sub] using
      (sq_le_sq₀ (norm_nonneg (x-y)) (norm_nonneg (T x-T y))).mpr
        (by nlinarith)
  simpa [T, LinearMap.range_comp] using hanti.isClosed_range

/-- For an angular operator the closure in `graphSubspace` is redundant. -/
theorem graphSubspace_eq_range
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    graphSubspace U X = LinearMap.range
      (projection U + X ∘L projection U).toLinearMap := by
  rw [graphSubspace, angularize_eq U X hX]
  rw [Submodule.topologicalClosure_eq_self]
  exact isClosed_range_graphEmbedding U X hX

/-- Closed-form projection onto a graph. -/
noncomputable def graphProjectionFormula
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : E →L[𝕜] E := by
  classical
  let Y := angularize U X
  let T := projection U + Y
  let G := 1 + star Y ∘L Y
  have hG : IsUnit G := one_add_star_mul_self_isUnit Y
  exact T ∘L (↑hG.unit⁻¹ : E →L[𝕜] E) ∘L star T

/-- Every acute subspace is the graph of a unique bounded angular operator. -/
theorem existsUnique_angularOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    ∃! X : E →L[𝕜] E,
      IsAngularOperator U X ∧ graphSubspace U X = V := by
  classical
  let T : V →L[𝕜] U := projectionRestriction U V
  have hbelow : ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖T v‖ :=
    projectionRestriction_boundedBelow_of_gap_lt_one U V hacute
  have hsurj : Function.Surjective T :=
    projectionRestriction_surjective_of_gap_lt_one U V hacute
  let e : V ≃L[𝕜] U := ContinuousLinearEquiv.ofBijective T
    hbelow.1 hbelow.2 hsurj
  let X : E →L[𝕜] E :=
    complementaryProjection U ∘L V.subtypeL ∘L e.symm.toContinuousLinearMap ∘L
      U.orthogonalProjectionOnto ∘L projection U
  have hX : IsAngularOperator U X := by
    constructor
    · simp [X, ContinuousLinearMap.comp_assoc]
    · rw [← ContinuousLinearMap.comp_assoc,
        projection_comp_complementaryProjection]
      simp
  have hgraph : graphSubspace U X = V := by
    rw [graphSubspace_eq_range U X hX]
    apply le_antisymm
    · rintro y ⟨u, rfl⟩
      exact graphEmbedding_projectionInverse_mem V e u
    · intro v hv
      let v' : V := ⟨v,hv⟩
      refine ⟨projection U v, ?_⟩
      exact graphEmbedding_projectionInverse_eq V e v'
  refine ⟨X, ⟨hX,hgraph⟩, ?_⟩
  intro Y hY
  have hYr := graphSubspace_eq_range U Y hY.1
  ext x
  rw [← hY.1.1, ← hX.1]
  let u := projection U x
  have hxGraph : u + X u ∈ V := by
    rw [← hgraph, graphSubspace_eq_range U X hX]
    exact LinearMap.mem_range_self _ u
  have hyGraph : u + Y u ∈ V := by
    rw [← hY.2, hYr]
    exact LinearMap.mem_range_self _ u
  have hcoord : X u = Y u := by
    have hzero := projectionRestriction_injective_of_acute U V hacute
    apply hzero
    simp [projectionRestriction, hX.2, hY.1.2]
  exact hcoord

/-- Projection onto a graph subspace in terms of the angular operator. -/
theorem projection_graphSubspace_formula
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    projection (graphSubspace U X) = graphProjectionFormula U X := by
  classical
  let Y := angularize U X
  let T := projection U + Y
  let G := 1 + star Y ∘L Y
  let GhalfInv := RCLikeContinuousFunctionalCalculus.invSqrt G
  let J := T ∘L GhalfInv
  have hJiso : ∀ x, ‖J x‖ = ‖projection U x‖ := by
    intro x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp [J, T, G, GhalfInv, angularize_eq U X hX,
      graphEmbedding_norm_sq]
  have hrange : LinearMap.range J.toLinearMap = graphSubspace U X := by
    rw [graphSubspace_eq_range U X hX]
    exact range_comp_isUnit_eq_range T
      (RCLikeContinuousFunctionalCalculus.invSqrt_isUnit G)
  have hproj : J ∘L star J = graphProjectionFormula U X := by
    unfold graphProjectionFormula
    rw [angularize_eq U X hX]
    simp [J, T, G, GhalfInv, ContinuousLinearMap.comp_assoc,
      RCLikeContinuousFunctionalCalculus.invSqrt_mul_self]
  rw [← hproj]
  exact orthogonalProjection_eq_isometry_range J hJiso hrange

/-- Tangent of the maximal angle is the angular-operator norm. -/
theorem tan_maximalAngle_eq_norm_angularOperator
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    Real.tan (maximalAngle U (graphSubspace U X)) = ‖X‖ := by
  have hgap : subspaceGap U (graphSubspace U X) =
      ‖X‖ / Real.sqrt (1 + ‖X‖^2) := by
    rw [projection_graphSubspace_formula U X hX]
    exact projectionGap_graphProjectionFormula U X hX
  rw [maximalAngle, hgap]
  exact Real.tan_arcsin_graph_ratio (norm_nonneg X)

/-- Contractive angular operators correspond to angles below `π/4`. -/
theorem norm_angularOperator_lt_one_iff
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    ‖X‖ < 1 ↔ maximalAngle U (graphSubspace U X) < Real.pi / 4 := by
  have hrange : maximalAngle U (graphSubspace U X) ∈
      Set.Ico 0 (Real.pi/2) := maximalAngle_graph_mem_Ico U X hX
  rw [← tan_maximalAngle_eq_norm_angularOperator U X hX,
    ← Real.tan_pi_div_four]
  exact Real.strictMonoOn_tan.lt_iff_lt hrange
    ⟨by positivity, by linarith [Real.pi_pos]⟩

end DavisKahanExt
end ForMathlib
