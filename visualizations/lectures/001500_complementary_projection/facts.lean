/- Existing projection facts used in the complementary-projection lesson. -/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
-- slide-begin
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E)
  [K.HasOrthogonalProjection]

example : Kᗮ.starProjection =
    ContinuousLinearMap.id ℝ E - K.starProjection :=
  K.starProjection_orthogonal

example (x : E) :
    x - K.starProjection x ∈ Kᗮ :=
  K.sub_starProjection_mem_orthogonal x
-- slide-end
