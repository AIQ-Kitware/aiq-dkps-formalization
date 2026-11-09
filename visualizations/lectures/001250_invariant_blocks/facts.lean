import TauCeti.Analysis.InnerProductSpace.Projection.Block
noncomputable section
-- slide-begin
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

example (T : E →L[ℝ] E) :
    K.offDiagBlock T = 0 ↔
      Commute K.starProjection T :=
  K.offDiagBlock_eq_zero_iff

example (x : E) :
    K.starProjection x +
      Kᗮ.starProjection x = x :=
  K.starProjection_add_starProjection_orthogonal x
-- slide-end
