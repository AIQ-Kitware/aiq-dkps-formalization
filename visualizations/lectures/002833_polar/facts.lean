/- Applications of the accepted canonical finite polar API. -/
import TauCeti.Analysis.InnerProductSpace.Polar.Finite

noncomputable section
-- slide-begin
variable {E F : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (A : E →ₗ[ℝ] F)

example : A.polarFactor ∘ₗ A.operatorAbs = A :=
  A.polarFactor_comp_operatorAbs

example {x : E} (hx : x ∈ A.kerᗮ) :
    ‖A.polarFactor x‖ = ‖x‖ :=
  A.norm_polarFactor_apply hx
-- slide-end
