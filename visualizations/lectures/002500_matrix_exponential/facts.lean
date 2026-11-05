/- Checked applications accompanying the closing lecture slides.
The imports own the mathematics; these examples introduce no new API. -/
import TauCeti.Analysis.Normed.Operator.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

-- slide-begin
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℝ] E) :=
  .restrictScalars ℚ ℝ _

example (A : E →L[ℝ] E) (s t : ℝ) :
    exp ((s + t) • A) =
      (exp (s • A)).comp (exp (t • A)) :=
  ContinuousLinearMap.exp_add_smul A s t

example (B : E →L[ℝ] E)
    (hB : B ∈ skewAdjoint (E →L[ℝ] E)) :
    exp B ∈ unitary (E →L[ℝ] E) :=
  exp_mem_unitary_of_mem_skewAdjoint hB

example (B P : E →L[ℝ] E) (h : Commute B P) :
    Commute (exp B) P :=
  h.exp_left
-- slide-end
