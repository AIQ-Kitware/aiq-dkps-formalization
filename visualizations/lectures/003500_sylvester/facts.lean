/- Applications of the accepted bounded Sylvester API. -/
import TauCeti.Analysis.InnerProductSpace.Sylvester

noncomputable section
-- slide-begin
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] (A B X : E →L[ℝ] E)

example : A.sylvester B X = A ∘L X - X ∘L B :=
  A.sylvester_apply B X

example (c δ : ℝ)
    (hA : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℝ)
    (hB : ∀ y, RCLike.re ⟪B y, y⟫_ℝ ≤ c * ‖y‖ ^ 2) :
    δ * ‖X‖ ≤ ‖A.sylvester B X‖ :=
  A.mul_norm_le_norm_sylvester_apply_of_le_re_inner_of_re_inner_le hA hB X
-- slide-end
