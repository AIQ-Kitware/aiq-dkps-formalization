/- Existing Mathlib facts used in the refresher. No new mathematical API. -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped InnerProductSpace

-- slide-begin
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

example (x : E) :
    ⟪x, x⟫_ℝ = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x

example {f : ℝ → ℝ} {d : ℝ}
    (hmin : IsLocalMin f 0)
    (hd : HasDerivAt f d 0) :
    d = 0 :=
  hmin.hasDerivAt_eq_zero hd
-- slide-end
