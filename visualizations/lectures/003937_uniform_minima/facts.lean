import Mathlib.Basic.Real.Basic
-- slide-begin
variable {α : Type*} (f g : α → ℝ) (x y : α) (ε : ℝ)

example (hmin : ∀ z, g y ≤ g z)
    (hupper : ∀ z, g z ≤ f z + ε) :
    g y ≤ f x + ε :=
  le_trans (hmin x) (hupper x)

example (hmin : ∀ z, f x ≤ f z)
    (hlower : ∀ z, f z - ε ≤ g z) :
    f x - ε ≤ g y :=
  le_trans (sub_le_sub_right (hmin y) ε) (hlower y)
-- slide-end
