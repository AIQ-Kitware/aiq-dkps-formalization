/- Checked applications accompanying the closing lecture slides.
The imports own the mathematics; these examples introduce no new API. -/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

-- slide-begin
example {f : ℝ → ℝ} {d : ℝ}
    (hmin : IsLocalMin f 0) (hd : HasDerivAt f d 0) :
    d = 0 :=
  hmin.hasDerivAt_eq_zero hd

variable {n : Type*} [Fintype n] [DecidableEq n]

example (C : Matrix n n ℝ) :
    (C.transpose * C).trace = 0 ↔ C = 0 := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using (Matrix.trace_conjTranspose_mul_self_eq_zero_iff
      (A := C))
-- slide-end
