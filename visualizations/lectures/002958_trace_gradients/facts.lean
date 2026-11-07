import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
-- slide-begin
variable {n : Type*} [Fintype n] [DecidableEq n]

example (A B : Matrix n n ℝ) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

example (C : Matrix n n ℝ) :
    (C.transpose * C).trace = 0 ↔ C = 0 := by
  simpa using
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := C))
-- slide-end
