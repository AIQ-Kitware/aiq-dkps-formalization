/- Applications of accepted Tau Ceti PVM laws. E(B) on the slides is P.proj B hB.
   The measurable-set argument hB is explicit; the carrier is a complex Hilbert space. -/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

noncomputable section
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : TauCeti.ProjValMeasure ℝ H)
  (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
-- slide-begin
example : P.proj B hB * P.proj C hC =
    P.proj (B ∩ C) (hB.inter hC) :=
  P.proj_inter B C hB hC

example : P.proj Bᶜ hB.compl =
    ContinuousLinearMap.id ℂ H - P.proj B hB :=
  P.proj_compl B hB

example (x : H) : ‖P.proj B hB x‖ ^ 2 =
    ((P.diag x) B).toReal :=
  P.norm_sq_proj_apply B hB x
-- slide-end
