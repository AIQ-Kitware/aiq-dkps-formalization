/- Source-facing applications of YWS Theorem 2. All hypotheses are retained.
   Paper indices are one-based; Lean's r,s below are zero-based.
   The slide aliases abbreviate only the two norms and the two errors. -/
import YuWangSamworth2015.Symmetric.Theorem2

noncomputable section
open YuWangSamworth2015
open scoped BigOperators

variable {p d r s : ℕ}
  (A Ahat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  (hA : A.IsSymmetric) (hAhat : Ahat.IsSymmetric)
  (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
  (V Vhat : Fin d → EuclideanSpace ℝ (Fin p))
  (hV : IsEigenvectorBlock A hA hr hs hd V)
  (hVhat : IsEigenvectorBlock Ahat hAhat hr hs hd Vhat)
  (Δ : ℝ) (hΔ : 0 < Δ)
  (hgap : SourcePopulationGap A hA r s Δ)

local notation "noise" => min (Real.sqrt d * ‖LinearMap.toContinuousLinearMap (Ahat - A)‖)
  (frobeniusNorm (Ahat - A))
local notation "sinError" =>
  Submodule.sinThetaFrobenius (Submodule.span ℝ (Set.range V))
    (Submodule.span ℝ (Set.range Vhat))
local notation "alignedError" => fun O : Matrix (Fin d) (Fin d) ℝ =>
  Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2)

-- slide-begin
example : sinError ≤ 2 * noise / Δ :=
  theorem2_sinTheta A Ahat hA hAhat hr hs hd
    V Vhat hV hVhat sinError rfl Δ hΔ hgap

example : ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
    alignedError O ≤ 2 * Real.sqrt 2 * noise / Δ :=
  theorem2_alignedFrame A Ahat hA hAhat
    hr hs hd V Vhat hV hVhat Δ hΔ hgap
-- slide-end
