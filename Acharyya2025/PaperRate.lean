/-
Paper-scale joint-rate bookkeeping for Acharyya et al. 2025.

The direct response-to-CMDS entrywise bridge removes the previous ambient
`n^2` detour.  This file isolates the resulting rate algebra:

* use response tolerance `η = x / n`;
* Chebyshev + the model union bound then has ratio `n^3 σ² / x²`, or
  `n^3 γ / (r x²)` when `σ² = γ/r`;
* the later entrywise-to-operator conversion contributes exactly one factor of
  `n`, which cancels the denominator in `η`, leaving a fixed multiple of `x`;
* the DK-sharpened spectral stage is therefore bounded by a degree-at-most-two
  polynomial in `x` under fixed spectral floor and ceiling.

Taking `x = (n^3/r)^(1/2-δ)` is the paper's final specialization.  The lemmas
here deliberately expose the algebra before introducing real-power asymptotic
syntax, so the source rate is not conflated with a hand-picked schedule.
-/

import Acharyya2025.GrowingResponse

open scoped BigOperators Topology
open Filter

namespace Acharyya2025.PaperRate

open Acharyya2025.Bridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.GrowingResponse

/-- Fixed constant multiple of the target scale `x` delivered to the spectral
perturbation theorem by the direct entrywise response bridge. -/
noncomputable def paperOperatorScale (m : Nat) (R x : Real) : Real :=
  16 * R * (m : Real)⁻¹ * x

/-- Degree-at-most-two DK spectral envelope at the paper operator scale. -/
noncomputable def paperFrobQuadraticRate
    (m d : Nat) (α Λ R x : Real) : Real :=
  configFrobQuadraticMajorant d α Λ (paperOperatorScale m R x)

/-- The population-size factor from entrywise-to-operator conversion cancels
exactly against the `1/n` response tolerance. -/
theorem scaled_cmdsEntrywiseRate_eq_paperOperatorScale
    (n m : Nat) (hn : 0 < n) (R x : Real) :
    (n : Real) * cmdsEntrywiseRate n m R (paperResponseTolerance n x) =
      paperOperatorScale m R x := by
  rw [scaled_cmdsEntrywiseRate_paperResponseTolerance n m hn R x]
  rfl

/-- The paper operator scale vanishes whenever `x` does. -/
theorem tendsto_paperOperatorScale_zero
    (m : Nat) (R : Real) {x : Nat → Real}
    (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun u => paperOperatorScale m R (x u)) atTop (𝓝 0) := by
  unfold paperOperatorScale
  simpa using hx.const_mul (16 * R * (m : Real)⁻¹)

/-- The explicit polynomial DK envelope vanishes with the paper scale. -/
theorem tendsto_paperFrobQuadraticRate_zero
    (m d : Nat) (α Λ R : Real) {x : Nat → Real}
    (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun u => paperFrobQuadraticRate m d α Λ R (x u))
      atTop (𝓝 0) := by
  have hop := tendsto_paperOperatorScale_zero m R hx
  have hlin := hop.const_mul (configFrobLinearCoeff d α Λ)
  have hquad := (hop.pow 2).const_mul (configFrobQuadraticCoeff d α Λ)
  unfold paperFrobQuadraticRate configFrobQuadraticMajorant
  simpa using hlin.add hquad

/-- Once the paper operator scale enters the local perturbative regime, the
exact DK Frobenius bound is dominated by the explicit quadratic polynomial in
`x`. -/
theorem eventually_configFrobBound_le_paperFrobQuadraticRate
    (m d : Nat) (α Λ R : Real) (hR : 0 ≤ R)
    {x : Nat → Real} (hx_nonneg : ∀ u, 0 ≤ x u)
    (hx : Tendsto x atTop (𝓝 0)) :
    ∀ᶠ u in atTop,
      configFrobBound d α Λ (paperOperatorScale m R (x u)) ≤
        paperFrobQuadraticRate m d α Λ R (x u) := by
  have hop := tendsto_paperOperatorScale_zero m R hx
  have hle1 : ∀ᶠ u in atTop, paperOperatorScale m R (x u) ≤ 1 :=
    (hop.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))).mono
      (fun _ hu => hu.le)
  filter_upwards [hle1] with u hu
  unfold paperFrobQuadraticRate
  exact configFrobBound_le_configFrobQuadraticMajorant d α Λ
    (paperOperatorScale m R (x u))
    (by
      unfold paperOperatorScale
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hR)
          (inv_nonneg.mpr (by positivity)))
        (hx_nonneg u)) hu

end Acharyya2025.PaperRate
