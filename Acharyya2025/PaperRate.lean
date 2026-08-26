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
import Acharyya2025.GrowingPipeline
import Acharyya2025.RateChain
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open scoped BigOperators Topology
open Filter
open MeasureTheory ProbabilityTheory

namespace Acharyya2025.PaperRate

open Acharyya2024
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


/-! ### Literal `r = ω(n³)` / real-power specialization -/

open Asymptotics
open Acharyya2025.GrowingPipeline

/-- The joint sample-size ratio appearing in the paper: `n³ / r`. -/
noncomputable def paperBaseRatio
    (count replicates : Nat → Nat) (u : Nat) : Real :=
  (count u : Real) ^ 3 / (replicates u : Real)

/-- Acharyya's source-scale choice `(n³/r)^(1/2-δ)`. -/
noncomputable def paperDeltaScale
    (count replicates : Nat → Nat) (δ : Real) (u : Nat) : Real :=
  (paperBaseRatio count replicates u) ^ ((1 : Real) / 2 - δ)

/-- Literal asymptotic encoding of `r = ω(n³)`: the cubic population sequence
is little-o of the replicate-count sequence. -/
def ReplicatesDominateCubic
    (count replicates : Nat → Nat) : Prop :=
  (fun u => (count u : Real) ^ 3) =o[atTop]
    (fun u => (replicates u : Real))

/-- The little-o formulation of `r = ω(n³)` implies `n³/r → 0`. -/
theorem tendsto_paperBaseRatio_zero
    {count replicates : Nat → Nat}
    (hω : ReplicatesDominateCubic count replicates) :
    Tendsto (paperBaseRatio count replicates) atTop (𝓝 0) := by
  unfold ReplicatesDominateCubic at hω
  change Tendsto
    (fun u => (count u : Real) ^ 3 / (replicates u : Real)) atTop (𝓝 0)
  exact hω.tendsto_div_nhds_zero

/-- The base ratio is strictly positive for positive population and replicate
counts. -/
theorem paperBaseRatio_pos
    (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u) (u : Nat) :
    0 < paperBaseRatio count replicates u := by
  unfold paperBaseRatio
  have hn : (0 : Real) < count u := by exact_mod_cast hcount u
  have hr : (0 : Real) < replicates u := by exact_mod_cast hrep u
  exact div_pos (pow_pos hn 3) hr

/-- Positive population and replicate counts make the paper scale positive for any exponent. -/
theorem paperDeltaScale_pos
    (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u)
    (δ : Real) (u : Nat) :
    0 < paperDeltaScale count replicates δ u := by
  unfold paperDeltaScale
  exact Real.rpow_pos_of_pos
    (paperBaseRatio_pos count replicates hcount hrep u) _

/-- Under `r = ω(n³)`, the literal source scale
`(n³/r)^(1/2-δ)` tends to zero for every `δ ∈ (0,1/2)`. -/
theorem tendsto_paperDeltaScale_zero
    {count replicates : Nat → Nat} {δ : Real}
    (hω : ReplicatesDominateCubic count replicates)
    (_hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    Tendsto (paperDeltaScale count replicates δ) atTop (𝓝 0) := by
  have hbase := tendsto_paperBaseRatio_zero hω
  have hexp : 0 < (1 : Real) / 2 - δ := by linarith
  change Tendsto
    (fun u => (paperBaseRatio count replicates u) ^ ((1 : Real) / 2 - δ))
    atTop (𝓝 0)
  exact hbase.rpow_const_nhds_zero hexp

/-- The cancellation behind the paper's probability estimate:

`(n³/r) / ((n³/r)^(1/2-δ))² = (n³/r)^(2δ)`.
-/
theorem paperBaseRatio_div_paperDeltaScale_sq
    (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u)
    (δ : Real) (u : Nat) :
    paperBaseRatio count replicates u /
        (paperDeltaScale count replicates δ u) ^ 2 =
      (paperBaseRatio count replicates u) ^ (2 * δ) := by
  let q := paperBaseRatio count replicates u
  have hq : 0 < q := paperBaseRatio_pos count replicates hcount hrep u
  change q / (q ^ ((1 : Real) / 2 - δ)) ^ 2 = q ^ (2 * δ)
  calc
    q / (q ^ ((1 : Real) / 2 - δ)) ^ 2
        = q / q ^ (((1 : Real) / 2 - δ) * 2) := by
          rw [← Real.rpow_natCast (q ^ ((1 : Real) / 2 - δ)) 2,
            ← Real.rpow_mul hq.le]
          norm_num
    _ = q ^ (1 - (((1 : Real) / 2 - δ) * 2)) := by
      rw [Real.rpow_sub hq, Real.rpow_one]
    _ = q ^ (2 * δ) := by
      congr 1
      ring

/-- Pointwise form of the paper concentration ratio at the real-power scale. -/
theorem concentration_ratio_paperDeltaScale_eq
    (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u)
    (γ : Nat → Real) (δ : Real) (u : Nat) :
    ((count u : Real) ^ 3 * γ u) / replicates u /
        (paperDeltaScale count replicates δ u) ^ 2 =
      γ u * (paperBaseRatio count replicates u) ^ (2 * δ) := by
  calc
    ((count u : Real) ^ 3 * γ u) / replicates u /
        (paperDeltaScale count replicates δ u) ^ 2
        = γ u * (paperBaseRatio count replicates u /
            (paperDeltaScale count replicates δ u) ^ 2) := by
          unfold paperBaseRatio
          ring
    _ = γ u * (paperBaseRatio count replicates u) ^ (2 * δ) := by
      rw [paperBaseRatio_div_paperDeltaScale_sq count replicates hcount hrep δ u]

/-- Bounded per-replicate second moments make the exact paper-scale Chebyshev
ratio vanish under `r = ω(n³)`. -/
theorem tendsto_concentration_ratio_paperDeltaScale_zero
    {count replicates : Nat → Nat}
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u)
    {γ : Nat → Real} {Γ δ : Real}
    (hγ : ∀ u, |γ u| ≤ Γ)
    (hω : ReplicatesDominateCubic count replicates)
    (hδ0 : 0 < δ) :
    Tendsto
      (fun u => ((count u : Real) ^ 3 * γ u) / replicates u /
        (paperDeltaScale count replicates δ u) ^ 2)
      atTop (𝓝 0) := by
  have hbase := tendsto_paperBaseRatio_zero hω
  have hpow : Tendsto
      (fun u => (paperBaseRatio count replicates u) ^ (2 * δ))
      atTop (𝓝 0) := by
    exact hbase.rpow_const_nhds_zero (by linarith)
  have hmajor : Tendsto
      (fun u => Γ * (paperBaseRatio count replicates u) ^ (2 * δ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul Γ
  have hprod : Tendsto
      (fun u => γ u * (paperBaseRatio count replicates u) ^ (2 * δ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun u => ?_) hmajor
    rw [Real.norm_eq_abs, abs_mul]
    have hp : 0 ≤ (paperBaseRatio count replicates u) ^ (2 * δ) :=
      Real.rpow_nonneg
        (paperBaseRatio_pos count replicates hcount hrep u).le _
    rw [abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (hγ u) hp
  have heq :
      (fun u => ((count u : Real) ^ 3 * γ u) / replicates u /
        (paperDeltaScale count replicates δ u) ^ 2) =
      (fun u => γ u * (paperBaseRatio count replicates u) ^ (2 * δ)) := by
    funext u
    exact concentration_ratio_paperDeltaScale_eq
      count replicates hcount hrep γ δ u
  rw [heq]
  exact hprod

/-- Concrete iid response concentration at Acharyya's literal source scale.
This discharges the generic `count³ γ/(r x²) → 0` premise from `r = ω(n³)`,
a uniform `O(1)` second-moment bound, and `δ ∈ (0,1/2)`. -/
theorem highProb_uniformResponseMeanClose_of_growing_iid_replicates_deltaScale
    {Ω0 : Type} [MeasurableSpace Ω0]
    (P : Nat → Measure Ω0) [∀ u, IsProbabilityMeasure (P u)]
    {m p : Nat} (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u)
    (Y : ∀ u, Fin (count u) → Fin (replicates u) → Ω0 → Mat m p)
    (μ : ∀ u, Fin (count u) → Mat m p)
    (hL2 : ∀ u i k, MemLp (Y u i k) 2 (P u))
    (hmean : ∀ u i k c, ∫ ω, Y u i k ω c ∂(P u) = μ u i c)
    (hindep : ∀ u i,
      Set.Pairwise (Set.univ : Set (Fin (replicates u)))
        fun k l => IndepFun (Y u i k) (Y u i l) (P u))
    (γ : Nat → Real) (Γ δ : Real)
    (hbound : ∀ u i k,
      ∫ ω, ‖Y u i k ω - μ u i‖ ^ 2 ∂(P u) ≤ γ u)
    (hsample_int : ∀ u i, Integrable
      (fun ω => ‖growingReplicateMean count replicates Y u ω i - μ u i‖ ^ 2)
      (P u))
    (hγ : ∀ u, |γ u| ≤ Γ)
    (hω : ReplicatesDominateCubic count replicates)
    (hδ0 : 0 < δ) (_hδhalf : δ < 1 / 2) :
    HighProbAtTop P
      (fun u => {ω | UniformResponseMeanClose
        (growingReplicateMean count replicates Y u ω) (μ u)
        (paperResponseTolerance (count u)
          (paperDeltaScale count replicates δ u))}) := by
  apply highProb_uniformResponseMeanClose_of_growing_iid_replicates_paperScale
    P count replicates hcount hrep Y μ hL2 hmean hindep γ
      (paperDeltaScale count replicates δ) hbound hsample_int
  · exact paperDeltaScale_pos count replicates hcount hrep δ
  · exact tendsto_concentration_ratio_paperDeltaScale_zero
      hcount hrep hγ hω hδ0

/-- The DK polynomial envelope tends to zero at the literal source scale. -/
theorem tendsto_paperFrobQuadraticRate_deltaScale_zero
    (m d : Nat) (α Λ R : Real)
    {count replicates : Nat → Nat} {δ : Real}
    (hω : ReplicatesDominateCubic count replicates)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    Tendsto
      (fun u => paperFrobQuadraticRate m d α Λ R
        (paperDeltaScale count replicates δ u))
      atTop (𝓝 0) := by
  exact tendsto_paperFrobQuadraticRate_zero m d α Λ R
    (tendsto_paperDeltaScale_zero hω hδ0 hδhalf)

/-- A growing deterministic spectral certificate at the literal source scale.
Its entrywise CMDS tolerance is the direct response rate at
`η=(n³/r)^(1/2-δ)/n`; its final envelope is the exact DK Frobenius bound. -/
noncomputable def paperDeltaGrowingConfigControl
    (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u) (hrep : ∀ u, 0 < replicates u)
    (m d : Nat) (α Λ R δ : Real)
    (_hα : 0 < α) (hR : 0 ≤ R)
    (hω : ReplicatesDominateCubic count replicates)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    GrowingConfigControl count d α (fun _ => Λ)
      (fun u => cmdsEntrywiseRate (count u) m R
        (paperResponseTolerance (count u)
          (paperDeltaScale count replicates δ u))) := by
  let x : Nat → Real := paperDeltaScale count replicates δ
  let entryRate : Nat → Real := fun u => cmdsEntrywiseRate (count u) m R
    (paperResponseTolerance (count u) (x u))
  have hx : Tendsto x atTop (𝓝 0) :=
    tendsto_paperDeltaScale_zero hω hδ0 hδhalf
  have hentry : ∀ u, 0 ≤ entryRate u := by
    intro u
    have hx0 : 0 ≤ x u :=
      (paperDeltaScale_pos count replicates hcount hrep δ u).le
    unfold entryRate cmdsEntrywiseRate responseEntrywiseRate paperResponseTolerance
    positivity
  have hscaled : Tendsto
      (fun u => (count u : Real) * entryRate u) atTop (𝓝 0) := by
    have heq :
        (fun u => (count u : Real) * entryRate u) =
        (fun u => paperOperatorScale m R (x u)) := by
      funext u
      unfold entryRate
      exact scaled_cmdsEntrywiseRate_eq_paperOperatorScale
        (count u) m (hcount u) R (x u)
    rw [heq]
    exact tendsto_paperOperatorScale_zero m R hx
  have hbound : Tendsto
      (fun u => configFrobBound d α Λ
        ((count u : Real) * entryRate u)) atTop (𝓝 0) :=
    Acharyya2025.RateChain.tendsto_configFrobBound_comp_zero d α Λ hscaled
  exact GrowingConfigControl.of_tendsto hentry hbound

end Acharyya2025.PaperRate
