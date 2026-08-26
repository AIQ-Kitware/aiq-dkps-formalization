/-
Explicit conservative schedules for raw-response Quench.

The current public bridge accepts abstract limit certificates.  This module
provides one deliberately loose polynomial schedule that discharges those
limits automatically.  The constants are not intended to be optimal; the goal
is a theorem whose users choose a response budget, not a collection of
asymptotic side proofs.
-/

import DkpsQuench2026.Probability.UniformConcentration

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

open Acharyya2025.Bridge
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open Acharyya2025.ConfigPerturbation

/-- Conservative response-mean tolerance.  With the direct entrywise
response-to-CMDS bridge, the second power is the smallest integer power that
makes the batch-scaled CMDS perturbation vanish. -/
noncomputable def safeResponseTolerance (n : Nat) : Real :=
  ((((n + 1 : Nat) : Real) ^ 2))⁻¹

/-- Conservative finite-model replicate budget. -/
def safeFiniteReplicates (n : Nat) : Nat :=
  (n + 1) ^ 6

/-- Replicate budget allowing a stage net with polynomial cardinality
`O((n+1)^entropyPower)`. -/
def safeEntropyReplicates (entropyPower n : Nat) : Nat :=
  (n + 1) ^ (6 + entropyPower)

/-- Canonical shrinking perspective-net radius for a common raw-response
Lipschitz constant `L`.  The denominator reserves half of the response error
budget for extension from net centers to arbitrary models. -/
noncomputable def safePerspectiveRadius (L : Real) (n : Nat) : Real :=
  safeResponseTolerance n / (4 * (L + 1))

/-- Half of the final response tolerance is reserved for concentration on the
finite net; the other half is reserved for deterministic net extension. -/
noncomputable def safeNetTolerance (n : Nat) : Real :=
  safeResponseTolerance n / 2

theorem safeResponseTolerance_pos (n : Nat) :
    0 < safeResponseTolerance n := by
  rw [safeResponseTolerance]
  exact inv_pos.mpr (pow_pos (by positivity : (0 : Real) < ((n + 1 : Nat) : Real)) 2)

theorem safeFiniteReplicates_pos (n : Nat) :
    0 < safeFiniteReplicates n := by
  rw [safeFiniteReplicates]
  exact pow_pos (Nat.succ_pos n) 6

theorem safeEntropyReplicates_pos (entropyPower n : Nat) :
    0 < safeEntropyReplicates entropyPower n := by
  rw [safeEntropyReplicates]
  exact pow_pos (Nat.succ_pos n) (6 + entropyPower)

theorem safePerspectiveRadius_pos
    (L : Real) (hL : 0 ≤ L) (n : Nat) :
    0 < safePerspectiveRadius L n := by
  rw [safePerspectiveRadius]
  have hden : (0 : Real) < 4 * (L + 1) := by nlinarith
  exact div_pos (safeResponseTolerance_pos n) hden

/-- The canonical perspective-net radius vanishes for every nonnegative fixed
Lipschitz constant.
-/
theorem safePerspectiveRadius_zero
    (L : Real) (hL : 0 ≤ L) :
    Tendsto (safePerspectiveRadius L) atTop (𝓝 0) := by
  have h0 : Tendsto safeResponseTolerance atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ 2) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by norm_num)))
        tendsto_id
    have h2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 2) atTop atTop := by
      simp_rw [← Nat.cast_pow]
      exact tendsto_natCast_atTop_atTop.comp hnat
    exact h2.inv_tendsto_atTop
  unfold safePerspectiveRadius
  simpa using h0.div_const (4 * (L + 1))

/-- Compact finite-dimensional perspective ranges admit canonical safe nets
with polynomial stage cardinality.

This result removes the net, radius, entropy exponent, and covering-number
certificate from the final infinite-model theorem.
-/
theorem exists_safeGrowingPerspectiveNet
    {Q : Type*} [DecidableEq Q]
    {X : Type*} [MeasurableSpace X]
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ))
    (L : Real) (hL : 0 ≤ L) :
    ∃ net : GrowingPerspectiveNet ψ, ∃ C : Real,
      0 ≤ C ∧
      (∀ n, ((net.centers n).card : Real) ≤
        C * (((n + 1 : Nat) : Real) ^ (2 * d))) ∧
      (∀ n, net.radius n = safePerspectiveRadius L n) := by
  obtain ⟨net, C0, hC0, hcard0, hradius⟩ :=
    exists_growingPerspectiveNet_with_polynomial_card ψ hcompact
      (safePerspectiveRadius L) (safePerspectiveRadius_pos L hL) (safePerspectiveRadius_zero L hL)
  refine ⟨net, C0 * (1 + 4 * (L + 1)) ^ d, by positivity, fun n => ?_, hradius⟩
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
  have hpos2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hinv : (safePerspectiveRadius L n)⁻¹ = 4 * (L + 1) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [safePerspectiveRadius, safeResponseTolerance, inv_div, div_eq_mul_inv, inv_inv]
  have hmax : max 1 (safePerspectiveRadius L n)⁻¹ ≤ (1 + 4 * (L + 1)) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hinv]
    refine max_le ?_ ?_
    · nlinarith [h1, hL, mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * (L + 1)) hpos2]
    · nlinarith [hpos2, hL]
  calc ((net.centers n).card : ℝ)
      ≤ C0 * (max 1 (safePerspectiveRadius L n)⁻¹) ^ d := hcard0 n
    _ ≤ C0 * ((1 + 4 * (L + 1)) * ((n + 1 : ℕ) : ℝ) ^ 2) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax d) hC0
    _ = C0 * (1 + 4 * (L + 1)) ^ d * (((n + 1 : ℕ) : ℝ)) ^ (2 * d) := by
        rw [mul_pow, ← pow_mul]; ring

/-- The conservative response tolerance vanishes.
-/
theorem safeResponseTolerance_zero :
    Tendsto safeResponseTolerance atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n + 1) ^ 2) atTop atTop :=
    tendsto_atTop_mono
      (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by norm_num)))
      tendsto_id
  have h2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 2) atTop atTop := by
    simp_rw [← Nat.cast_pow]
    exact tendsto_natCast_atTop_atTop.comp hnat
  exact h2.inv_tendsto_atTop

/-- The finite-model Chebyshev/union-bound ratio vanishes under the safe
replicate schedule.
-/
theorem safeFinite_concentration_ratio_zero
    (targetCount : Nat) (varianceBound : Real) :
    Tendsto (fun n =>
      (targetCount : Real) * ((n + 1 : Nat) : Real) *
        (varianceBound / safeFiniteReplicates n) /
        (safeResponseTolerance n) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hmain : Tendsto (fun n : ℕ =>
      (targetCount * varianceBound : ℝ) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using h1.const_mul (targetCount * varianceBound : ℝ)
  refine hmain.congr (fun n => ?_)
  have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [safeFiniteReplicates, safeResponseTolerance]
  push_cast
  field_simp

/-- Entropy-aware concentration ratio for polynomial-size shrinking nets.

The theorem is stated with an upper bound on net cardinality so applications do
not need an exact covering number formula.  The extra exponent in
`safeEntropyReplicates` leaves polynomial slack after the tolerance is squared.
-/
theorem safeEntropy_concentration_ratio_zero
    (entropyPower : Nat) (varianceBound coverConstant : Real)
    (centersCard : Nat → Nat)
    (hcard : ∀ n,
      (centersCard n : Real) ≤
        coverConstant * (((n + 1 : Nat) : Real) ^ entropyPower)) :
    Tendsto (fun n =>
      (centersCard n : Real) *
        (varianceBound / safeEntropyReplicates entropyPower n) /
        (safeNetTolerance n) ^ 2) atTop (𝓝 0) := by
  have hcov : 0 ≤ coverConstant := by
    have h := hcard 0
    simpa using le_trans (Nat.cast_nonneg (centersCard 0)) h
  have hpow2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ 2) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by omega))) tendsto_id
    have h2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 2) atTop atTop := by
      simp_rw [← Nat.cast_pow]; exact tendsto_natCast_atTop_atTop.comp hnat
    exact h2.inv_tendsto_atTop
  have hg : Tendsto (fun n : ℕ =>
      4 * coverConstant * |varianceBound| * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow2.const_mul (4 * coverConstant * |varianceBound|)
  refine squeeze_zero_norm (fun n => ?_) hg
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have hfeq : (centersCard n : ℝ) * (varianceBound / safeEntropyReplicates entropyPower n) /
      (safeNetTolerance n) ^ 2
      = 4 * varianceBound * ((centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹) *
          (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    simp only [safeEntropyReplicates, safeNetTolerance, safeResponseTolerance]
    push_cast
    rw [pow_add]
    (field_simp; ring)
  have hcard' : (centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹ ≤ coverConstant := by
    rw [mul_inv_le_iff₀ (by positivity)]
    simpa [mul_comm] using hcard n
  rw [hfeq, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)]
  have h4 : |4 * varianceBound| = 4 * |varianceBound| := by rw [abs_mul]; norm_num
  have hc2 : |(centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹|
      = (centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹ :=
    abs_of_nonneg (by positivity)
  rw [h4, hc2]
  calc 4 * |varianceBound| *
        ((centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹) *
          (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
      ≤ 4 * |varianceBound| * coverConstant * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by gcongr
    _ = 4 * coverConstant * |varianceBound| * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by ring

/-- A small enough shrinking-net radius fits inside the half-tolerance budget
when sample and population response maps have a common Lipschitz envelope.

This is elementary scalar bookkeeping.  It is separated because the infinite-
model capstone should ask for one radius inequality, not repeat a triangle-
inequality calculation in every application.
-/
theorem safe_net_extension_budget
    (Lsample Lpopulation radius : Nat → Real)
    (L : Real)
    (hL : 0 ≤ L)
    (hsampleNonneg : ∀ n, 0 ≤ Lsample n)
    (hpopulationNonneg : ∀ n, 0 ≤ Lpopulation n)
    (hradiusNonneg : ∀ n, 0 ≤ radius n)
    (hsample : ∀ n, Lsample n ≤ L)
    (hpopulation : ∀ n, Lpopulation n ≤ L)
    (hradius : ∀ n,
      radius n ≤ safeResponseTolerance n / (4 * (L + 1))) :
    ∀ n,
      safeNetTolerance n +
          (Lsample n + Lpopulation n) * radius n ≤
        safeResponseTolerance n := by
  intro n
  have hη : (0 : ℝ) ≤ safeResponseTolerance n := (safeResponseTolerance_pos n).le
  have hLpos : (0 : ℝ) < 4 * (L + 1) := by linarith
  have hratio : 2 * L / (4 * (L + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hLpos]
    nlinarith [hL]
  have hnet : safeNetTolerance n = safeResponseTolerance n / 2 := rfl
  have hprod : (Lsample n + Lpopulation n) * radius n ≤ safeResponseTolerance n / 2 :=
    calc (Lsample n + Lpopulation n) * radius n
        ≤ (2 * L) * (safeResponseTolerance n / (4 * (L + 1))) :=
          mul_le_mul (by linarith [hsample n, hpopulation n]) (hradius n)
            (hradiusNonneg n) (by linarith [hL])
      _ = (2 * L / (4 * (L + 1))) * safeResponseTolerance n := by ring
      _ ≤ (1 / 2) * safeResponseTolerance n := mul_le_mul_of_nonneg_right hratio hη
      _ = safeResponseTolerance n / 2 := by ring
  rw [hnet]
  linarith [hprod]

/-- **A natural power of `n + 1` tends to infinity**, cast to `ℝ`.

This is used by the explicit safe scaled-rate calculation below.  The improved
selected-block polar expression no longer needs an additional growing ambient
factor. -/
theorem tendsto_natCast_succ_pow_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ k) atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => (n + 1) ^ k) atTop atTop :=
    tendsto_atTop_mono
      (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by omega))) tendsto_id
  simp_rw [← Nat.cast_pow]
  exact tendsto_natCast_atTop_atTop.comp hnat

/-- The batch-size-scaled CMDS entry rate vanishes under the safe
tolerance.

This records the batch-scaled perturbation decay used elsewhere in the explicit
rate analysis.  `GrowingConfigControl` no longer needs it as a side-condition field.
-/
theorem safe_scaled_cmdsEntrywiseRate_zero
    (m : Nat) (hm : 0 < m) (populationResponseBound : Real) :
    Tendsto (fun n =>
      ((n + 1 : Nat) : Real) *
        cmdsEntrywiseRate (n + 1) m
          (responseDistBound m
            (populationResponseBound + safeResponseTolerance n))
          (safeResponseTolerance n)) atTop (𝓝 0) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h1 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h3 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) atTop (𝓝 0) := by
    simpa [inv_pow] using h1.pow 3
  have hfinal : Tendsto (fun n : ℕ => 32 * ((m : ℝ)⁻¹) ^ 2 *
      (populationResponseBound * (((n + 1 : ℕ) : ℝ))⁻¹
        + (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹)) atTop (𝓝 0) := by
    have := ((h1.const_mul populationResponseBound).add h3).const_mul (32 * ((m : ℝ)⁻¹) ^ 2)
    simpa using this
  refine hfinal.congr (fun n => ?_)
  have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [cmdsEntrywiseRate, responseEntrywiseRate, responseDistBound, safeResponseTolerance]
  (field_simp; ring)

/-- The former polar-factor side expression also vanishes under the safe tolerance.

The strengthened spectral theorem no longer requires this fact, but the limit is
retained as a useful quantitative consequence of the explicit schedule. -/
theorem safe_polar_expression_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound κ : Real) (hκ : 0 < κ) :
    Tendsto (fun n =>
      (d : Real) *
        (4 * (d : Real) *
          ((((n + 1 : Nat) : Real) *
            cmdsEntrywiseRate (n + 1) m
              (responseDistBound m
                (populationResponseBound + safeResponseTolerance n))
              (safeResponseTolerance n)) ^ 2) / (κ / 2) ^ 2))
      atTop (𝓝 0) := by
  let e : Nat → Real := fun n =>
    ((n + 1 : Nat) : Real) *
      cmdsEntrywiseRate (n + 1) m
        (responseDistBound m
          (populationResponseBound + safeResponseTolerance n))
        (safeResponseTolerance n)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using safe_scaled_cmdsEntrywiseRate_zero m hm populationResponseBound
  have hbase : Tendsto (fun n =>
      ((d : ℝ) * (4 * (d : ℝ)) / (κ / 2) ^ 2) * (e n * e n))
      atTop (𝓝 0) := by
    simpa using (he.mul he).const_mul
      ((d : ℝ) * (4 * (d : ℝ)) / (κ / 2) ^ 2)
  refine hbase.congr (fun n => ?_)
  simp only [e]
  ring

/-- The complete Frobenius configuration envelope vanishes under the retuned
schedule and linear population spectral ceiling.

With `safeResponseTolerance n = (n+1)⁻²`, the batch-scaled CMDS perturbation is
`O((n+1)⁻¹)`.  The DK-sharpened Frobenius terms then scale as `O((n+1)⁻¹/²)`
or faster even when the population spectral ceiling grows linearly.  The older
`configBound` endpoint would reintroduce `sqrt(n+1)` and does not support this
weaker schedule; the growing Quench path no longer uses that compatibility
norm. -/
theorem safe_configFrobBound_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hκ : 0 < κ) :
    Tendsto (fun n =>
      configFrobBound d (κ / 2)
        (4 * ((n + 1 : Nat) : Real) * perspectiveBound ^ 2)
        (((n + 1 : Nat) : Real) *
          cmdsEntrywiseRate (n + 1) m
            (responseDistBound m
              (populationResponseBound + safeResponseTolerance n))
            (safeResponseTolerance n))) atTop (𝓝 0) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hκ' : κ ≠ 0 := ne_of_gt hκ
  set en : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) *
      cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (populationResponseBound + safeResponseTolerance n))
        (safeResponseTolerance n) with hen
  have hpt : ∀ n : ℕ, en n = ((n + 1 : ℕ) : ℝ) *
      cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (populationResponseBound + safeResponseTolerance n))
        (safeResponseTolerance n) := fun n => by rw [hen]
  simp only [← hpt]
  have hu : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : Tendsto en atTop (𝓝 0) := by
    simpa only [hen] using
      safe_scaled_cmdsEntrywiseRate_zero m hm populationResponseBound
  -- One factor of `n+1` times the scaled perturbation has a finite limit.
  have hNen : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * en n) atTop
      (𝓝 (32 * ((m : ℝ)⁻¹) ^ 2 * populationResponseBound)) := by
    have h2 : Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℝ))⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using hu.pow 2
    have hconst : Tendsto (fun _ : ℕ => populationResponseBound) atTop
        (𝓝 populationResponseBound) := tendsto_const_nhds
    have hbase : Tendsto (fun n : ℕ =>
        32 * ((m : ℝ)⁻¹) ^ 2 *
          (populationResponseBound + ((((n + 1 : ℕ) : ℝ))⁻¹) ^ 2)) atTop
        (𝓝 (32 * ((m : ℝ)⁻¹) ^ 2 * populationResponseBound)) := by
      simpa only [add_zero] using
        (hconst.add h2).const_mul (32 * ((m : ℝ)⁻¹) ^ 2)
    refine hbase.congr (fun n => ?_)
    simp only [hen, cmdsEntrywiseRate, responseEntrywiseRate, responseDistBound,
      safeResponseTolerance]
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    (field_simp; ring)
  have hNe2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (en n) ^ 2)
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ =>
        en n * (((n + 1 : ℕ) : ℝ) * en n)) atTop (𝓝 0) := by
      simpa using he.mul hNen
    refine hbase.congr (fun n => ?_)
    ring
  have hNe4 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (en n) ^ 4)
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ =>
        (en n) ^ 3 * (((n + 1 : ℕ) : ℝ) * en n)) atTop (𝓝 0) := by
      simpa using (he.pow 3).mul hNen
    refine hbase.congr (fun n => ?_)
    ring
  have he2 : Tendsto (fun n : ℕ => (en n) ^ 2) atTop (𝓝 0) := by
    simpa using he.pow 2
  have he5 : Tendsto (fun n : ℕ => (en n) ^ 5) atTop (𝓝 0) := by
    simpa using he.pow 5
  -- First square-root term: `e_n^4 (Λ_n + e_n)`.
  have hsq1 : Tendsto (fun n : ℕ => Real.sqrt
      ((2 * ((d : ℝ) * (4 * (d : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) ^ 2 *
        ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2 + en n))))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ =>
        ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 *
            ((d : ℝ) * 4 * perspectiveBound ^ 2)) *
          (((n + 1 : ℕ) : ℝ) * (en n) ^ 4)
        + ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 * (d : ℝ)) *
          (en n) ^ 5) atTop (𝓝 0) := by
      simpa using
        (hNe4.const_mul
          ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 *
            ((d : ℝ) * 4 * perspectiveBound ^ 2))).add
        (he5.const_mul
          ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 * (d : ℝ)))
    have hlim : Tendsto (fun n : ℕ =>
        (2 * ((d : ℝ) * (4 * (d : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) ^ 2 *
          ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2 + en n)))
        atTop (𝓝 0) := by
      refine hbase.congr (fun n => ?_)
      field_simp
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  -- Second square-root term: a fixed multiple of `e_n^2`.
  have hsq2 : Tendsto (fun n : ℕ =>
      Real.sqrt ((d : ℝ) * (en n / Real.sqrt ((κ / 2) / 2)) ^ 2))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (d : ℝ) * (en n / Real.sqrt ((κ / 2) / 2)) ^ 2) atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ =>
          ((d : ℝ) / ((κ / 2) / 2)) * (en n) ^ 2) atTop (𝓝 0) := by
        simpa using he2.const_mul ((d : ℝ) / ((κ / 2) / 2))
      refine hbase.congr (fun n => ?_)
      have hc : Real.sqrt ((κ / 2) / 2) ^ 2 = (κ / 2) / 2 :=
        Real.sq_sqrt (by positivity)
      rw [div_pow, hc]
      field_simp
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  -- Third square-root term: a fixed multiple of `(n+1) e_n^2`.
  have hsq3 : Tendsto (fun n : ℕ => Real.sqrt
      ((4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2) *
        (4 * (d : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2) *
          (4 * (d : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ =>
          (16 * (d : ℝ) * perspectiveBound ^ 2 / (κ / 2) ^ 2) *
            (((n + 1 : ℕ) : ℝ) * (en n) ^ 2)) atTop (𝓝 0) := by
        simpa using hNe2.const_mul
          (16 * (d : ℝ) * perspectiveBound ^ 2 / (κ / 2) ^ 2)
      refine hbase.congr (fun n => ?_)
      (field_simp; ring)
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  unfold configFrobBound
  simpa using (hsq1.add hsq2).add hsq3

/-- The conservative tolerance and linear spectral ceiling satisfy every field
of `GrowingConfigControl` for the current proved CMDS perturbation bound.

The certificate now controls the Frobenius configuration bound directly, so
the growing Quench path avoids the legacy `sqrt(n+1)` conversion.  Completing
this theorem removes `Hrate`, entrywise nonnegativity, the local smallness
inequality, the polar inequality, and the vanishing configuration bound from
the final public theorem.  The second-power response tolerance is the smallest
integer-power choice that makes the proved batch-scaled CMDS perturbation
vanish; no legacy
`ConfigError` factor is included in this schedule.
-/
noncomputable def safe_growingConfigControl
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hresponse : 0 ≤ populationResponseBound)
    (hperspective : 0 ≤ perspectiveBound)
    (hκ : 0 < κ) :
    GrowingConfigControl (fun n => n + 1) d (κ / 2)
      (fun n => 4 * ((n + 1 : Nat) : Real) * perspectiveBound ^ 2)
      (fun n => cmdsEntrywiseRate (n + 1) m
        (responseDistBound m
          (populationResponseBound + safeResponseTolerance n))
        (safeResponseTolerance n)) :=
  GrowingConfigControl.of_tendsto
    (fun n => by
      simp only [cmdsEntrywiseRate, responseEntrywiseRate, responseDistBound, safeResponseTolerance]
      positivity)
    (safe_configFrobBound_zero m d hm populationResponseBound perspectiveBound κ hκ)

end DkpsQuench2026
