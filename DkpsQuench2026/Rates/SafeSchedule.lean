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

/-- Conservative response-mean tolerance.

The first power suffices.  The spectral certificate reports the population Gram
floor at its true scale `n·(κ/2)` rather than a constant, so the conditioning
ratio `ceiling/floor` in the Davis--Kahan configuration bound is bounded instead
of growing linearly in `n`.  That removes one power of `(n+1)` from every term of
`configFrobBound`, and the batch-scaled CMDS perturbation is then allowed to stay
bounded rather than having to vanish. -/
noncomputable def safeResponseTolerance (n : Nat) : Real :=
  (((n + 1 : Nat) : Real))⁻¹

/-- Conservative finite-model replicate budget. -/
def safeFiniteReplicates (n : Nat) : Nat :=
  (n + 1) ^ 4

/-- Replicate budget allowing a stage net with polynomial cardinality
`O((n+1)^entropyPower)`. -/
def safeEntropyReplicates (entropyPower n : Nat) : Nat :=
  (n + 1) ^ (4 + entropyPower)

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
  exact inv_pos.mpr (by positivity : (0 : Real) < ((n + 1 : Nat) : Real))

theorem safeFiniteReplicates_pos (n : Nat) :
    0 < safeFiniteReplicates n := by
  rw [safeFiniteReplicates]
  exact pow_pos (Nat.succ_pos n) 4

theorem safeEntropyReplicates_pos (entropyPower n : Nat) :
    0 < safeEntropyReplicates entropyPower n := by
  rw [safeEntropyReplicates]
  exact pow_pos (Nat.succ_pos n) (4 + entropyPower)

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
    have h1 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id)
    exact h1.inv_tendsto_atTop
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
        C * (((n + 1 : Nat) : Real) ^ d)) ∧
      (∀ n, net.radius n = safePerspectiveRadius L n) := by
  obtain ⟨net, C0, hC0, hcard0, hradius⟩ :=
    exists_growingPerspectiveNet_with_polynomial_card ψ hcompact
      (safePerspectiveRadius L) (safePerspectiveRadius_pos L hL) (safePerspectiveRadius_zero L hL)
  refine ⟨net, C0 * (1 + 4 * (L + 1)) ^ d, by positivity, fun n => ?_, hradius⟩
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hpos2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hinv : (safePerspectiveRadius L n)⁻¹ = 4 * (L + 1) * ((n + 1 : ℕ) : ℝ) := by
    rw [safePerspectiveRadius, safeResponseTolerance, inv_div, div_eq_mul_inv, inv_inv]
  have hmax : max 1 (safePerspectiveRadius L n)⁻¹ ≤ (1 + 4 * (L + 1)) * ((n + 1 : ℕ) : ℝ) := by
    rw [hinv]
    refine max_le ?_ ?_
    · nlinarith [h1, hL, mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * (L + 1)) hpos2]
    · nlinarith [hpos2, hL]
  calc ((net.centers n).card : ℝ)
      ≤ C0 * (max 1 (safePerspectiveRadius L n)⁻¹) ^ d := hcard0 n
    _ ≤ C0 * ((1 + 4 * (L + 1)) * ((n + 1 : ℕ) : ℝ)) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax d) hC0
    _ = C0 * (1 + 4 * (L + 1)) ^ d * (((n + 1 : ℕ) : ℝ)) ^ d := by
        rw [mul_pow]; ring

/-- The conservative response tolerance vanishes.
-/
theorem safeResponseTolerance_zero :
    Tendsto safeResponseTolerance atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id)
  exact h1.inv_tendsto_atTop

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

/-- **The source's replicate condition**, `r = omega(n^3)`.

Acharyya et al. (2025) Theorem 2, which Quench imports as its Theorem 1, requires the replicate
budget to grow faster than the cube of the model count.  This is that condition, and it is
exactly what the finite-model concentration ratio needs: the ratio is a constant divided by
`r n / (n+1)^3`. -/
def SourceReplicateRate (r : Nat → Nat) : Prop :=
  Tendsto (fun n : Nat => (r n : Real) / (((n : Real) + 1)) ^ 3) atTop atTop

/-- The finite-model Chebyshev/union-bound ratio vanishes under *any* replicate schedule
meeting the source rate, not merely the hardcoded one. -/
theorem finite_concentration_ratio_zero_of_sourceRate
    {r : Nat → Nat} (hr : SourceReplicateRate r)
    (targetCount : Nat) (varianceBound : Real) :
    Tendsto (fun n =>
      (targetCount : Real) * ((n + 1 : Nat) : Real) *
        (varianceBound / r n) /
        (safeResponseTolerance n) ^ 2) atTop (𝓝 0) := by
  have hmain : Tendsto (fun n : Nat =>
      (targetCount * varianceBound : Real) / ((r n : Real) / (((n : Real) + 1)) ^ 3))
      atTop (𝓝 0) := hr.const_div_atTop _
  refine hmain.congr (fun n => ?_)
  have hpos : ((n : Real) + 1) ≠ 0 := by positivity
  simp only [safeResponseTolerance]
  push_cast
  field_simp

/-- The hardcoded schedule meets the source rate. -/
theorem sourceReplicateRate_safeFiniteReplicates :
    SourceReplicateRate safeFiniteReplicates := by
  have h : Tendsto (fun n : Nat => ((n : Real) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hpos : ((n : Real) + 1) ≠ 0 := by positivity
  simp only [safeFiniteReplicates]
  push_cast
  field_simp

/-- **The net-adjusted replicate condition.**

The compact-infinite route buys uniformity over an infinite model class with a union bound over
a shrinking perspective net of polynomial cardinality `O((n+1)^entropyPower)`.  That costs
`entropyPower` powers on top of what the finite route needs, and this is the resulting
condition on the replicate budget.  It reduces to the finite requirement when the net is
trivial, and the gap to the source's `r = omega(n^3)` is exactly the price of the net. -/
def NetReplicateRate (entropyPower : Nat) (r : Nat → Nat) : Prop :=
  Tendsto (fun n : Nat => (r n : Real) / (((n : Real) + 1)) ^ (2 + entropyPower)) atTop atTop

/-- The entropy-aware concentration ratio vanishes under *any* replicate schedule meeting the
net-adjusted rate. -/
theorem entropy_concentration_ratio_zero_of_netRate
    (entropyPower : Nat) {r : Nat → Nat} (hr : NetReplicateRate entropyPower r)
    (varianceBound coverConstant : Real)
    (centersCard : Nat → Nat)
    (hcard : ∀ n,
      (centersCard n : Real) ≤
        coverConstant * (((n + 1 : Nat) : Real) ^ entropyPower)) :
    Tendsto (fun n =>
      (centersCard n : Real) * (varianceBound / r n) /
        (safeNetTolerance n) ^ 2) atTop (𝓝 0) := by
  have hcov : 0 ≤ coverConstant := by
    have h := hcard 0
    simpa using le_trans (Nat.cast_nonneg (centersCard 0)) h
  have hinv : Tendsto (fun n : Nat =>
      (((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real)) atTop (𝓝 0) := by
    have := hr.inv_tendsto_atTop
    refine this.congr (fun n => ?_)
    simp only [Pi.inv_apply]
    rw [inv_div]
  have hg : Tendsto (fun n : Nat =>
      4 * coverConstant * |varianceBound| *
        ((((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hinv.const_mul (4 * coverConstant * |varianceBound|)
  refine squeeze_zero_norm (fun n => ?_) hg
  have hNpos : (0 : Real) < ((n : Real) + 1) := by positivity
  rcases eq_or_ne (r n : Real) 0 with hr0 | hr0
  · have hnn : (0 : Real) ≤ 4 * coverConstant * |varianceBound| *
        ((((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real)) := by
      rw [hr0]
      simp
    simpa [hr0] using hnn
  · have hfeq : (centersCard n : Real) * (varianceBound / r n) / (safeNetTolerance n) ^ 2
        = 4 * varianceBound * ((centersCard n : Real) * (((n : Real) + 1) ^ entropyPower)⁻¹) *
            ((((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real)) := by
      simp only [safeNetTolerance, safeResponseTolerance]
      push_cast
      rw [pow_add]
      field_simp
      ring
    have hcard' : (centersCard n : Real) * (((n : Real) + 1) ^ entropyPower)⁻¹
        ≤ coverConstant := by
      rw [mul_inv_le_iff₀ (by positivity)]
      have := hcard n
      push_cast at this
      simpa [mul_comm] using this
    have hcard0 : (0 : Real) ≤ (centersCard n : Real) * (((n : Real) + 1) ^ entropyPower)⁻¹ := by
      positivity
    have hquot : (0 : Real) ≤ (((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real) := by
      have : (0 : Real) ≤ (r n : Real) := Nat.cast_nonneg _
      positivity
    rw [hfeq, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hcard0,
      abs_of_nonneg hquot, abs_mul]
    have h4 : |(4 : Real)| = 4 := by norm_num
    rw [h4]
    have hstep : 4 * |varianceBound| *
        ((centersCard n : Real) * (((n : Real) + 1) ^ entropyPower)⁻¹)
        ≤ 4 * |varianceBound| * coverConstant := by
      have : (0 : Real) ≤ 4 * |varianceBound| := by positivity
      exact mul_le_mul_of_nonneg_left hcard' this
    calc 4 * |varianceBound| *
          ((centersCard n : Real) * (((n : Real) + 1) ^ entropyPower)⁻¹) *
          ((((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real))
        ≤ 4 * |varianceBound| * coverConstant *
          ((((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real)) :=
          mul_le_mul_of_nonneg_right hstep hquot
      _ = 4 * coverConstant * |varianceBound| *
          ((((n : Real) + 1) ^ (2 + entropyPower)) / (r n : Real)) := by ring

/-- The hardcoded entropy schedule meets the net-adjusted rate, with two powers to spare. -/
theorem netReplicateRate_safeEntropyReplicates (entropyPower : Nat) :
    NetReplicateRate entropyPower (safeEntropyReplicates entropyPower) := by
  have h : Tendsto (fun n : Nat => (((n : Real) + 1)) ^ 2) atTop atTop := by
    have h1 : Tendsto (fun n : Nat => ((n : Real) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : Real => x ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    exact h2.comp h1
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hpos : (0 : Real) < ((n : Real) + 1) := by positivity
  simp only [safeEntropyReplicates]
  push_cast
  rw [show (4 + entropyPower) = (2 + entropyPower) + 2 by omega, pow_add]
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

/-- The batch-scaled CMDS perturbation converges to an explicit constant.

Under the retuned first-power tolerance the batch scale `(n+1)` exactly cancels
the tolerance, so this quantity no longer vanishes -- it settles at
`32 m⁻² R`.  That is the point of the retune: with the spectral floor reported at
its true scale `n(κ/2)`, `configFrobBound` only needs the perturbation to stay
bounded, not to vanish, and the tolerance may therefore be a whole power of
`(n+1)` looser. -/
theorem safe_scaled_cmdsEntrywiseRate_tendsto
    (m : Nat) (hm : 0 < m) (populationResponseBound : Real) :
    Tendsto (fun n =>
      ((n + 1 : Nat) : Real) *
        cmdsEntrywiseRate (n + 1) m
          (responseDistBound m
            (populationResponseBound + safeResponseTolerance n))
          (safeResponseTolerance n)) atTop
      (𝓝 (32 * ((m : Real)⁻¹) ^ 2 * populationResponseBound)) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h1 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfinal : Tendsto (fun n : ℕ => 32 * ((m : ℝ)⁻¹) ^ 2 *
      (populationResponseBound + (((n + 1 : ℕ) : ℝ))⁻¹)) atTop
      (𝓝 (32 * ((m : ℝ)⁻¹) ^ 2 * populationResponseBound)) := by
    have := ((tendsto_const_nhds (x := populationResponseBound)
      (f := atTop (α := ℕ))).add h1).const_mul (32 * ((m : ℝ)⁻¹) ^ 2)
    simpa using this
  refine hfinal.congr (fun n => ?_)
  have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [cmdsEntrywiseRate, responseEntrywiseRate, responseDistBound, safeResponseTolerance]
  (field_simp; ring)

/-- The complete Frobenius configuration envelope vanishes under the retuned
schedule, the linear population spectral ceiling, and the linear spectral floor.

Every term of `configFrobBound d α Λ ε` is a ratio in which `α` appears squared
or under a square root while `Λ` appears linearly.  Reporting the floor at its
true scale `α_n = n(κ/2)` against the ceiling `Λ_n = 4(n+1)B²` therefore makes
the conditioning ratio bounded rather than linear in `n`:

* `√(Λ · 4dε²/α²) ~ ε √((n+1)/n²)`,
* `√(d(ε/√α)²) ~ ε/√n`, and
* `√((2d·4dε²/α²)² · d(Λ+ε)) ~ ε⁴ √(n+1)/n⁴`.

All three vanish for a merely *bounded* `ε`, which is what buys the looser
first-power response tolerance.  With the old constant floor the first two terms
carried a factor `√n` and forced `ε → 0`. -/
theorem safe_configFrobBound_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hκ : 0 < κ) :
    Tendsto (fun n : Nat =>
      configFrobBound d (max ((n : Real)) 1 * (κ / 2))
        (4 * ((n + 1 : Nat) : Real) * perspectiveBound ^ 2)
        (((n + 1 : Nat) : Real) *
          cmdsEntrywiseRate (n + 1) m
            (responseDistBound m
              (populationResponseBound + safeResponseTolerance n))
            (safeResponseTolerance n))) atTop (𝓝 0) := by
  have hκ2 : (0 : ℝ) < κ / 2 := by linarith
  set en : ℕ → ℝ := fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (populationResponseBound + safeResponseTolerance n))
        (safeResponseTolerance n) with hen
  have heLim : Tendsto en atTop
      (𝓝 (32 * ((m : ℝ)⁻¹) ^ 2 * populationResponseBound)) :=
    safe_scaled_cmdsEntrywiseRate_tendsto m hm populationResponseBound
  -- polynomial ratios that vanish against the linear floor
  have hN : Tendsto (fun n : ℕ => ((n : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) := hN.inv_tendsto_atTop
  have hratio : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ + ((n : ℝ))⁻¹ * ((n : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa using hinv.add (hinv.mul hinv)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : ((n : ℝ)) ≠ 0 := by positivity
    field_simp
    try ring
  have hratio4 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ) ^ 4)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ =>
        (((n : ℝ) + 1) / (n : ℝ) ^ 2) * (((n : ℝ))⁻¹ * ((n : ℝ))⁻¹)) atTop (𝓝 0) := by
      simpa using hratio.mul (hinv.mul hinv)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : ((n : ℝ)) ≠ 0 := by positivity
    field_simp
    try ring
  -- the three configFrobBound terms, each as a vanishing sequence times a convergent one
  have hT1 : Tendsto (fun n : ℕ =>
      (2 * ((d : ℝ) * (4 * (d : ℝ) * (en n) ^ 2 / ((n : ℝ) * (κ / 2)) ^ 2))) ^ 2 *
        ((d : ℝ) * (4 * (((n + 1 : ℕ)) : ℝ) * perspectiveBound ^ 2 + en n))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ =>
        ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 * ((d : ℝ) * 4 * perspectiveBound ^ 2))
            * ((en n) ^ 4 * (((n : ℝ) + 1) / (n : ℝ) ^ 4))
          + ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 * (d : ℝ))
            * ((en n) ^ 4 * en n * ((n : ℝ) ^ 4)⁻¹)) atTop (𝓝 0) := by
      have h4 : Tendsto (fun n : ℕ => ((n : ℝ) ^ 4)⁻¹) atTop (𝓝 0) := by
        simpa [inv_pow] using hinv.pow 4
      have ha := ((heLim.pow 4).mul hratio4).const_mul
        ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 * ((d : ℝ) * 4 * perspectiveBound ^ 2))
      have hb := (((heLim.pow 4).mul heLim).mul h4).const_mul
        ((2 * ((d : ℝ) * (4 * (d : ℝ) / (κ / 2) ^ 2))) ^ 2 * (d : ℝ))
      simpa using ha.add hb
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : ((n : ℝ)) ≠ 0 := by positivity
    have hk0 : (κ / 2) ≠ 0 := ne_of_gt hκ2
    push_cast
    field_simp
    try ring
  have hT2 : Tendsto (fun n : ℕ =>
      (d : ℝ) * (en n / Real.sqrt ((n : ℝ) * (κ / 2))) ^ 2) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ =>
        ((d : ℝ) / (κ / 2)) * ((en n) ^ 2 * ((n : ℝ))⁻¹)) atTop (𝓝 0) := by
      simpa using ((heLim.pow 2).mul hinv).const_mul ((d : ℝ) / (κ / 2))
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq : Real.sqrt ((n : ℝ) * (κ / 2)) ^ 2 = (n : ℝ) * (κ / 2) :=
      Real.sq_sqrt (by positivity)
    rw [div_pow, hsq]
    field_simp
    try ring
  have hT3 : Tendsto (fun n : ℕ =>
      (4 * (((n + 1 : ℕ)) : ℝ) * perspectiveBound ^ 2) *
        (4 * (d : ℝ) * (en n) ^ 2 / ((n : ℝ) * (κ / 2)) ^ 2)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ =>
        (16 * (d : ℝ) * perspectiveBound ^ 2 / (κ / 2) ^ 2) *
          ((en n) ^ 2 * (((n : ℝ) + 1) / (n : ℝ) ^ 2))) atTop (𝓝 0) := by
      simpa using ((heLim.pow 2).mul hratio).const_mul
        (16 * (d : ℝ) * perspectiveBound ^ 2 / (κ / 2) ^ 2)
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : ((n : ℝ)) ≠ 0 := by positivity
    have hk0 : (κ / 2) ≠ 0 := ne_of_gt hκ2
    push_cast
    field_simp
    try ring
  have hsqrt : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => Real.sqrt (f n)) atTop (𝓝 0) := by
    intro f hf
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hf
    rwa [Real.sqrt_zero] at h
  have hsum := ((hsqrt hT1).add (hsqrt hT2)).add (hsqrt hT3)
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmax : max ((n : ℝ)) 1 = (n : ℝ) := max_eq_left hn1
  simp only [configFrobBound, hmax, hen]

/-- The conservative tolerance and linear spectral ceiling satisfy every field
of `GrowingConfigControl` for the current proved CMDS perturbation bound.

The certificate now controls the Frobenius configuration bound directly, so
the growing Quench path avoids the legacy `sqrt(n+1)` conversion.  Completing
this theorem removes `Hrate`, entrywise nonnegativity, the local smallness
inequality, the polar inequality, and the vanishing configuration bound from
the final public theorem.  The floor is the stage-scaled `max n 1 · (κ/2)`: the `max` only keeps it
positive at `n = 0`, where the spectral certificate's event is empty anyway.
Reporting the floor at that scale rather than as the constant `κ/2` is what
allows the first-power response tolerance; no legacy `ConfigError` factor is
included in this schedule.
-/
noncomputable def safe_growingConfigControl
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hresponse : 0 ≤ populationResponseBound)
    (hperspective : 0 ≤ perspectiveBound)
    (hκ : 0 < κ) :
    GrowingConfigControl (fun n => n + 1) d
      (fun n : Nat => max ((n : Real)) 1 * (κ / 2))
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
