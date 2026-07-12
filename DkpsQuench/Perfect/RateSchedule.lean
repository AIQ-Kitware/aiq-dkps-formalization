/-
Explicit conservative schedules for Perfect Quench.

The current public bridge accepts abstract limit certificates.  This module
provides one deliberately loose polynomial schedule that discharges those
limits automatically.  The constants are not intended to be optimal; the goal
is a theorem whose users choose a response budget, not a collection of
asymptotic side proofs.
-/

import DkpsQuench.Perfect.UniformConcentration

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

namespace DkpsQuench.Perfect

open Acharyya2025.Bridge
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open Acharyya2025.ConfigPerturbation

/-- Conservative response-mean tolerance.  The fifth power is chosen to beat
the intentionally loose growing CMDS bound, including its final
configuration-error factor. -/
noncomputable def safeResponseTolerance (n : Nat) : Real :=
  ((((n + 1 : Nat) : Real) ^ 5))⁻¹

/-- Conservative finite-model replicate budget. -/
def safeFiniteReplicates (n : Nat) : Nat :=
  (n + 1) ^ 13

/-- Replicate budget allowing a stage net with polynomial cardinality
`O((n+1)^entropyPower)`. -/
def safeEntropyReplicates (entropyPower n : Nat) : Nat :=
  (n + 1) ^ (13 + entropyPower)

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
  exact inv_pos.mpr (pow_pos (by positivity : (0 : Real) < ((n + 1 : Nat) : Real)) 5)

theorem safeFiniteReplicates_pos (n : Nat) :
    0 < safeFiniteReplicates n := by
  rw [safeFiniteReplicates]
  exact pow_pos (Nat.succ_pos n) 13

theorem safeEntropyReplicates_pos (entropyPower n : Nat) :
    0 < safeEntropyReplicates entropyPower n := by
  rw [safeEntropyReplicates]
  exact pow_pos (Nat.succ_pos n) (13 + entropyPower)

theorem safePerspectiveRadius_pos
    (L : Real) (hL : 0 ≤ L) (n : Nat) :
    0 < safePerspectiveRadius L n := by
  rw [safePerspectiveRadius]
  have hden : (0 : Real) < 4 * (L + 1) := by nlinarith
  exact div_pos (safeResponseTolerance_pos n) hden

/-- The canonical perspective-net radius vanishes for every nonnegative fixed
Lipschitz constant.

Implementation recipe (execute in this order):
1. Unfold `safePerspectiveRadius`; set the positive constant
   `c := (4 * (L + 1))⁻¹` and prove it is finite using `hL`.
2. Rewrite the function as `fun n => c * safeResponseTolerance n`.
3. Apply `safeResponseTolerance_zero.const_mul c` after that theorem is
   available; if declaration order prevents this, prove directly from
   `tendsto_natCast_atTop_atTop`, `tendsto_pow_atTop_atTop_of_one_lt`, and
   `tendsto_inv_atTop_zero` for power five.
4. Close scalar normalization with `ring`/`field_simp`; no epsilon proof is
   necessary.
-/
theorem safePerspectiveRadius_zero
    (L : Real) (hL : 0 ≤ L) :
    Tendsto (safePerspectiveRadius L) atTop (𝓝 0) := by
  have h0 : Tendsto safeResponseTolerance atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ 5) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by norm_num)))
        tendsto_id
    have h5 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 5) atTop atTop := by
      simp_rw [← Nat.cast_pow]
      exact tendsto_natCast_atTop_atTop.comp hnat
    exact h5.inv_tendsto_atTop
  unfold safePerspectiveRadius
  simpa using h0.div_const (4 * (L + 1))

/-- Compact finite-dimensional perspective ranges admit canonical safe nets
with polynomial stage cardinality.

Proof plan:

1. apply `exists_growingPerspectiveNet_with_polynomial_card` to
   `safePerspectiveRadius L`;
2. rewrite the inverse radius as a fixed constant times `(n+1)^5`;
3. raise that estimate to dimension `d`;
4. absorb every fixed factor and all `max 1` early-stage slack into `C`.

This result removes the net, radius, entropy exponent, and covering-number
certificate from the final infinite-model theorem.

Implementation recipe (execute in this order):
1. Apply `exists_growingPerspectiveNet_with_polynomial_card` with radius
   `safePerspectiveRadius L`, positivity
   `safePerspectiveRadius_pos L hL`, and limit `safePerspectiveRadius_zero`.
2. Obtain `net`, a cover constant `C0`, its polynomial inverse-radius bound, and
   the radius identity.
3. Prove a fixed constant `K` such that
   `max 1 (safePerspectiveRadius L n)⁻¹ ≤ K * (n+1)^5` for every `n`; unfold the
   radius and use `safeResponseTolerance` plus `hL`.
4. Raise this inequality to power `d` using `pow_le_pow_left₀`; combine with the
   existing card bound.
5. Choose `C := C0 * K^d` (or a larger nonnegative max) and normalize
   `((n+1)^5)^d = (n+1)^(5*d)` with `pow_mul`.
6. Return the original `net` and exact radius equality; absorb all small-stage
   slack into `C`, never by adding a lower bound on `n`.
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
        C * (((n + 1 : Nat) : Real) ^ (5 * d))) ∧
      (∀ n, net.radius n = safePerspectiveRadius L n) := by
  obtain ⟨net, C0, hC0, hcard0, hradius⟩ :=
    exists_growingPerspectiveNet_with_polynomial_card ψ hcompact
      (safePerspectiveRadius L) (safePerspectiveRadius_pos L hL) (safePerspectiveRadius_zero L hL)
  refine ⟨net, C0 * (1 + 4 * (L + 1)) ^ d, by positivity, fun n => ?_, hradius⟩
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 5 :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
  have hpos5 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 5 := by positivity
  have hinv : (safePerspectiveRadius L n)⁻¹ = 4 * (L + 1) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
    rw [safePerspectiveRadius, safeResponseTolerance, inv_div, div_eq_mul_inv, inv_inv]
  have hmax : max 1 (safePerspectiveRadius L n)⁻¹ ≤ (1 + 4 * (L + 1)) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
    rw [hinv]
    refine max_le ?_ ?_
    · nlinarith [h1, hL, mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * (L + 1)) hpos5]
    · nlinarith [hpos5, hL]
  calc ((net.centers n).card : ℝ)
      ≤ C0 * (max 1 (safePerspectiveRadius L n)⁻¹) ^ d := hcard0 n
    _ ≤ C0 * ((1 + 4 * (L + 1)) * ((n + 1 : ℕ) : ℝ) ^ 5) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax d) hC0
    _ = C0 * (1 + 4 * (L + 1)) ^ d * (((n + 1 : ℕ) : ℝ)) ^ (5 * d) := by
        rw [mul_pow, ← pow_mul]; ring

/-- The conservative response tolerance vanishes.

Implementation recipe (execute in this order):
1. Unfold `safeResponseTolerance`.
2. Prove `((n+1 : Nat) : Real) → ∞` with `tendsto_natCast_atTop_atTop` composed
   with `tendsto_add_atTop_nat`.
3. Raise to the fifth power using `tendsto_pow_atTop_atTop_of_one_lt` or the
   monotone polynomial API.
4. Apply `tendsto_inv_atTop_zero`.
5. Use `simpa` to match the exact coercion and power syntax.  Avoid manual
   epsilon estimates.
-/
theorem safeResponseTolerance_zero :
    Tendsto safeResponseTolerance atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n + 1) ^ 5) atTop atTop :=
    tendsto_atTop_mono
      (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by norm_num)))
      tendsto_id
  have h5 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 5) atTop atTop := by
    simp_rw [← Nat.cast_pow]
    exact tendsto_natCast_atTop_atTop.comp hnat
  exact h5.inv_tendsto_atTop

/-- The finite-model Chebyshev/union-bound ratio vanishes under the safe
replicate schedule.

Suggested proof route: rewrite every term as a power of `n+1`; after cancelling
powers, dominate the expression by a constant times `(n+1)⁻²`.  Use the
existing `tendsto_pow_atTop_nhds_zero_of_lt_one` or polynomial-at-infinity API
rather than epsilon arithmetic.

Implementation recipe (execute in this order):
1. Unfold `safeFiniteReplicates`, `safeResponseTolerance`, and division; rewrite
   natural powers after coercion with `Nat.cast_pow`.
2. On all stages, normalize the expression algebraically to
   `(targetCount * varianceBound) * (((n+1 : Nat) : Real)⁻¹)^2` (or an even
   smaller inverse power); use `field_simp` only after proving `n+1 ≠ 0`.
3. Prove `(((n+1 : Nat) : Real)⁻¹)^2 → 0` from the inverse-at-infinity theorem
   and `Tendsto.pow`.
4. Multiply by the fixed constant with `Tendsto.const_mul`.
5. The theorem is valid even when `varianceBound` is negative, so avoid order
   arguments; use exact algebra and limits.
-/
theorem safeFinite_concentration_ratio_zero
    (targetCount : Nat) (varianceBound : Real) :
    Tendsto (fun n =>
      (targetCount : Real) * ((n + 1 : Nat) : Real) *
        (varianceBound / safeFiniteReplicates n) /
        (safeResponseTolerance n) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hlim : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  have hmain : Tendsto (fun n : ℕ =>
      (targetCount * varianceBound : ℝ) * (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hlim.const_mul (targetCount * varianceBound : ℝ)
  refine hmain.congr (fun n => ?_)
  have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [safeFiniteReplicates, safeResponseTolerance]
  push_cast
  field_simp

/-- Entropy-aware concentration ratio for polynomial-size shrinking nets.

The theorem is stated with an upper bound on net cardinality so applications do
not need an exact covering number formula.  The extra exponent in
`safeEntropyReplicates` leaves polynomial slack after the tolerance is squared.

Implementation recipe (execute in this order):
1. Let `a n` be the nonnegative target expression and replace
   `centersCard n` with its upper bound from `hcard`; if constants may be
   negative, first enlarge `coverConstant` and `varianceBound` by `max 0` or
   prove the target by exact algebra when possible.
2. Unfold `safeEntropyReplicates` and `safeNetTolerance`; rewrite all casts and
   powers of `n+1`.
3. Show the resulting upper bound is a fixed constant times at most
   `((n+1 : Nat) : Real)⁻²`; the exponent calculation is
   `entropyPower + 10 - (13 + entropyPower) = -3`, with one spare power.
4. Apply squeeze with nonnegativity of the original ratio and the inverse-power
   limit.
5. If sign assumptions make squeeze awkward, split on `varianceBound ≤ 0`; in
   that branch the second-moment application is trivial, and in the positive
   branch all factors are nonnegative.
6. Keep this theorem independent of any particular net structure.
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
  have hpow3 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ 3) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by omega))) tendsto_id
    have h3 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ 3) atTop atTop := by
      simp_rw [← Nat.cast_pow]; exact tendsto_natCast_atTop_atTop.comp hnat
    exact h3.inv_tendsto_atTop
  have hg : Tendsto (fun n : ℕ =>
      4 * coverConstant * |varianceBound| * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow3.const_mul (4 * coverConstant * |varianceBound|)
  refine squeeze_zero_norm (fun n => ?_) hg
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have hfeq : (centersCard n : ℝ) * (varianceBound / safeEntropyReplicates entropyPower n) /
      (safeNetTolerance n) ^ 2
      = 4 * varianceBound * ((centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹) *
          (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ := by
    simp only [safeEntropyReplicates, safeNetTolerance, safeResponseTolerance]
    push_cast
    rw [pow_add]
    field_simp
    ring
  have hcard' : (centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹ ≤ coverConstant := by
    rw [mul_inv_le_iff₀ (by positivity)]
    simpa [mul_comm] using hcard n
  rw [hfeq, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹)]
  have h4 : |4 * varianceBound| = 4 * |varianceBound| := by rw [abs_mul]; norm_num
  have hc2 : |(centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹|
      = (centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹ :=
    abs_of_nonneg (by positivity)
  rw [h4, hc2]
  calc 4 * |varianceBound| *
        ((centersCard n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ entropyPower)⁻¹) *
          (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹
      ≤ 4 * |varianceBound| * coverConstant * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ := by gcongr
    _ = 4 * coverConstant * |varianceBound| * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ := by ring

/-- A small enough shrinking-net radius fits inside the half-tolerance budget
when sample and population response maps have a common Lipschitz envelope.

This is elementary scalar bookkeeping.  It is separated because the infinite-
model capstone should ask for one radius inequality, not repeat a triangle-
inequality calculation in every application.

Implementation recipe (execute in this order):
1. Fix `n`; abbreviate `η := safeResponseTolerance n` and note `0 < η`.
2. Use `hsampleNonneg n`, `hpopulationNonneg n`, `hsample n`, and
   `hpopulation n` to obtain
   `0 ≤ Lsample n + Lpopulation n ≤ 2 * L`.
3. Use `hradiusNonneg n` and `hradius n` with
   `mul_le_mul_of_nonneg_left` to bound the extension term by
   `(2 * L) * (η / (4 * (L + 1)))`.
4. Substitute `safeNetTolerance n = η/2` and the definition of
   `safePerspectiveRadius`.
5. Show `2 * L / (4 * (L + 1)) ≤ 1/2` from `hL`; multiply by `η ≥ 0` and finish
   by `nlinarith` or `field_simp` followed by `nlinarith`.
6. The explicit nonnegativity premises are essential for the multiplication
   steps; do not remove them or infer them from upper bounds alone.
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

/-- The batch-size-scaled CMDS entry rate vanishes under the safe
tolerance.

Unfold the response and CMDS rates, use `hm` to simplify the inverse query
count safely, and compare powers of `n+1`.  This is the exact limit used by the
local spectral-smallness field of `GrowingConfigControl`.

Implementation recipe (execute in this order):
1. Unfold `cmdsEntrywiseRate`, `responseFrobRate`, `responseDistBound`, and
   `safeResponseTolerance`; rewrite the inverse of `(m : Real)` using `hm` only
   to establish it is a fixed finite constant.
2. Expand the expression and collect every fixed factor into one constant.
3. Count powers of `N := ((n+1 : Nat) : Real)`: the scaled rate is bounded by a
   constant times `N^3 * N⁻5`, hence `O(N⁻2)`; the extra term containing
   `safeResponseTolerance` decays faster.
4. Prove the inverse-power limits and combine them with `Tendsto.add`,
   `Tendsto.mul`, and constant multiplication.
5. Use exact ring normalization in a local equality before applying limits; do
   not attempt to make `simp` discover the exponent arithmetic automatically.
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
  have hpow : ∀ k : ℕ, 1 ≤ k → Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ k) atTop atTop := by
    intro k hk
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ k) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by omega))) tendsto_id
    simp_rw [← Nat.cast_pow]
    exact tendsto_natCast_atTop_atTop.comp hnat
  have h2 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    (hpow 2 (by norm_num)).inv_tendsto_atTop
  have h7 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 7)⁻¹) atTop (𝓝 0) :=
    (hpow 7 (by norm_num)).inv_tendsto_atTop
  have hfinal : Tendsto (fun n : ℕ => 32 * ((m : ℝ)⁻¹) ^ 2 *
      (populationResponseBound * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
        + (((n + 1 : ℕ) : ℝ) ^ 7)⁻¹)) atTop (𝓝 0) := by
    have := ((h2.const_mul populationResponseBound).add h7).const_mul (32 * ((m : ℝ)⁻¹) ^ 2)
    simpa using this
  refine hfinal.congr (fun n => ?_)
  have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [cmdsEntrywiseRate, responseFrobRate, responseDistBound, safeResponseTolerance]
  field_simp
  ring

/-- The polar-factor side expression vanishes under the safe tolerance.

This proof should consume `safe_scaled_cmdsEntrywiseRate_zero`, square the
scaled rate, multiply by the remaining linear batch factor, and use `hκ` to
show division by the fixed positive spectral floor is harmless.

Implementation recipe (execute in this order):
1. Define `s n := ((n+1 : Nat) : Real) * cmdsEntrywiseRate ...`; obtain
   `hs : Tendsto s atTop (𝓝 0)` from
   `safe_scaled_cmdsEntrywiseRate_zero`.
2. Prove the stronger weighted limit
   `((n+1 : Real) * (s n)^2) → 0` by unfolding the safe rate once and comparing
   powers; `hs` alone is not sufficient without a rate.
3. Multiply by fixed constants `d`, `4`, and `((κ/2)^2)⁻¹`; prove the denominator
   nonzero from `hκ`.
4. Normalize the target expression to that product with `field_simp` and `ring`.
5. Conclude by `Tendsto.const_mul`; keep this separate from `configBound` so any
   exponent correction is localized here.
-/
theorem safe_polar_expression_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound κ : Real) (hκ : 0 < κ) :
    Tendsto (fun n =>
      (d : Real) *
        (4 * ((n + 1 : Nat) : Real) *
          ((((n + 1 : Nat) : Real) *
            cmdsEntrywiseRate (n + 1) m
              (responseDistBound m
                (populationResponseBound + safeResponseTolerance n))
              (safeResponseTolerance n)) ^ 2) / (κ / 2) ^ 2))
      atTop (𝓝 0) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hκ2 : (κ / 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hpow : ∀ k : ℕ, 1 ≤ k → Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ k) atTop atTop := by
    intro k hk
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ k) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by omega))) tendsto_id
    simp_rw [← Nat.cast_pow]
    exact tendsto_natCast_atTop_atTop.comp hnat
  have h3 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) atTop (𝓝 0) :=
    (hpow 3 (by norm_num)).inv_tendsto_atTop
  have h8 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹) atTop (𝓝 0) :=
    (hpow 8 (by norm_num)).inv_tendsto_atTop
  have h13 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 13)⁻¹) atTop (𝓝 0) :=
    (hpow 13 (by norm_num)).inv_tendsto_atTop
  have hsum : Tendsto (fun n : ℕ =>
      populationResponseBound ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹
      + 2 * populationResponseBound * (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹
      + (((n + 1 : ℕ) : ℝ) ^ 13)⁻¹) atTop (𝓝 0) := by
    have := ((h3.const_mul (populationResponseBound ^ 2)).add
      (h8.const_mul (2 * populationResponseBound))).add h13
    simpa only [mul_zero, add_zero, zero_add] using this
  have hfinal : Tendsto (fun n : ℕ =>
      ((d : ℝ) * 4096 * ((m : ℝ)⁻¹) ^ 4 / (κ / 2) ^ 2) *
      (populationResponseBound ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹
        + 2 * populationResponseBound * (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹
        + (((n + 1 : ℕ) : ℝ) ^ 13)⁻¹)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      hsum.const_mul ((d : ℝ) * 4096 * ((m : ℝ)⁻¹) ^ 4 / (κ / 2) ^ 2)
  refine hfinal.congr (fun n => ?_)
  have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [cmdsEntrywiseRate, responseFrobRate, responseDistBound, safeResponseTolerance]
  field_simp
  ring

/-- The complete deterministic configuration envelope vanishes under the safe
schedule and linear population spectral ceiling.

Treat the summands in `configBound` separately.  Use the preceding scaled-rate
limit, the ceiling `4(n+1)B²`, and positivity of `κ/2`.  Loose domination is
preferred; this theorem exists so the final constructor does not contain a
single monolithic asymptotic calculation.

Implementation recipe (execute in this order):
1. Inspect the exact definition of `configBound` and name its three summands
   `t1`, `t2`, and `t3` in local `let`s.
2. Use `safe_scaled_cmdsEntrywiseRate_zero` for the scaled perturbation `e n` and
   the explicit ceiling `4*(n+1)*perspectiveBound^2`.
3. For every square-root term, prove the radicand tends to zero by explicit power
   comparison under `safeResponseTolerance`; then apply continuity of `Real.sqrt`
   at zero.
4. Handle division by `κ/2` using `hκ`, and fixed factors with constant
   multiplication.
5. Combine the three limits with `Tendsto.add` and normalize back to
   `configBound` by `simpa [configBound, t1, t2, t3]`.
6. Do not appeal only to continuity in `e`; the ceiling grows with `n`, so each
   weighted product must be shown to vanish explicitly.
-/
theorem safe_configBound_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hκ : 0 < κ) :
    Tendsto (fun n =>
      configBound (n + 1) d (κ / 2)
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
  -- `1/(n+1) → 0` and a generic zero-at-zero continuous composition tool.
  have hpow : ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ k) atTop atTop := by
    intro k hk
    have hnat : Tendsto (fun n : ℕ => (n + 1) ^ k) atTop atTop :=
      tendsto_atTop_mono
        (fun n => le_trans (Nat.le_succ n) (le_self_pow (by omega) (by omega))) tendsto_id
    simp_rw [← Nat.cast_pow]
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hu : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have key : ∀ f : ℝ → ℝ, Continuous f → f 0 = 0 →
      Tendsto (fun n : ℕ => f ((((n + 1 : ℕ) : ℝ))⁻¹)) atTop (𝓝 0) := by
    intro f hf hf0
    have h := (hf.tendsto (0 : ℝ)).comp hu
    rw [hf0] at h
    exact h
  -- Building-block limits (each an explicit polynomial in `x = (n+1)⁻¹`).
  have he : Tendsto en atTop (𝓝 0) := by
    refine (key (fun x => (32 / (m : ℝ) ^ 2) *
        (populationResponseBound * x ^ 2 + x ^ 7)) (by fun_prop) (by simp)).congr ?_
    intro n
    simp only [hen, cmdsEntrywiseRate, responseFrobRate, responseDistBound,
      safeResponseTolerance]
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hP : Tendsto (fun n : ℕ =>
      4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2) atTop (𝓝 0) := by
    refine (key (fun x => (16 * (32 / (m : ℝ) ^ 2) ^ 2 / κ ^ 2) *
        (populationResponseBound ^ 2 * x ^ 3 + 2 * populationResponseBound * x ^ 8 + x ^ 13))
      (by fun_prop) (by simp)).congr ?_
    intro n
    simp only [hen, cmdsEntrywiseRate, responseFrobRate, responseDistBound,
      safeResponseTolerance]
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hPN : Tendsto (fun n : ℕ =>
      (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2) * ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    refine (key (fun x => (16 * (32 / (m : ℝ) ^ 2) ^ 2 / κ ^ 2) *
        (populationResponseBound ^ 2 * x ^ 2 + 2 * populationResponseBound * x ^ 7 + x ^ 12))
      (by fun_prop) (by simp)).congr ?_
    intro n
    simp only [hen, cmdsEntrywiseRate, responseFrobRate, responseDistBound,
      safeResponseTolerance]
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hNen : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * en n) atTop (𝓝 0) := by
    refine (key (fun x => (32 / (m : ℝ) ^ 2) *
        (populationResponseBound * x + x ^ 6)) (by fun_prop) (by simp)).congr ?_
    intro n
    simp only [hen, cmdsEntrywiseRate, responseFrobRate, responseDistBound,
      safeResponseTolerance]
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hN2P : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ 2 * (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))
      atTop (𝓝 0) := by
    refine (key (fun x => (16 * (32 / (m : ℝ) ^ 2) ^ 2 / κ ^ 2) *
        (populationResponseBound ^ 2 * x + 2 * populationResponseBound * x ^ 6 + x ^ 11))
      (by fun_prop) (by simp)).congr ?_
    intro n
    simp only [hen, cmdsEntrywiseRate, responseFrobRate, responseDistBound,
      safeResponseTolerance]
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  -- The three square-root summands of `configBound`, each scaled by `√(n+1)`.
  have hsq1 : Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ) *
      ((2 * ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) ^ 2 *
        ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2 + en n)))))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        ((2 * ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) ^ 2 *
          ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2 + en n))))
        atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ =>
          16 * (d : ℝ) ^ 3 * perspectiveBound ^ 2 *
            ((4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2 * ((n + 1 : ℕ) : ℝ)) *
              (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2 * ((n + 1 : ℕ) : ℝ)))
          + 4 * (d : ℝ) ^ 3 *
            ((4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2) *
              (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2 * ((n + 1 : ℕ) : ℝ)) *
              en n)) atTop (𝓝 0) := by
        simpa using
          (((hPN.mul hPN).const_mul (16 * (d : ℝ) ^ 3 * perspectiveBound ^ 2)).add
            (((hP.mul hPN).mul he).const_mul (4 * (d : ℝ) ^ 3)))
      refine hbase.congr (fun n => ?_)
      field_simp
      ring
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  have hsq2 : Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ) *
      ((d : ℝ) ^ 2 * (en n / Real.sqrt ((κ / 2) / 2)) ^ 2))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        ((d : ℝ) ^ 2 * (en n / Real.sqrt ((κ / 2) / 2)) ^ 2)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ =>
          (d : ℝ) ^ 2 / ((κ / 2) / 2) * (en n * (((n + 1 : ℕ) : ℝ) * en n)))
          atTop (𝓝 0) := by
        simpa using (he.mul hNen).const_mul ((d : ℝ) ^ 2 / ((κ / 2) / 2))
      refine hbase.congr (fun n => ?_)
      have hc : Real.sqrt ((κ / 2) / 2) ^ 2 = (κ / 2) / 2 := Real.sq_sqrt (by positivity)
      rw [div_pow, hc]
      field_simp
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  have hsq3 : Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ) *
      ((4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2) *
        (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2)))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        ((4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2) *
          (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ =>
          4 * perspectiveBound ^ 2 *
            (((n + 1 : ℕ) : ℝ) ^ 2 * (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2)))
          atTop (𝓝 0) := by
        simpa using hN2P.const_mul (4 * perspectiveBound ^ 2)
      refine hbase.congr (fun n => ?_)
      ring
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  -- Rewrite `configBound` as those three summands via `√a·√b = √(a·b)`.
  have hfun : (fun n : ℕ => configBound (n + 1) d (κ / 2)
      (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2) (en n))
      = fun n : ℕ =>
        Real.sqrt (((n + 1 : ℕ) : ℝ) *
          ((2 * ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) ^ 2 *
            ((d : ℝ) * (4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2 + en n))))
        + Real.sqrt (((n + 1 : ℕ) : ℝ) *
            ((d : ℝ) ^ 2 * (en n / Real.sqrt ((κ / 2) / 2)) ^ 2))
        + Real.sqrt (((n + 1 : ℕ) : ℝ) *
            ((4 * ((n + 1 : ℕ) : ℝ) * perspectiveBound ^ 2) *
              (4 * ((n + 1 : ℕ) : ℝ) * (en n) ^ 2 / (κ / 2) ^ 2))) := by
    funext n
    simp only [configBound]
    rw [mul_add, mul_add,
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)),
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)),
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
  rw [hfun]
  simpa using (hsq1.add hsq2).add hsq3

/-- The conservative tolerance and linear spectral ceiling satisfy every field
of `GrowingConfigControl` for the current proved CMDS perturbation bound.

Completing this theorem removes `Hrate`, entrywise nonnegativity, the local
smallness inequality, the polar inequality, and the vanishing configuration
bound from the final public theorem.  This is intentionally a safe-rate result;
a later sharp Davis--Kahan theorem may improve the exponent without changing
the Perfect Quench interface.

Proof plan:
1. unfold `cmdsEntrywiseRate`, `responseFrobRate`, `responseDistBound`, and the
   safe tolerance;
2. prove the scaled entry rate is `O((n+1)⁻²)`;
3. prove the polar term is `O((n+1)⁻³)`;
4. bound each of the three square-root summands in `configBound` separately
   using the linear ceiling;
5. invoke `GrowingConfigControl.of_tendsto`.
Mark any future replacement by sharper spectral theory here, but retain the
proved bespoke finite theorem until the replacement removes a public premise.

Implementation recipe (execute in this order):
1. Set `entryRate n` to the displayed `cmdsEntrywiseRate` and `ceiling n` to the
   displayed linear ceiling.
2. Prove `entry_nonneg` by unfolding the response/CMDS rates and using
   `hresponse`, `safeResponseTolerance_pos`, `hm`, and positivity.
3. Supply `hscaled` with `safe_scaled_cmdsEntrywiseRate_zero`.
4. Supply `hpolar` with `safe_polar_expression_zero`.
5. Supply `hbound` with `safe_configBound_zero`.
6. Apply `GrowingConfigControl.of_tendsto` with `α := κ/2`; discharge positivity
   from `hκ`.
7. Use named arguments so `count := fun n => n+1` and the exact ceiling/entry
   functions are not inferred incorrectly.
8. No new asymptotic algebra belongs in this theorem; all failures should be
   repaired in the three preceding limit lemmas.
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
  GrowingConfigControl.of_tendsto (by positivity)
    (fun n => by
      simp only [cmdsEntrywiseRate, responseFrobRate, responseDistBound, safeResponseTolerance]
      positivity)
    (safe_scaled_cmdsEntrywiseRate_zero m hm populationResponseBound)
    (safe_polar_expression_zero m d hm populationResponseBound κ hκ)
    (safe_configBound_zero m d hm populationResponseBound perspectiveBound κ hκ)

end DkpsQuench.Perfect
