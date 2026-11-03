/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Paper-facing Yu--Wang--Samworth declarations remain here with their original
statement forms. Their finite-dimensional population-gap proofs now forward to
Tau Ceti. The arbitrary ordered-eigenframe residual foundations also landed
in #26824 and are consumed directly, with no local compatibility declarations.
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.Basic
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.FrameResidual
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.ResidualGap

/-! # The Yu–Wang–Samworth Davis–Kahan variant (Frobenius, population gap)

For symmetric `T, S` on a finite-dimensional inner product space, fix an index
block `s` (the target eigenvectors).  Write `u` for `T`'s eigenbasis and `w` for
`S`'s.  The **sin-Θ overlap** between the `S`-block subspace `span (w j : j ∈ s)`
and the `T`-block subspace `span (u k : k ∈ s)` is

`overlap = ∑_{j ∈ s} ∑_{k ∉ s} ‖⟪u k, w j⟫‖²`.

Yu, Wang and Samworth bound this using only a **population eigengap**
`Δ ≤ |λⱼ(T) − λₖ(T)|` for `j ∈ s`, `k ∉ s` — a separation of `T`'s own spectrum,
with no mixed `T`/`S` term — at the cost of the constant `2`:

`Δ² · overlap ≤ 4 · ‖S − T‖²_F`,  i.e.  `‖sinΘ‖_F ≤ 2 ‖S − T‖_F / Δ`.

The proof is the residual sandwich around `Rⱼ = λⱼ(T) wⱼ − T wⱼ`:

* **Lower bound** (`Δ² overlap ≤ ∑_{j ∈ s} ‖Rⱼ‖²`): the cross-term identity
  `⟪uₖ, Rⱼ⟫ = (λⱼ(T) − λₖ(T)) ⟪uₖ, wⱼ⟫` uses *only* `T`-eigenvalues on both
  sides, so the population gap applies directly; Bessel's inequality then sums
  the complement block into `‖Rⱼ‖²`.
* **Upper bound** (`∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 ‖S − T‖²_F`): from
  `Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ` and `(a + b)² ≤ 2a² + 2b²`, the two
  pieces are the Frobenius norm of `S − T` and — via **Hoffman–Wielandt** — the
  eigenvalue displacement, each `≤ ‖S − T‖²_F`.

## Main results

* `YuWangSamworth2015.sq_gap_mul_sum_cross_le_of_population_gap`: the squared bound
  `Δ² · overlap ≤ 4 · ∑ₖ ‖(S − T) uₖ‖²`.
* `YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap`: the `‖sinΘ‖_F` form
  `√overlap ≤ 2 · √(∑ₖ ‖(S − T) uₖ‖²) / Δ`.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), 315–323.  arXiv:1405.0680.

## Provenance

The residual argument was previously staged under
`ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Residual.lean`.  On
2026-08-17 it moved into `YuWangSamworth2015.Core` because the population-only
gap sandwich is paper-specific application theory rather than foundation API.
Its reusable inputs remain in `ForTauCeti`; the move changes package ownership
and namespace, not the mathematical statement.

-/

public section

namespace YuWangSamworth2015
open TauCeti
open LinearMap.IsSymmetric (IsOrderedEigenframe isOrderedEigenframe_iff)
open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- **Yu–Wang–Samworth sin-Θ bound (Frobenius, population gap), squared form.**
With a population gap `Δ ≤ |λⱼ(T) − λₖ(T)|` separating the block `s` from its
complement, the sin-Θ overlap obeys `Δ² · overlap ≤ 4 · ‖S − T‖²_F`. -/
theorem sq_gap_mul_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  have h := hT.sq_mul_sum_sum_norm_inner_sq_le_four_mul_frobenius_sq
    hS hn hΔ hgap
  rw [← TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply
    (hT.eigenvectorBasis hn) (S - T)]
  exact h

/-- **Yu–Wang–Samworth sin-Θ bound (operator-norm branch, population gap).** With
`S − T` `ε`-operator-close, `Δ² · overlap ≤ 4 · d · ε²` where `d = |s|` is the
block size — the `√d ε` branch of Yu–Wang–Samworth. -/
theorem sq_gap_mul_sum_cross_le_of_population_gap_opNorm
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ ε : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|)
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ε ^ 2 :=
  hT.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq hS hn hΔ hgap hε

/-- **Yu–Wang–Samworth sin-Θ bound (Frobenius, population gap), `‖sinΘ‖_F` form.**
For a positive population gap `Δ`, `√overlap ≤ 2 · √(∑ₖ ‖(S − T) uₖ‖²) / Δ`, the
statistician's `‖sinΘ‖_F ≤ 2 ‖S − T‖_F / Δ`. -/
theorem sqrt_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
      ≤ 2 * Real.sqrt (∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2) / Δ := by
  set overlap := ∑ j ∈ s, ∑ k ∈ sᶜ,
    ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 with hov
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  have hkey := sq_gap_mul_sum_cross_le_of_population_gap hT hS hn s hΔ.le hgap
  rw [← hov, ← hfrob] at hkey
  have hov0 : 0 ≤ overlap := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hfr0 : 0 ≤ frob := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [le_div_iff₀ hΔ]
  -- `√overlap · Δ ≤ 2 √frob`; square both sides (both nonneg).
  have hsq : (Real.sqrt overlap * Δ) ^ 2 ≤ (2 * Real.sqrt frob) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hov0, mul_pow, Real.sq_sqrt hfr0]
    nlinarith [hkey]
  have hL : 0 ≤ Real.sqrt overlap * Δ := by positivity
  have hR : 0 ≤ 2 * Real.sqrt frob := by positivity
  nlinarith [hsq, hL, hR, sq_nonneg (Real.sqrt overlap * Δ - 2 * Real.sqrt frob)]

end YuWangSamworth2015
