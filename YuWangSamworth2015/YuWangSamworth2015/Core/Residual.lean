/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Paper-facing Yu--Wang--Samworth declarations remain here with their original
statement forms. Their finite-dimensional population-gap proofs now forward to
Tau Ceti; this module retains only the arbitrary ordered-eigenframe extensions
that are not in the upstream API.
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth
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

/-! ### The residual bounds for an arbitrary ordered eigenframe

The declarations above fix the perturbed block to be `S`'s *chosen* eigenbasis at
the indices `s`.  Yu, Wang and Samworth do not: their `V̂ = (v̂_r,…,v̂_s)` is any
orthonormal family with `Σ̂ v̂ⱼ = λ̂ⱼ v̂ⱼ`, and they deliberately assume no gap in
`λ̂`, so at a repeated sample eigenvalue the family is genuinely not determined.
`LinearMap.IsSymmetric.IsOrderedEigenframe` is that hypothesis, and the estimates below are the
upper half of the residual sandwich for it.

The ordering is used *only* on the eigenvalues: Weyl and Hoffman--Wielandt
compare `λⱼ(S)` with `λⱼ(T)` at the same index.  Nothing in either proof looks at
which eigenvector was chosen, which is exactly why the source theorem quantifies
over the choice. -/

section Frame

variable {d : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- **Orthonormal compression cannot increase the Frobenius norm.**
`∑ᵢ ‖M wᵢ‖² ≤ ∑ₖ ‖M bₖ‖²` for a symmetric `M`, an orthonormal *family* `w` and an
orthonormal *basis* `b`: expand each `M wᵢ` in `b`, move `M` across the inner
product by symmetry, and apply Bessel in `w`.

This is the appendix lemma of Yu--Wang--Samworth (`‖UᵀMW‖_F ≤ ‖M‖_F` for `U`, `W`
with orthonormal columns) in the half the main proof consumes, stated
basis-free. -/
theorem sum_sq_norm_apply_orthonormal_le (hM : (S - T).IsSymmetric)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {w : Fin d → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, ‖(S - T) (w i)‖ ^ 2 ≤ ∑ k, ‖(S - T) (b k)‖ ^ 2 := by
  calc ∑ i, ‖(S - T) (w i)‖ ^ 2
      = ∑ i, ∑ k, ‖⟪b k, (S - T) (w i)⟫_𝕜‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => (b.sum_sq_norm_inner_right _).symm
    _ = ∑ k, ∑ i, ‖⟪w i, (S - T) (b k)⟫_𝕜‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← hM (b k) (w i), norm_inner_symm]
    _ ≤ ∑ k, ‖(S - T) (b k)‖ ^ 2 :=
        Finset.sum_le_sum fun k _ =>
          _root_.Orthonormal.sum_inner_products_le ((S - T) (b k)) hw

/-- **A sum over an index embedding is at most the full sum**, for nonnegative
terms.  The step that lets Weyl and Hoffman--Wielandt be applied only at the
selected indices. -/
private theorem sum_comp_embedding_le (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j)
    (e : Fin d ↪ Fin n) : ∑ i, g (e i) ≤ ∑ j, g j := by
  classical
  rw [← Finset.sum_map Finset.univ e g]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hg j

/-- **The frame residual as a perturbation column.**
`λ_{e i}(T) wᵢ − T wᵢ = (S − T) wᵢ − (λ_{e i}(S) − λ_{e i}(T)) wᵢ`, using only the
eigenvalue equation of the frame. -/
theorem frameResidual_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : Fin d ↪ Fin n} {w : Fin d → E}
    (hw : IsOrderedEigenframe hS hn e w) (i : Fin d) :
    (hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)
      = (S - T) (w i)
        - ((hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i) : ℝ) : 𝕜) • w i := by
  rw [LinearMap.sub_apply, (isOrderedEigenframe_iff.mp hw).apply_eq i]
  push_cast
  module

/-- **Frame residual, Frobenius branch.**  `∑ᵢ ‖Rᵢ‖² ≤ 4 ‖S − T‖²_F` for an
arbitrary ordered eigenframe `w` of `S`: the perturbation columns are bounded by
orthonormal compression and the eigenvalue displacement by Hoffman--Wielandt,
each by `‖S − T‖²_F`. -/
theorem sum_sq_norm_frameResidual_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : Fin d ↪ Fin n} {w : Fin d → E}
    (hw : IsOrderedEigenframe hS hn e w) :
    ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  have hST : (S - T).IsSymmetric := hS.sub hT
  -- The two halves, each bounded by the Frobenius norm.
  have hcols : ∑ i, ‖(S - T) (w i)‖ ^ 2 ≤ frob :=
    sum_sq_norm_apply_orthonormal_le hST (hT.eigenvectorBasis hn)
      (isOrderedEigenframe_iff.mp hw).orthonormal
  have hHW : ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 ≤ frob := by
    refine (sum_comp_embedding_le
      (fun j => (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
      (fun j => sq_nonneg _) e).trans ?_
    rw [show (∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
        = ∑ j, (hT.eigenvalues hn j - hS.eigenvalues hn j) ^ 2 from
        Finset.sum_congr rfl fun j _ => by ring]
    rw [hfrob]
    have hbase :=
      hT.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply hS hn (hT.eigenvectorBasis hn)
    exact hbase.trans_eq (Finset.sum_congr rfl fun k _ => by
      change ‖T (hT.eigenvectorBasis hn k) - S (hT.eigenvectorBasis hn k)‖ ^ 2 = _
      exact congrArg (fun r : ℝ => r ^ 2) (norm_sub_rev _ _))
  -- Per-column triangle inequality.
  have hcol : ∀ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ 2 * ‖(S - T) (w i)‖ ^ 2
        + 2 * (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 := by
    intro i
    have htri : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖
        ≤ ‖(S - T) (w i)‖ + |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)| := by
      rw [frameResidual_eq hT hS hn hw i]
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_smul, RCLike.norm_ofReal,
        (isOrderedEigenframe_iff.mp hw).orthonormal.norm_eq_one i, mul_one]
    have h1 : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
        ≤ (‖(S - T) (w i)‖
            + |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [h1, sq_nonneg (‖(S - T) (w i)‖
      - |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)|),
      sq_abs (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i))]
  calc ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ ∑ i, (2 * ‖(S - T) (w i)‖ ^ 2
          + 2 * (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2) :=
        Finset.sum_le_sum fun i _ => hcol i
    _ = 2 * ∑ i, ‖(S - T) (w i)‖ ^ 2
          + 2 * ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * frob := by linarith

/-- **Frame residual, operator-norm branch.**  `∑ᵢ ‖Rᵢ‖² ≤ 4 d ε²` when `S − T`
is `ε`-operator-close: each column splits as `‖(S − T) wᵢ‖ ≤ ε` and, by Weyl at
the *index* `e i`, `|λ_{e i}(S) − λ_{e i}(T)| ≤ ε`. -/
theorem sum_sq_norm_frameResidual_le_of_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : Fin d ↪ Fin n} {w : Fin d → E}
    (hw : IsOrderedEigenframe hS hn e w) {ε : ℝ}
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ 4 * d * ε ^ 2 := by
  have hcol : ∀ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ 4 * ε ^ 2 := by
    intro i
    have hEwi : ‖(S - T) (w i)‖ ≤ ε := by
      have := hε (w i)
      rwa [(isOrderedEigenframe_iff.mp hw).orthonormal.norm_eq_one i, mul_one] at this
    have hδ : |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)| ≤ ε :=
      LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le hS hT hn hε (e i)
    have htri : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ≤ 2 * ε := by
      rw [frameResidual_eq hT hS hn hw i]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal,
        (isOrderedEigenframe_iff.mp hw).orthonormal.norm_eq_one i, mul_one]
      linarith
    calc ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ (2 * ε) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ = 4 * ε ^ 2 := by ring
  calc ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ ∑ _i : Fin d, 4 * ε ^ 2 := Finset.sum_le_sum fun i _ => hcol i
    _ = 4 * d * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Frame

end YuWangSamworth2015
