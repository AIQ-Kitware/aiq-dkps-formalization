/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
alongside the finite-dimensional spectral perturbation material.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.EigenFrame
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Corollaries

/-! # The spectral-gap residual lower bound

Let `T` be symmetric, `U` a `T`-invariant subspace whose spectrum is
`Δ`-separated from the spectrum on `Uᗮ`, and let `w` be *any* family of trial
vectors carrying trial values `lam i` drawn from the spectrum on `U`.  Then the
mass of `w i` outside `U` is controlled by the residual `lam i • w i - T (w i)`:

`Δ² ∑ᵢ ‖P_{Uᗮ} wᵢ‖² ≤ ∑ᵢ ‖lam i • wᵢ − T wᵢ‖²`.

This is the lower half of the Davis--Kahan/Yu--Wang--Samworth residual sandwich,
stated where it actually lives: it needs nothing about `w` beyond the residual,
in particular neither orthonormality nor any relation to a second operator.  The
proof applies TauCeti's vector residual inequality to each trial vector
and sums the squared estimates.

Because the trial values are only required to lie in `Module.End.restrictedPointSpectrum T U`,
the statement is insensitive to which eigenvectors were chosen inside a repeated
eigenspace — the point of `Module.End.IsEigenfamily`.

## Main results

* `TauCeti.exists_isEigenFamily_span_eq`: an invariant subspace of a symmetric
  operator is spanned by an orthonormal eigenfamily.
* `TauCeti.sq_gap_mul_sum_sq_norm_starProjection_orthogonal_le`: the residual
  lower bound.
-/

public section

open Module (finrank)
open scoped InnerProductSpace BigOperators

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

/-- **An invariant subspace is spanned by an orthonormal eigenfamily.**
Diagonalize the restriction `T|W` and push its eigenbasis back into `E`. -/
theorem exists_isEigenFamily_span_eq (hT : T.IsSymmetric) {W : Submodule 𝕜 E}
    (hW : (W ∈ Module.End.invtSubmodule T)) :
    ∃ (m : ℕ) (y : Fin m → E) (c : Fin m → ℝ),
      Module.End.IsEigenfamily T c y ∧ Submodule.span 𝕜 (Set.range y) = W := by
  classical
  have hsym : (T.restrict hW).IsSymmetric := hT.restrict_invariant hW
  have hm : finrank 𝕜 W = finrank 𝕜 W := rfl
  set b := hsym.eigenvectorBasis hm with hb
  have hon : Orthonormal 𝕜 fun k => ((b k : W) : E) :=
    b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  refine ⟨finrank 𝕜 W, fun k => ((b k : W) : E), fun k => hsym.eigenvalues hm k,
    ⟨hon, ?_⟩, ?_⟩
  · intro k
    have hk : (T.restrict hW) (b k) = (hsym.eigenvalues hm k : 𝕜) • b k :=
      hsym.apply_eigenvectorBasis hm k
    exact congrArg Subtype.val hk
  · refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨k, rfl⟩
      exact (b k).property
    · rw [finrank_span_eq_card hon.linearIndependent, Fintype.card_fin]

/-- **The spectral-gap residual lower bound.**

With `U` invariant, `Δ`-separated from `Uᗮ` in `T`'s spectrum, and trial values
`lam i` carried by `U`, the component of `w i` outside `U` costs at least `Δ`
per unit of residual:
`Δ² ∑ᵢ ‖P_{Uᗮ} wᵢ‖² ≤ ∑ᵢ ‖lam i • wᵢ − T wᵢ‖²`.

The vector inequality applies separately at each trial value. -/
theorem sq_gap_mul_sum_sq_norm_starProjection_orthogonal_le (hT : T.IsSymmetric)
    {U : Submodule 𝕜 E} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : Module.End.PointInternalGap T U Δ) {d : ℕ} (w : Fin d → E) (lam : Fin d → ℝ)
    (hlam : ∀ i, lam i ∈ Module.End.restrictedPointSpectrum T U) :
    Δ ^ 2 * ∑ i, ‖Uᗮ.starProjection (w i)‖ ^ 2
      ≤ ∑ i, ‖(lam i : 𝕜) • w i - T (w i)‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hspec : Module.End.PointSpectrumIn T Uᗮ (Set.Ioo (lam i - Δ) (lam i + Δ))ᶜ := by
    refine Module.End.pointSpectrumIn_iff.mpr fun y hy hy0 μ hTy => ?_
    have hdist := hgap.pointSpectraSeparated.le_abs_sub (hlam i)
      (Module.End.mem_restrictedPointSpectrum hy hy0 hTy)
    intro hμ
    exact hdist.not_gt (abs_lt.mpr ⟨by linarith [hμ.2], by linarith [hμ.1]⟩)
  have h := LinearMap.IsSymmetric.mul_norm_starProjection_orthogonal_le_norm_apply_sub_smul
    (A := T.toContinuousLinearMap) hT hgap.invariant hspec (w i)
  change Δ * ‖Uᗮ.starProjection (w i)‖ ≤ ‖T (w i) - (lam i : 𝕜) • w i‖ at h
  have hs := pow_le_pow_left₀ (mul_nonneg hΔ (norm_nonneg _)) h 2
  rw [norm_sub_rev]
  simpa only [mul_pow] using hs

end TauCeti
