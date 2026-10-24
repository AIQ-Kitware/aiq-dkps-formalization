/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Spectral formulas for finite Schatten costs

An orthonormal eigenbasis computes the Schatten norm of a normal operator by
the absolute values of its eigenvalues. Sorting is confined to one use of the
accepted diagonal singular-value formula; the spectral sum is then invariant
under that sorting permutation.

This connects the normal spectral-trace first variation to the accepted
Schatten seminorm. It does not define a second Schatten norm. The formula and
its variational consequences are classical foundations for constrained unitary
optimization, not novelty claims.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A normal operator's Schatten norm is the power sum of the norms of its
eigenvalues. The orthonormal eigenbasis is supplied explicitly, so the result
also applies to real operators admitting such a basis and to dimension zero. -/
theorem schatten_eq_sum_norm_eigenvalues {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E)
    (mu : Fin n → 𝕜) (hA : ∀ i, A (b i) = mu i • b i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 E E p A =
      (∑ i, ‖mu i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  classical
  have hE : Module.finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hdiag : A = Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal mu) := by
    apply b.toBasis.ext
    intro i
    simpa [Matrix.toLin_self, Matrix.diagonal_apply] using hA i
  let pi := Tuple.sortDesc (fun i => ‖mu i‖)
  have hpi : Antitone (fun i => ‖mu (pi i)‖) := by
    simpa only [pi, Function.comp_def] using Tuple.antitone_sortDesc (fun i => ‖mu i‖)
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp]
  congr 1
  rw [← A.sum_fin_singularValues (fun s : ℝ => s ^ p.toReal)
    (Real.zero_rpow hp0.ne'), hE]
  calc
    _ = ∑ i, ‖mu (pi i)‖ ^ p.toReal := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdiag, Matrix.singularValues_toLin_diagonal b mu pi hpi i]
    _ = _ := Equiv.sum_comp pi (fun i => ‖mu i‖ ^ p.toReal)

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

/-- The displacement Schatten power is exactly its real normal spectral
trace. This identifies the accepted norm, rather than a surrogate spectral
objective, with the expression used by the first-variation theorem. -/
theorem schatten_displacement_rpow_eq_re_trace_cfc
    (T : H →L[ℂ] H) [IsStarNormal T]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten ℂ H H p
        (LinearMap.id - T.toLinearMap) ^ p.toReal =
      (LinearMap.trace ℂ H
        (cfc (fun z => ((‖z - 1‖ ^ p.toReal : ℝ) : ℂ)) T).toLinearMap).re := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap T
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal T.toLinearMap
      (ι := Fin (Module.finrank ℂ H)) (by simp)
  have hA (i : Fin (Module.finrank ℂ H)) :
      ((LinearMap.id : H →ₗ[ℂ] H) - T.toLinearMap) (b i) = (1 - mu i) • b i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  rw [schatten_eq_sum_norm_eigenvalues b _ _ hA p hp,
    ContinuousLinearMap.re_trace_cfc_eq_sum (fun z => ‖z - 1‖ ^ p.toReal) T b mu hmu,
    ← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [one_div_mul_cancel hp0.ne', Real.rpow_one]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sub_rev]

/-- **First variation of the actual Schatten displacement power.** The
exponent is finite and greater than one. A common compact spectral set is
enough for a normal curve; unitary curves use the unit circle. No spectral
simplicity or invertibility of the displacement is assumed. -/
theorem hasDerivAt_schatten_displacement_rpow
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (s : Set ℂ) (hs : IsCompact s)
    (a : ℝ → H →L[ℂ] H) (x : ℝ) (a' : H →L[ℂ] H)
    (ha : HasDerivAt a a' x) (hnormal : ∀ t, IsStarNormal (a t))
    (hspectrum : ∀ t, spectrum ℂ (a t) ⊆ s) :
    HasDerivAt
      (fun t => UnitarilyInvariantSeminorm.schatten ℂ H H p
        (LinearMap.id - (a t).toLinearMap) ^ p.toReal)
      (LinearMap.trace ℂ H
        ((cfc (fun z => ((p.toReal * ‖z - 1‖ ^ (p.toReal - 2) : ℝ) : ℂ) * (z - 1))
          (a x)).adjoint * a').toLinearMap).re x := by
  have h := ContinuousLinearMap.hasDerivAt_re_trace_cfc_norm_sub_one_rpow
    p.toReal hp1 s hs a x a' ha hnormal hspectrum
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  let := hnormal t
  exact schatten_displacement_rpow_eq_re_trace_cfc (a t) p hp

end Complex

end TauCeti
