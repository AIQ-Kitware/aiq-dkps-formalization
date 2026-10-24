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

/-- Finite Schatten norms are preserved by isometric changes of source
and target coordinates, including changes of the underlying carrier types. -/
theorem schatten_congr_linearIsometryEquiv
    {F G H : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    (U : F ≃ₗᵢ[𝕜] H) (V : G ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 G H p
        ((U : F →ₗ[𝕜] H) ∘ₗ A ∘ₗ (V : G →ₗ[𝕜] E)) =
      UnitarilyInvariantSeminorm.schatten 𝕜 E F p A := by
  rw [UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp,
    UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp,
    LinearMap.singularValues_linearIsometryEquiv_comp,
    LinearMap.singularValues_comp_linearIsometryEquiv]

/-- The displacement Schatten norm is independent of orthonormal
coordinates on the ambient finite-dimensional Hilbert space. -/
theorem schatten_displacement_conj_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) (A : E →L[𝕜] E)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 F F p
        (LinearMap.id - (e.conjStarAlgEquiv A).toLinearMap) =
      UnitarilyInvariantSeminorm.schatten 𝕜 E E p (LinearMap.id - A.toLinearMap) := by
  have hconj : LinearMap.id - (e.conjStarAlgEquiv A).toLinearMap =
      (e : E →ₗ[𝕜] F) ∘ₗ (LinearMap.id - A.toLinearMap) ∘ₗ
        (e.symm : F →ₗ[𝕜] E) := by
    ext x
    change x - e (A (e.symm x)) = e (e.symm x - A (e.symm x))
    rw [map_sub, e.apply_symm_apply]
  rw [hconj]
  exact schatten_congr_linearIsometryEquiv e e.symm _ p hp

/-- A spectral sum over all singular values of a normal map can be
computed from the absolute eigenvalues in any finite orthonormal eigenbasis.
The ambient-dimension sum includes zero singular values, so `f 0 = 0` is
not required. -/
theorem sum_singularValues_eq_sum_norm_eigenvalues
    {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] E)
    (mu : ι → 𝕜) (hA : ∀ i, A (b i) = mu i • b i) (f : ℝ → M) :
    (∑ i : Fin (Module.finrank 𝕜 E), f (A.singularValues i)) = ∑ i, f ‖mu i‖ := by
  classical
  let e := Fintype.equivFin ι
  let b' := b.reindex e
  let nu (i : Fin (Fintype.card ι)) := mu (e.symm i)
  have heigen (i) : A (b' i) = nu i • b' i := by
    simpa only [b', nu, OrthonormalBasis.reindex_apply] using hA (e.symm i)
  have hE : Module.finrank 𝕜 E = Fintype.card ι := Module.finrank_eq_card_basis b.toBasis
  have hdiag : A = Matrix.toLin b'.toBasis b'.toBasis (Matrix.diagonal nu) := by
    apply b'.toBasis.ext
    intro i
    simpa [Matrix.toLin_self, Matrix.diagonal_apply] using heigen i
  let pi := Tuple.sortDesc (fun i => ‖nu i‖)
  have hpi : Antitone (fun i => ‖nu (pi i)‖) := by
    simpa only [pi, Function.comp_def] using Tuple.antitone_sortDesc (fun i => ‖nu i‖)
  rw [hE]
  calc
    _ = ∑ i, f ‖nu (pi i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdiag, Matrix.singularValues_toLin_diagonal b' nu pi hpi i]
    _ = ∑ i, f ‖nu i‖ := Equiv.sum_comp pi (fun i => f ‖nu i‖)
    _ = _ := Equiv.sum_comp e.symm (fun i => f ‖mu i‖)

/-- A normal operator's Schatten norm is the power sum of the norms of its
eigenvalues. The orthonormal eigenbasis is supplied explicitly, so the result
also applies to real operators admitting such a basis and to dimension zero. -/
theorem schatten_eq_sum_norm_eigenvalues {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E)
    (mu : Fin n → 𝕜) (hA : ∀ i, A (b i) = mu i • b i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 E E p A =
      (∑ i, ‖mu i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp]
  congr 1
  rw [← A.sum_fin_singularValues (fun s : ℝ => s ^ p.toReal)
    (Real.zero_rpow hp0.ne')]
  exact sum_singularValues_eq_sum_norm_eigenvalues b A mu hA (fun s : ℝ => s ^ p.toReal)

/-- The finite Schatten power sum in an orthonormal eigenbasis indexed
by any finite type. This avoids sorting or index conventions when assembling
orthogonal spectral blocks. -/
theorem schatten_rpow_eq_sum_norm_eigenvalues
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] E)
    (mu : ι → 𝕜) (hA : ∀ i, A (b i) = mu i • b i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 E E p A ^ p.toReal =
      ∑ i, ‖mu i‖ ^ p.toReal := by
  classical
  let e := Fintype.equivFin ι
  have heigen (i : Fin (Fintype.card ι)) :
      A ((b.reindex e) i) = mu (e.symm i) • (b.reindex e) i := by
    simpa only [OrthonormalBasis.reindex_apply] using hA (e.symm i)
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [schatten_eq_sum_norm_eigenvalues (b.reindex e) A (fun i => mu (e.symm i)) heigen p hp,
    ← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)),
    one_div_mul_cancel hp0.ne', Real.rpow_one]
  exact Equiv.sum_comp e.symm (fun i => ‖mu i‖ ^ p.toReal)

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
  rw [schatten_rpow_eq_sum_norm_eigenvalues b _ _ hA p hp,
    ContinuousLinearMap.re_trace_cfc_eq_sum (fun z => ‖z - 1‖ ^ p.toReal) T b mu hmu]
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
