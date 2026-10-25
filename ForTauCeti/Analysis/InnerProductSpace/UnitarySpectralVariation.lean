/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace
public import TauCeti.Analysis.InnerProductSpace.Trace.Free
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# First variations of supported spectral penalties on the unitary group

A continuous scalar supporting field gives the self-adjoint phase gradient
and its actual trace pairing along every Hermitian exponential variation.
No spectral simplicity or displacement invertibility is required.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The intrinsic phase gradient induced by a complex scalar supporting field. -/
@[expose] def unitaryPhaseGradient (g : ℂ → ℂ) (U : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc (fun z => ((conj (g z) * (Complex.I * z)).re : ℂ)) U

/-- Its scalar symbol is real, so the phase gradient is self-adjoint. -/
theorem isSelfAdjoint_unitaryPhaseGradient (g : ℂ → ℂ) (U : E →L[ℂ] E) :
    IsSelfAdjoint (unitaryPhaseGradient g U) := by
  change star (cfc (fun z => ((conj (g z) * (Complex.I * z)).re : ℂ)) U) = _
  rw [← cfc_star]
  congr 1
  ext z
  exact Complex.conj_ofReal _

/-- The phase gradient preserves the spectral subspaces of the operator. -/
theorem commute_unitaryPhaseGradient
    (g : ℂ → ℂ) (U : E →L[ℂ] E) [IsStarNormal U] :
    Commute (unitaryPhaseGradient g U) U :=
  (Commute.refl U).cfc (star_comm_self : Commute (star U) U) _

omit [CompleteSpace E] in
private theorem re_trace_mul_of_eigenbasis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ E) (A B : E →L[ℂ] E)
    (mu : Fin n → ℂ) (hA : ∀ i, A (b i) = mu i • b i) :
    (LinearMap.trace ℂ E (A * B).toLinearMap).re =
      ∑ i, (mu i * inner ℂ (b i) (B (b i))).re := by
  rw [_root_.ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
    LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (inner ℂ (b i) (B (A (b i)))).re = _
  rw [hA, map_smul, inner_smul_right]

variable [FiniteDimensional ℂ E]

/-- The phase gradient gives the ambient supporting functional on every
Hermitian unitary tangent. -/
theorem re_trace_unitaryPhaseGradient_mul
    (g : ℂ → ℂ) (U : E →L[ℂ] E) [IsStarNormal U]
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    (LinearMap.trace ℂ E (unitaryPhaseGradient g U * H).toLinearMap).re =
      (LinearMap.trace ℂ E
        ((cfc g U).adjoint * (U * (Complex.I • H))).toLinearMap).re := by
  let A := cfc g U
  let := ContinuousLinearMap.isStarNormal_toLinearMap U
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal U.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hU (i) : U (b i) = mu i • b i := hmu i
  have hG (i) : unitaryPhaseGradient g U (b i) =
      ((conj (g (mu i)) * (Complex.I * mu i)).re : ℂ) • b i :=
    ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hU i)
  have hA (i) : A.adjoint (b i) = conj (g (mu i)) • b i := by
    change (cfc g U).adjoint (b i) = _
    rw [← _root_.ContinuousLinearMap.star_eq_adjoint, ← cfc_star]
    exact ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hU i)
  have hfactor : A.adjoint * (U * (Complex.I • H)) =
      (Complex.I • (A.adjoint * U)) * H := by
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  have hB (i) : (Complex.I • (A.adjoint * U)) (b i) =
      (Complex.I * (mu i * conj (g (mu i)))) • b i := by
    simp only [smul_apply, mul_apply_eq_comp, hU, map_smul, hA, smul_smul]
  change _ = (LinearMap.trace ℂ E (A.adjoint * (U * (Complex.I • H))).toLinearMap).re
  rw [hfactor, re_trace_mul_of_eigenbasis b _ H _ hG,
    re_trace_mul_of_eigenbasis b _ H _ hB]
  apply Finset.sum_congr rfl
  intro i _
  have hHi : (inner ℂ (b i) (H (b i))).im = 0 :=
    (_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH).im_inner_self_apply _
  have hphase : (conj (g (mu i)) * (Complex.I * mu i)).re =
      (Complex.I * (mu i * conj (g (mu i)))).re := by congr 1; ring
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hHi, mul_zero,
    sub_zero, hphase]

/-- A supported spectral trace has its phase-gradient first variation at
every time along a Hermitian exponential curve of unitaries. -/
theorem hasDerivAt_unitary_spectral_right_variation_at
    (f : ℂ → ℝ) (g : ℂ → ℂ)
    (hg : ContinuousOn g (Metric.sphere (0 : ℂ) 1))
    (hsupport : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ∀ w ∈ Metric.sphere (0 : ℂ) 1,
      f z + (conj (g z) * (w - z)).re ≤ f w)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (LinearMap.trace ℂ E
        (cfc (fun z => (f z : ℂ)) ((U : E →L[ℂ] E) *
          NormedSpace.exp (s • (Complex.I • H)))).toLinearMap).re)
      (LinearMap.trace ℂ E
        (unitaryPhaseGradient g ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • H))) * H).toLinearMap).re t := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let a : ℝ → E →L[ℂ] E := fun s =>
    (U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H))
  have hunit (s : ℝ) : a s ∈ unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have ha : HasDerivAt a (a t * (Complex.I • H)) t := by
    simpa only [a, mul_assoc] using (hasDerivAt_exp_smul_const
      (𝕂 := ℝ) (Complex.I • H) t).const_mul (U : E →L[ℂ] E)
  have hd := ContinuousLinearMap.hasDerivAt_re_trace_cfc f g
    (Metric.sphere (0 : ℂ) 1) (isCompact_sphere 0 1) hg hsupport
    a t (a t * (Complex.I • H)) ha
    (fun s => isStarNormal_of_mem_unitary (hunit s))
    (fun s => spectrum.subset_circle_of_unitary (hunit s))
  let := isStarNormal_of_mem_unitary (hunit t)
  exact hd.congr_deriv (re_trace_unitaryPhaseGradient_mul g (a t) H hH).symm

end TauCeti
