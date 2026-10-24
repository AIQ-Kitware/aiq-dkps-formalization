/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
public import TauCeti.Analysis.InnerProductSpace.Trace.Free
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Unitary first variations of Schatten displacement

The self-adjoint unitary gradient is the normal functional calculus of the
phase derivative of `|1 - z| ^ p`. Its trace pairing with a Hermitian direction
is the derivative under right multiplication by `exp (i t H)`.

The analytic input is the supported normal spectral-trace theorem. The curve
has spectrum on the unit circle for every real time, so the compact spectral
set is automatic. These are classical variational ingredients, developed here
to support the exact constrained Schatten optimization problem.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The scalar phase derivative, expressed without a choice of argument.
Its formula remains defined at `z = 1`, with value zero. -/
def schattenPhaseDerivative (p : ℝ) (z : ℂ) : ℝ :=
  (conj (((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) * (Complex.I * z)).re

theorem schattenPhaseDerivative_def (p : ℝ) (z : ℂ) :
    schattenPhaseDerivative p z =
      (conj (((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) * (Complex.I * z)).re := by rfl

/-- The phase symbol is the radial norm-power coefficient times the
imaginary coordinate. In particular its sign on the unit circle follows
the sign of the principal phase. -/
theorem schattenPhaseDerivative_eq (p : ℝ) (z : ℂ) :
    schattenPhaseDerivative p z = p * ‖z - 1‖ ^ (p - 2) * z.im := by
  rw [schattenPhaseDerivative_def]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  ring

/-- The self-adjoint gradient for variations within the unitary group. -/
def schattenUnitaryGradient (p : ℝ) (U : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc (fun z => (schattenPhaseDerivative p z : ℂ)) U

theorem schattenUnitaryGradient_def (p : ℝ) (U : E →L[ℂ] E) :
    schattenUnitaryGradient p U = cfc (fun z => (schattenPhaseDerivative p z : ℂ)) U := by rfl

/-- The unitary gradient is self-adjoint because its spectral symbol is real. -/
theorem isSelfAdjoint_schattenUnitaryGradient (p : ℝ) (U : E →L[ℂ] E) :
    IsSelfAdjoint (schattenUnitaryGradient p U) := by
  rw [schattenUnitaryGradient_def]
  change star (cfc (fun z => (schattenPhaseDerivative p z : ℂ)) U) = _
  rw [← cfc_star]
  congr 1
  ext z
  exact Complex.conj_ofReal _

/-- The unitary gradient commutes with the underlying normal operator. -/
theorem commute_schattenUnitaryGradient (p : ℝ) (U : E →L[ℂ] E) [IsStarNormal U] :
    Commute (schattenUnitaryGradient p U) U := by
  rw [schattenUnitaryGradient_def]
  exact (Commute.refl U).cfc (star_comm_self : Commute (star U) U) _

variable [FiniteDimensional ℂ E]

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
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

/-- The phase-gradient trace pairing is the real trace coefficient of the
ambient displacement gradient on a unitary tangent. Normality suffices for
this identity; self-adjointness of the direction makes its diagonal real. -/
theorem re_trace_schattenUnitaryGradient_mul
    (p : ℝ) (U : E →L[ℂ] E) [IsStarNormal U]
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    (LinearMap.trace ℂ E (schattenUnitaryGradient p U * H).toLinearMap).re =
      (LinearMap.trace ℂ E
        ((cfc (fun z => ((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) U).adjoint *
          (U * (Complex.I • H))).toLinearMap).re := by
  let g : ℂ → ℂ := fun z => ((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)
  let A : E →L[ℂ] E := cfc g U
  let := ContinuousLinearMap.isStarNormal_toLinearMap U
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal U.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hU (i) : U (b i) = mu i • b i := hmu i
  have hG (i) : schattenUnitaryGradient p U (b i) =
      (schattenPhaseDerivative p (mu i) : ℂ) • b i := by
    rw [schattenUnitaryGradient_def]
    exact ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hU i)
  have hA (i) : A.adjoint (b i) = conj (g (mu i)) • b i := by
    change (cfc g U).adjoint (b i) = _
    rw [← _root_.ContinuousLinearMap.star_eq_adjoint, ← cfc_star]
    exact ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hU i)
  have hfactor : A.adjoint * (U * (Complex.I • H)) =
      (Complex.I • (A.adjoint * U)) * H := by
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  have hB (i) : (Complex.I • (A.adjoint * U)) (b i) =
      (Complex.I * (mu i * conj (g (mu i)))) • b i := by
    simp only [smul_apply, mul_apply_eq_comp, hU, map_smul, hA,
      smul_smul]
  change _ = (LinearMap.trace ℂ E (A.adjoint * (U * (Complex.I • H))).toLinearMap).re
  rw [hfactor, re_trace_mul_of_eigenbasis b _ H _ hG,
    re_trace_mul_of_eigenbasis b _ H _ hB]
  apply Finset.sum_congr rfl
  intro i _
  have hHi : (inner ℂ (b i) (H (b i))).im = 0 :=
    (_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH).im_inner_self_apply _
  have hphase : schattenPhaseDerivative p (mu i) =
      (Complex.I * (mu i * conj (g (mu i)))).re := by
    rw [schattenPhaseDerivative_def]
    congr 1
    change conj (g (mu i)) * (Complex.I * mu i) = _
    ring
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hHi, mul_zero,
    sub_zero, hphase]

/-- Right multiplication by the exponential of a skew-adjoint direction
is a differentiable unitary curve. The formula uses the actual Schatten
displacement power, and permits a zero displacement singular value. -/
theorem hasDerivAt_schatten_displacement_rpow_mul_exp
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    HasDerivAt
      (fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal)
      (LinearMap.trace ℂ E
        ((cfc (fun z => ((p.toReal * ‖z - 1‖ ^ (p.toReal - 2) : ℝ) : ℂ) * (z - 1))
          (U : E →L[ℂ] E)).adjoint * ((U : E →L[ℂ] E) * (Complex.I • H))).toLinearMap).re 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let a : ℝ → E →L[ℂ] E := fun t =>
    (U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))
  have hunit (t : ℝ) : a t ∈ unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have ha : HasDerivAt a ((U : E →L[ℂ] E) * (Complex.I • H)) 0 := by
    have h := (hasDerivAt_exp_smul_const
      (𝕂 := ℝ) (Complex.I • H) (0 : ℝ)).const_mul (U : E →L[ℂ] E)
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using h
  have hd := hasDerivAt_schatten_displacement_rpow p hp hp1 (Metric.sphere (0 : ℂ) 1)
    (isCompact_sphere 0 1) a 0 ((U : E →L[ℂ] E) * (Complex.I • H)) ha
    (fun t => isStarNormal_of_mem_unitary (hunit t))
    (fun t => spectrum.subset_circle_of_unitary (hunit t))
  simpa only [a, zero_smul, NormedSpace.exp_zero, mul_one] using hd

/-- The self-adjoint unitary gradient pairs with a Hermitian right
direction to give the first variation of Schatten displacement. -/
theorem hasDerivAt_schatten_unitary_right_variation
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    HasDerivAt
      (fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal)
      (LinearMap.trace ℂ E
        (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E) * H).toLinearMap).re 0 :=
  (hasDerivAt_schatten_displacement_rpow_mul_exp p hp hp1 U H hH).congr_deriv
    (re_trace_schattenUnitaryGradient_mul p.toReal (U : E →L[ℂ] E) H hH).symm

/-- At a local minimum along a Hermitian unitary variation, its gradient
trace pairing vanishes. Feasibility of a particular constrained variation is
a separate geometric input to this calculus theorem. -/
theorem re_trace_schattenUnitaryGradient_mul_eq_zero_of_isLocalMin
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hmin : IsLocalMin (fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - ((U : E →L[ℂ] E) *
        NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal) 0) :
    (LinearMap.trace ℂ E
      (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E) * H).toLinearMap).re = 0 :=
  hmin.hasDerivAt_eq_zero (hasDerivAt_schatten_unitary_right_variation p hp hp1 U H hH)

end TauCeti
