/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.FourierSemigroup
import ForMathlib.Analysis.InnerProductSpace.SpectralOrder.Complex
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Ordered-spectrum Sylvester reconstruction

For bounded self-adjoint complex operators whose spectra are ordered by a
positive gap, the Sylvester solution is the Laplace integral

`X = integral over t >= 0 of exp(-t A) C exp(t B)`.

The proof differentiates `exp(-t A) X exp(t B)`, integrates on a finite
interval, and lets the endpoint tend to infinity.  The spectral order gives
exponential decay.  This is the constant-one branch of the Sylvester theory;
it is logically different from the two-sided Fourier branch, whose universal
constant is `pi/2`.
-/

namespace ForMathlib
namespace DavisKahanExt

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open Spectra.YosidaHille.Approximation

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The restriction to the full space has the original real spectrum.  Proved by
conjugating the top-restriction through `Submodule.topContEquiv` and invoking
spectral invariance of the induced endomorphism-algebra equivalence. -/
theorem restrictedSpectrum_top_eq_realSpectrum
    (T : E →L[ℂ] E) : restrictedSpectrum T ⊤ = realSpectrum T := by
  have hInv :
      ForMathlib.DavisKahan.Experimental.Foundation.InvariantFor T (⊤ : Submodule ℂ E) :=
    fun x _ => Submodule.mem_top
  have hbridge :=
    ForMathlib.DavisKahan.Experimental.Foundation.restrictedSpectrum_eq_restrictionSpectrum
      T ⊤ hInv
  have hconj :
      (Submodule.topContEquiv : (⊤ : Submodule ℂ E) ≃L[ℂ] E).conjContinuousAlgEquiv
        (T.restrict hInv) = T := by
    ext x
    rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    show ((T.restrict hInv) ((Submodule.topContEquiv :
      (⊤ : Submodule ℂ E) ≃L[ℂ] E).symm x) : E) = T x
    rw [ContinuousLinearMap.coe_restrict_apply]
    rfl
  have hspec : spectrum ℂ (T.restrict hInv) = spectrum ℂ T := by
    conv_rhs => rw [← hconj]
    exact (AlgEquiv.spectrum_eq
      ((Submodule.topContEquiv : (⊤ : Submodule ℂ E) ≃L[ℂ] E).conjContinuousAlgEquiv)
      (T.restrict hInv)).symm
  show ForMathlib.DavisKahan.Experimental.Foundation.restrictedSpectrum T ⊤ =
    ForMathlib.DavisKahan.Experimental.Foundation.realSpectrum T
  rw [hbridge]
  ext r
  simp only [ForMathlib.DavisKahan.Experimental.Foundation.realSpectrum,
    Set.mem_setOf_eq, hspec]

/-- A common cut between two compact ordered spectra. -/
theorem exists_common_cut_of_orderedSeparation
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d) :
    ∃ c : ℝ,
      realSpectrum B ⊆ Set.Iic c ∧
      realSpectrum A ⊆ Set.Ici (c + d) := by
  -- Open obligation: compactness and nonemptiness of the real spectrum
  -- (`realSpectrum_isCompact`, `realSpectrum_nonempty_of_selfAdjoint`) plus the
  -- restricted-spectrum bridge, handed to the mathematics agent.
  sorry

/-- Functional-calculus formula for the bounded exponential group. -/
theorem semigroup_eq_cfc
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T) (t : ℝ) :
    semigroup T t = cfc (fun z : ℂ => Complex.exp (t * z)) T := by
  -- Open obligation: agreement of the bounded exponential with the continuous
  -- functional calculus of `exp` on a self-adjoint operator, handed to the
  -- mathematics agent.
  sorry

/-- Upper spectral bound for a self-adjoint exponential. -/
theorem norm_semigroup_le_of_spectrum_subset_Iic
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Iic c) :
    ‖semigroup T t‖ ≤ Real.exp (t * c) := by
  -- Open obligation: the self-adjoint CFC norm bound `‖f(T)‖ ≤ sup_{σ(T)} |f|`
  -- (Mathlib `norm_cfc_le`) composed with `semigroup_eq_cfc`, handed to the
  -- mathematics agent.
  sorry

/-- Lower spectral bound, written as decay of `exp(-t T)`. -/
theorem norm_semigroup_neg_le_of_spectrum_subset_Ici
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Ici c) :
    ‖semigroup (-T) t‖ ≤ Real.exp (-t * c) := by
  -- Open obligation: negation of a self-adjoint operator and the spectral
  -- reflection `σ(-T) = -σ(T)`, composed with the upper bound above; handed to
  -- the mathematics agent.
  sorry

/-- The ordered semigroup integrand has the sharp exponential majorant. -/
theorem orderedSemigroup_integrand_bound
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    ∀ t ≥ 0,
      ‖semigroup (-A) t ∘L C ∘L semigroup B t‖ ≤
        Real.exp (-d * t) * ‖C‖ := by
  obtain ⟨c, hBc, hAc⟩ :=
    exists_common_cut_of_orderedSeparation hA hB hd hsep
  intro t ht
  have hleft := norm_semigroup_neg_le_of_spectrum_subset_Ici A hA ht hAc
  have hright := norm_semigroup_le_of_spectrum_subset_Iic B hB ht hBc
  calc
    ‖semigroup (-A) t ∘L C ∘L semigroup B t‖
        ≤ ‖semigroup (-A) t‖ * ‖C‖ * ‖semigroup B t‖ := by
          refine ((semigroup (-A) t).opNorm_comp_le (C ∘L semigroup B t)).trans ?_
          rw [mul_assoc]
          gcongr
          exact C.opNorm_comp_le (semigroup B t)
    _ ≤ Real.exp (-t * (c + d)) * ‖C‖ * Real.exp (t * c) := by
      gcongr
    _ = Real.exp (-d * t) * ‖C‖ := by
      rw [mul_right_comm, ← Real.exp_add,
        show -t * (c + d) + t * c = -d * t from by ring]

/-- Bochner integrability of the ordered semigroup formula. -/
theorem orderedSylvester_integrable
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  have hcontA : Continuous (semigroup (-A)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup (-A) t).continuousAt
  have hcontB : Continuous (semigroup B) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup B t).continuousAt
  have hcont : Continuous (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) :=
    (hcontA.clm_comp continuous_const).clm_comp hcontB
  have hmajor : IntegrableOn (fun t : ℝ => Real.exp (-d * t) * ‖C‖) (Set.Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 hd).congr_set_ae Ioi_ae_eq_Ici.symm).mul_const ‖C‖
  -- Dominate the operator-valued indicator by the `ℝ`-valued exponential
  -- indicator, sidestepping the continuous-linear-map `enorm` instance diamond.
  refine (hmajor.integrable_indicator measurableSet_Ici).mono'
    (hcont.aestronglyMeasurable.indicator measurableSet_Ici) ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Ici 0
  · simp only [Set.indicator_of_mem ht]
    exact orderedSemigroup_integrand_bound hA hB hd hsep C t ht
  · simp only [Set.indicator_of_notMem ht, norm_zero, le_refl]

/-- Derivative of the conjugated solution orbit. -/
theorem hasDerivAt_ordered_solution_orbit
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) (t : ℝ) :
    HasDerivAt
      (fun s => semigroup (-A) s ∘L X ∘L semigroup B s)
      (-(semigroup (-A) t ∘L C ∘L semigroup B t)) t := by
  -- Open obligation: the product rule for the conjugated orbit
  -- `s ↦ e^{-sA} X e^{sB}` (bilinear-composition Fréchet derivative plus the
  -- generator commutation `B_commute_expBounded`), handed to the mathematics
  -- agent.
  sorry

/-- Finite-interval fundamental theorem for the ordered orbit. -/
theorem ordered_orbit_sub_eq_integral
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) {T : ℝ} (hT : 0 ≤ T) :
    X - semigroup (-A) T ∘L X ∘L semigroup B T =
      ∫ t in Set.Icc (0 : ℝ) T,
        semigroup (-A) t ∘L C ∘L semigroup B t := by
  -- Open obligation: the finite-interval fundamental theorem of calculus for
  -- the ordered orbit, depending on `hasDerivAt_ordered_solution_orbit`; handed
  -- to the mathematics agent.
  sorry

/-- The conjugated endpoint tends to zero under an ordered gap. -/
theorem tendsto_ordered_solution_orbit_zero
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (X : E →L[ℂ] F) :
    Tendsto (fun t : ℝ => semigroup (-A) t ∘L X ∘L semigroup B t)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound := orderedSemigroup_integrand_bound hA hB hd hsep X
  have hexp : Tendsto (fun t : ℝ => Real.exp (-d * t) * ‖X‖) atTop (nhds 0) := by
    have h : Tendsto (fun t : ℝ => Real.exp (-d * t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg (by linarith : -d < 0)).mpr tendsto_id)
    simpa using h.mul_const ‖X‖
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards with t using norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using hbound t ht

/-- Exact ordered-spectrum reconstruction. -/
theorem orderedSylvester_reconstruction
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    {X C : E →L[ℂ] F}
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  -- Open obligation: assemble the truncated-integral limit (endpoint decay via
  -- `tendsto_ordered_solution_orbit_zero`, `Ici`-integral as the limit of
  -- `Icc 0 T` integrals) into the reconstruction; handed to the mathematics
  -- agent.
  sorry

end

end DavisKahanExt
end ForMathlib
