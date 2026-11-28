/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import DavisKahan.BoundedOperator.Problem
public import DavisKahan.SpectralTheory.AbstractSpectrum
public import DavisKahan.SpectralTheory.PartialMap.RealSpectrum
public import DavisKahan.SpectralTheory.PartialMap.BoundedRealization
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Bounded

/-!
# Boundedness from a bounded spectrum

A closed densely defined self-adjoint operator whose spectrum lies in the
bounded interval `[β, α]` is defined on the whole space and bounded, with the
sharp centered estimate `‖A - (β+α)/2‖ ≤ (α-β)/2`.

The spectral projection of the interval is the identity since the complement
consists of resolvent points. TauCeti's `mem_graph_spectralCut` identifies the
operator on this full range with the centered spectral cut plus the midpoint.
The native spectral-cut norm bound gives the centered estimate directly.

Until 2026-07-29 this went through Spectra: the operator was realized as the
generator of its Yosida group and the four bricks were Spectra's.  The Stone
group is not needed — the spectral measure is constructed directly from the
Cayley transform, and `A` is its own generator.

This is the missing seam for the fully unbounded interval/exterior orientation
of Davis--Kahan Theorem 5.2: the interval block of the configuration is
secretly a bounded operator.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Boundedness from a bounded spectrum.**  A closed densely defined
self-adjoint operator with spectrum contained in `[β, α]` admits a bounded
realization on the whole space, centered within distance `(α - β)/2` of the
midpoint multiple of the identity. -/
theorem exists_boundedRealization_of_spectrum_subset_Icc
    {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A)
    {β α : ℝ} (hβα : β ≤ α)
    (hσ : Complex.ofReal ⁻¹' _root_.LinearPMap.spectrum A ⊆
        Set.Icc β α) :
    ∃ R : BoundedRealization (𝕜 := ℂ) (E := H) A,
      ‖R.operator - (((β + α) / 2 : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ H‖ ≤ (α - β) / 2 := by
  have hB : MeasurableSet (Set.Icc β α) := measurableSet_Icc
  have hprojc : (A.spectralPVM hA).proj (Set.Icc β α)ᶜ hB.compl = 0 := by
    apply hA.spectralPVM_proj_eq_zero_of_forall_mem_resolventSet hB.compl
    intro t ht
    by_contra hres
    exact ht (hσ ((_root_.LinearPMap.mem_spectrum_iff A (t : ℂ)).2 hres))
  have hproj : (A.spectralPVM hA).proj (Set.Icc β α) hB =
      ContinuousLinearMap.id ℂ H := by
    rw [ProjValMeasure.proj_compl] at hprojc
    exact (sub_eq_zero.mp hprojc).symm
  let c := (β + α) / 2
  let r := (α - β) / 2
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hβα) (by norm_num)
  have hcr : ∀ t ∈ Set.Icc β α, |t - c| ≤ r := by
    intro t ht
    dsimp [c, r]
    rw [abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let C := A.spectralCut hA (Set.Icc β α) hB c r hr hcr
  let T := C + (c : ℂ) • ContinuousLinearMap.id ℂ H
  have hgraph (x : H) : (x, T x) ∈ A.graph := by
    have hx := hA.mem_graph_spectralCut (Set.Icc β α) hB c r hr hcr x
    rw [hproj, ContinuousLinearMap.id_apply] at hx
    exact hx
  refine ⟨⟨T, Submodule.eq_top_iff'.mpr (fun x => _root_.LinearPMap.mem_domain_of_mem_graph
    (hgraph x)), fun x => A.mem_graph_snd_inj (hgraph x) (A.mem_graph x) rfl⟩, ?_⟩
  change ‖C + (c : ℂ) • ContinuousLinearMap.id ℂ H - (c : ℂ) •
    ContinuousLinearMap.id ℂ H‖ ≤ r
  rw [add_sub_cancel_right]
  exact hA.norm_spectralCut_le (Set.Icc β α) hB c r hr hcr

end ExactSinTheta
end DavisKahan
end TauCeti
