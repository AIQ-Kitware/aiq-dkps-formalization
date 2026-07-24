/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.SpectralTheory.ClosedOperator.BoundedRealization
import Spectra.SpectralTheory.Essential.Discrete
import Spectra.SpectralTheory.Measure.GeneratorLink

/-!
# Boundedness from a bounded spectrum

A closed densely defined self-adjoint operator whose Spectra spectrum lies
in the bounded interval `[β, α]` is defined on the whole space and bounded,
with the sharp centered estimate `‖A - (β+α)/2‖ ≤ (α-β)/2`.

The proof assembles four Spectra bricks:

* `spectralPVM_proj_eq_zero_of_subset_resolventSet` — the spectral
  projection vanishes off the spectrum, so `E([β,α]ᶜ) = 0`;
* `spectralProjection_compl` — complementation gives `E([β,α]) = 1`;
* `spectralProjection_mem_generatorDomain` — spectrally bounded vectors lie
  in the generator's domain, so the domain is the whole space;
* `generator_sub_smul_norm_le_Icc` — the centered norm bound on the
  spectral interval.

The generator of the Yosida group of `A` is `A` itself
(`generator_genToGroup`), which transports all four statements to `A`.
This is the missing seam for the fully unbounded interval/exterior
orientation of Davis--Kahan Theorem 5.2: the interval block of the
configuration is secretly a bounded operator.

Upstream candidate: the statement is Spectra-idiomatic and belongs next to
the spectral-projection algebra.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Resolvent
open Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Boundedness from a bounded spectrum.**  A closed densely defined
self-adjoint operator with spectrum contained in `[β, α]` admits a bounded
realization on the whole space, centered within distance `(α - β)/2` of the
midpoint multiple of the identity. -/
theorem exists_boundedRealization_of_spectrum_subset_Icc
    {A : SpectraBridge.DKClosedOperator (H := H)}
    (hA : IsSelfAdjoint A.toLinearPMap)
    {β α : ℝ} (hβα : β ≤ α)
    (hσ : Spectra.Resolvent.spectrum A.toLinearPMap ⊆ Set.Icc β α) :
    ∃ R : BoundedRealization (𝕜 := ℂ) (E := H) A,
      ‖R.operator - (((β + α) / 2 : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ H‖ ≤ (α - β) / 2 := by
  classical
  have hgen : generator (genToGroup hA) = A.toLinearPMap :=
    generator_genToGroup hA
  -- every point outside `[β, α]` is a resolvent point
  have hres : ∀ lam ∈ (Set.Icc β α)ᶜ,
      (lam : ℂ) ∈ resolventSet A.toLinearPMap := by
    intro lam hlam
    by_contra hnot
    exact hlam (hσ hnot)
  -- the spectral projection of the complement vanishes
  have hprojc : spectralProjection (genToGroup hA) (Set.Icc β α)ᶜ
      measurableSet_Icc.compl = 0 := by
    have h := spectralPVM_proj_eq_zero_of_subset_resolventSet hA
      measurableSet_Icc.compl hres
    simpa using h
  -- the interval carries the full projection
  have hprojid : spectralProjection (genToGroup hA) (Set.Icc β α)
      measurableSet_Icc = ContinuousLinearMap.id ℂ H := by
    have hc := spectralProjection_compl (genToGroup hA) (Set.Icc β α)
      measurableSet_Icc
    rw [hprojc] at hc
    exact (sub_eq_zero.mp hc.symm).symm
  have hEfix : ∀ φ : H, spectralProjection (genToGroup hA) (Set.Icc β α)
      measurableSet_Icc φ = φ := fun φ => by rw [hprojid]; rfl
  -- absolute bound on the interval
  have hRabs : ∀ x ∈ Set.Icc β α, |x| ≤ max |β| |α| := by
    intro x hx
    rw [abs_le]
    constructor
    · exact le_trans
        (le_trans (neg_le_neg (le_max_left |β| |α|)) (neg_abs_le β)) hx.1
    · exact le_trans hx.2 (le_trans (le_abs_self α) (le_max_right |β| |α|))
  -- every vector lies in the generator's domain
  have hdomAll : ∀ φ : H, φ ∈ (generator (genToGroup hA)).domain := by
    intro φ
    have h := spectralProjection_mem_generatorDomain (genToGroup hA)
      measurableSet_Icc hRabs φ
    rw [hEfix φ] at h
    exact h
  -- the centered pointwise estimate
  have hbound : ∀ φ : H,
      ‖generator (genToGroup hA) ⟨φ, hdomAll φ⟩ -
        ((β + α) / 2 : ℝ) • φ‖ ≤ (α - β) / 2 * ‖φ‖ := by
    intro φ
    have hmem : spectralProjection (genToGroup hA) (Set.Icc β α)
        measurableSet_Icc φ ∈ (generator (genToGroup hA)).domain := by
      rw [hEfix φ]
      exact hdomAll φ
    have h := generator_sub_smul_norm_le_Icc (genToGroup hA) β α
      ((β + α) / 2) (by linarith) (by linarith) φ hmem
    have hsub : (⟨spectralProjection (genToGroup hA) (Set.Icc β α)
        measurableSet_Icc φ, hmem⟩ :
        (generator (genToGroup hA)).domain) = ⟨φ, hdomAll φ⟩ :=
      Subtype.ext (hEfix φ)
    rw [hsub, hEfix φ] at h
    have hmax : max ((β + α) / 2 - β) (α - (β + α) / 2) = (α - β) / 2 := by
      rw [show (β + α) / 2 - β = (α - β) / 2 by ring,
        show α - (β + α) / 2 = (α - β) / 2 by ring, max_self]
    rwa [hmax] at h
  -- the everywhere-defined linear realization
  let g : H →ₗ[ℂ] H :=
    { toFun := fun φ => generator (genToGroup hA) ⟨φ, hdomAll φ⟩
      map_add' := fun φ ψ => by
        have h : (⟨φ + ψ, hdomAll (φ + ψ)⟩ :
            (generator (genToGroup hA)).domain) =
            ⟨φ, hdomAll φ⟩ + ⟨ψ, hdomAll ψ⟩ := rfl
        rw [h, (generator (genToGroup hA)).map_add]
      map_smul' := fun c φ => by
        have h : (⟨c • φ, hdomAll (c • φ)⟩ :
            (generator (genToGroup hA)).domain) =
            c • ⟨φ, hdomAll φ⟩ := rfl
        rw [h, (generator (genToGroup hA)).map_smul]
        rfl }
  have hgφ : ∀ φ : H, g φ = generator (genToGroup hA) ⟨φ, hdomAll φ⟩ :=
    fun _ => rfl
  -- continuity of the realization
  have hgbound : ∀ φ : H,
      ‖g φ‖ ≤ (|(β + α) / 2| + (α - β) / 2) * ‖φ‖ := by
    intro φ
    have h := hbound φ
    rw [← hgφ φ] at h
    have h2 : ‖((β + α) / 2 : ℝ) • φ‖ = |(β + α) / 2| * ‖φ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    calc ‖g φ‖
        = ‖(g φ - ((β + α) / 2 : ℝ) • φ) + ((β + α) / 2 : ℝ) • φ‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖g φ - ((β + α) / 2 : ℝ) • φ‖ +
            ‖((β + α) / 2 : ℝ) • φ‖ := norm_add_le _ _
      _ ≤ (α - β) / 2 * ‖φ‖ + |(β + α) / 2| * ‖φ‖ := by
          rw [h2]
          exact add_le_add h le_rfl
      _ = (|(β + α) / 2| + (α - β) / 2) * ‖φ‖ := by ring
  let T : H →L[ℂ] H := g.mkContinuous _ hgbound
  have hTφ : ∀ φ : H, T φ = generator (genToGroup hA) ⟨φ, hdomAll φ⟩ :=
    fun _ => rfl
  -- application transport from the generator to `A`
  have happly := (LinearPMap.ext_iff.mp hgen).2
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · -- the domain is everything
    have hd : A.toLinearPMap.domain =
        (generator (genToGroup hA)).domain :=
      (congrArg LinearPMap.domain hgen).symm
    refine Submodule.eq_top_iff'.mpr fun φ => ?_
    have h := hdomAll φ
    rw [← hd] at h
    exact h
  · -- the realization agrees with `A` on the domain
    intro x
    have hx : (x : H) ∈ (generator (genToGroup hA)).domain :=
      hdomAll (x : H)
    have h : generator (genToGroup hA) ⟨(x : H), hx⟩ =
        A.toLinearPMap ⟨(x : H), x.2⟩ :=
      happly (x := (x : H)) (hf := hx) (hg := x.2)
    rw [hTφ (x : H)]
    exact h
  · -- the centered norm bound
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun φ => ?_
    have h := hbound φ
    rw [← hTφ φ] at h
    have hsm : (((β + α) / 2 : ℝ) : ℂ) • φ = ((β + α) / 2 : ℝ) • φ :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ φ).symm
    calc ‖(T - (((β + α) / 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H) φ‖
        = ‖T φ - ((β + α) / 2 : ℝ) • φ‖ := by
          rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, hsm]
      _ ≤ (α - β) / 2 * ‖φ‖ := h

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti