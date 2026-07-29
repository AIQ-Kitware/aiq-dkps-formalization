/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.QuantumMechanics.BornRule.Joint.Defs
import Spectra.YosidaHille.Basic
import Spectra.Resolvent.Integral.Domain

/-!
# Rectangular intertwining for Stone groups and spectral calculi

A bounded map between two Hilbert spaces that intertwines the generators of
strongly continuous unitary groups also intertwines the groups themselves.
Fourier determinacy of the polarized spectral forms then promotes the group
identity to every bounded Borel symbol and, in particular, to every spectral
projection.

The result is rectangular: the source and target Hilbert spaces need not agree.
This is the natural tool for uniqueness of bounded solutions of homogeneous
Sylvester equations under arbitrary disjoint self-adjoint spectra.
-/

open InnerProductSpace Complex Filter Topology
open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup

namespace Spectra.YosidaHille

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Domain-aware intertwining of the generators of two unitary groups. -/
structure GeneratorIntertwines
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (X : F →L[ℂ] E) : Prop where
  mapsTo_domain : ∀ x : (generator V).domain, X (x : F) ∈ (generator U).domain
  equation : ∀ x : (generator V).domain,
    generator U ⟨X (x : F), mapsTo_domain x⟩ = X (generator V x)

namespace GeneratorIntertwines

/-- Generator intertwining is preserved along the source unitary orbit. -/
lemma equation_orbit
    {U : OneParameterUnitaryGroup (H := E)}
    {V : OneParameterUnitaryGroup (H := F)}
    {X : F →L[ℂ] E}
    (h : GeneratorIntertwines U V X)
    (s : ℝ) (x : (generator V).domain) :
    generator U
        ⟨X (V.U s (x : F)),
          h.mapsTo_domain
            ⟨V.U s (x : F), generator_domain_invariant V s x⟩⟩
      = X (V.U s (generator V x)) := by
  let xs : (generator V).domain :=
    ⟨V.U s (x : F), generator_domain_invariant V s x⟩
  calc
    generator U ⟨X (V.U s (x : F)), h.mapsTo_domain xs⟩
        = X (generator V xs) := h.equation xs
    _ = X (V.U s (generator V x)) := by rw [generator_comm]

open Spectra.Resolvent in
/-- **Rectangular Stone intertwining.**  A bounded generator intertwiner
intertwines the full one-parameter unitary groups. -/
theorem group
    {U : OneParameterUnitaryGroup (H := E)}
    {V : OneParameterUnitaryGroup (H := F)}
    {X : F →L[ℂ] E}
    (h : GeneratorIntertwines U V X) :
    ∀ t : ℝ, U.U t ∘L X = X ∘L V.U t := by
  intro t
  have hdense : Dense ((generator V).domain : Set F) :=
    generatorDomain_dense_via_average V
  have hpt : ∀ x ∈ (generator V).domain,
      U.U t (X x) = X (V.U t x) := by
    intro x hx
    let xd : (generator V).domain := ⟨x, hx⟩
    let g : ℝ → E := fun s => U.U (t - s) (X (V.U s x))
    have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
      intro s
      let xs : (generator V).domain :=
        ⟨V.U s x, generator_domain_invariant V s xd⟩
      have hVderiv := unitary_orbit_hasDerivAt V xd s
      have hXderiv : HasDerivAt (fun r => X (V.U r x))
          (I • X (V.U s (generator V xd))) s := by
        have hcomp := ((X.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hVderiv)
        simpa only [ContinuousLinearMap.coe_restrictScalars', map_smul,
          Function.comp_def, xd] using hcomp
      have hcurve := group_apply_curve_hasDerivAt U
        (v := fun r => X (V.U r x))
        (v' := I • X (V.U s (generator V xd)))
        (r := fun r => t - r) (r' := -1) (s := s)
        hXderiv ((hasDerivAt_id s).const_sub t)
        (h.mapsTo_domain xs)
      have hkey : generator U
          ⟨X (V.U s x), h.mapsTo_domain xs⟩
          = X (V.U s (generator V xd)) := h.equation_orbit s xd
      rw [show (-1 : ℝ) •
            (I • U.U (t - s)
              (generator U ⟨X (V.U s x), h.mapsTo_domain xs⟩))
            + U.U (t - s) (I • X (V.U s (generator V xd))) = 0 by
          rw [hkey, map_smul, neg_one_smul, neg_add_cancel]] at hcurve
      exact hcurve
    have hconst : g 0 = g t :=
      is_const_of_deriv_eq_zero
        (fun s => (hg s).differentiableAt)
        (fun s => (hg s).deriv) 0 t
    simpa [g, U.identity, V.identity, ContinuousLinearMap.id_apply,
      sub_zero, sub_self] using hconst
  apply ContinuousLinearMap.ext
  intro x
  change U.U t (X x) = X (V.U t x)
  exact congrFun
    (Continuous.ext_on hdense
      ((U.U t) ∘L X).continuous
      (X ∘L V.U t).continuous
      (fun x hx => hpt x hx)) x

end GeneratorIntertwines

end
end Spectra.YosidaHille

namespace Spectra.QuantumMechanics.SpectralTheory

open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.Borel
open Spectra.YosidaHille

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Character determinacy for polarized spectral forms belonging to two
possibly different unitary groups and Hilbert spaces. -/
theorem rectangularSpectralForm_ext_of_char
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (ξ₁ η₁ : E) (ξ₂ η₂ : F)
    (hchar : ∀ t : ℝ,
      spectralForm U ξ₁ η₁ (fun l => cexp (I * l * t)) =
        spectralForm V ξ₂ η₂ (fun l => cexp (I * l * t)))
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U ξ₁ η₁ g = spectralForm V ξ₂ η₂ g := by
  have key := Spectra.Fourier.integral_combination_ext'
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)] : Fin 4 → ℂ)
    (fun i => borelMeasure U
      (![ξ₁ + η₁, ξ₁ - η₁, ξ₁ - I • η₁, ξ₁ + I • η₁] i))
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)] : Fin 4 → ℂ)
    (fun j => borelMeasure V
      (![ξ₂ + η₂, ξ₂ - η₂, ξ₂ - I • η₂, ξ₂ + I • η₂] j))
    (fun t => by
      have ht := hchar t
      simp only [spectralForm] at ht
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero]
      linear_combination ht)
    hgm hgb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at key
  simp only [spectralForm]
  linear_combination key

/-- A rectangular group intertwiner intertwines every bounded Borel spectral
calculus. -/
theorem spectralCalculus_intertwines_of_group
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (X : F →L[ℂ] E)
    (hX : ∀ t : ℝ, U.U t ∘L X = X ∘L V.U t)
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralCalculus U g hgm hgb ∘L X =
      X ∘L spectralCalculus V g hgm hgb := by
  have hkey : ∀ ξ : E, ∀ η : F,
      spectralForm U ξ (X η) g =
        spectralForm V (ContinuousLinearMap.adjoint X ξ) η g := by
    intro ξ η
    refine rectangularSpectralForm_ext_of_char U V
      ξ (X η) (ContinuousLinearMap.adjoint X ξ) η
      (fun t => ?_) hgm hgb
    rw [spectralForm_char, spectralForm_char]
    have hintertwine : U.U t (X η) = X (V.U t η) := by
      have ht := congrArg (fun T : F →L[ℂ] E => T η) (hX t)
      simpa only [ContinuousLinearMap.comp_apply] using ht
    rw [hintertwine, ContinuousLinearMap.adjoint_inner_left]
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_spectralCalculus,
    ← ContinuousLinearMap.adjoint_inner_left X
      (spectralCalculus V g hgm hgb η) ξ,
    inner_spectralCalculus]
  exact hkey ξ η

/-- A rectangular generator intertwiner intertwines every bounded Borel
spectral calculus. -/
theorem spectralCalculus_intertwines_of_generator
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (X : F →L[ℂ] E)
    (hX : GeneratorIntertwines U V X)
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralCalculus U g hgm hgb ∘L X =
      X ∘L spectralCalculus V g hgm hgb :=
  spectralCalculus_intertwines_of_group U V X hX.group hgm hgb

/-- A rectangular generator intertwiner intertwines every spectral
projection. -/
theorem spectralProjection_intertwines_of_generator
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (X : F →L[ℂ] E)
    (hX : GeneratorIntertwines U V X)
    (S : Set ℝ) (hS : MeasurableSet S) :
    spectralProjection U S hS ∘L X = X ∘L spectralProjection V S hS := by
  exact spectralCalculus_intertwines_of_generator U V X hX
    (measurable_const.indicator hS) (indicator_one_bdd S)

end
end Spectra.QuantumMechanics.SpectralTheory
