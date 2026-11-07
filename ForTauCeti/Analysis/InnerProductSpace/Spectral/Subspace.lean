/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.SpectralOrder
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Finite-dimensional spectral subspaces

Restriction/ambient point-spectrum correspondences, the real-spectrum bridge for finite
continuous realizations, and the quadratic-form consequences used by Davis--Kahan.
Invariant submodules and orthogonal projections use canonical Mathlib and Tau Ceti APIs.

The point-spectrum predicates name eigenvalue data explicitly; the quadratic-form results
reduce to the generic bounded spectral-order API after restricting to an invariant subspace.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-! ### Restriction to an invariant subspace and the restricted-spectrum bridge

These give the concrete restriction `A.restrict hU : U →ₗ[𝕜] U` of an operator to
an invariant subspace and identify its full point spectrum with the `U`-carried
point spectrum of `A`.  This is the bridge used to discharge the spectral
hypotheses of the residual/perturbation `sin Θ` theorems on the subtype. -/

omit [FiniteDimensional 𝕜 E] in
/-- **The restricted-spectrum bridge.**  The point spectrum of the restriction
`A.restrict hU : U →ₗ[𝕜] U` (over the whole `⊤`) equals the `U`-carried point
spectrum of `A`.  Eigenvectors transport across the subtype coercion. -/
theorem restrictedPointSpectrum_restrict (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : (U ∈ Module.End.invtSubmodule A)) :
    Module.End.restrictedPointSpectrum (A.restrict hU) ⊤ =
      Module.End.restrictedPointSpectrum A U := by
  ext lam
  constructor
  · intro hlam
    obtain ⟨x, -, hx0, hxEig⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hlam
    refine Module.End.mem_restrictedPointSpectrum x.2 (fun hx => hx0 (Subtype.ext hx)) ?_
    -- The restriction equality is pointwise after taking the subtype coercion.
    exact congrArg (Subtype.val) hxEig
  · intro hlam
    obtain ⟨x, hxU, hx0, hxEig⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hlam
    refine Module.End.mem_restrictedPointSpectrum (x := ⟨x, hxU⟩) Submodule.mem_top
      (fun hxu => hx0 (congrArg Subtype.val hxu)) ?_
    apply Subtype.ext
    exact hxEig

omit [FiniteDimensional 𝕜 E] in
/-- The containment form of the restricted-spectrum bridge: `A.restrict hU` has
spectrum in `s` iff `A` carries spectrum in `s` on `U`. -/
theorem pointSpectrumIn_restrict_iff (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : (U ∈ Module.End.invtSubmodule A)) (s : Set ℝ) :
    Module.End.PointSpectrumIn (A.restrict hU) ⊤ s ↔ Module.End.PointSpectrumIn A U s := by
  constructor
  · intro h
    apply Module.End.pointSpectrumIn_iff.mpr
    intro x hxU hx0 lam hAx
    have hsub := Module.End.pointSpectrumIn_iff.mp h
    have hxeq : (A.restrict hU) ⟨x, hxU⟩ = (lam : 𝕜) • ⟨x, hxU⟩ := by
      apply Subtype.ext
      change A x = (lam : 𝕜) • x
      exact hAx
    exact hsub ⟨x, hxU⟩ Submodule.mem_top
      (fun hzero => hx0 (congrArg (Subtype.val) hzero)) lam hxeq
  · intro h
    apply Module.End.pointSpectrumIn_iff.mpr
    intro x hxTop hx0 lam hAx
    have hambient := Module.End.pointSpectrumIn_iff.mp h
    have hxeq : A (x : E) = (lam : 𝕜) • (x : E) := by
      have h := congrArg (Subtype.val) hAx
      change A (x : E) = (lam : 𝕜) • (x : E) at h
      exact h
    exact hambient (x : E) x.property
      (fun hzero => hx0 (Subtype.ext hzero)) lam hxeq

/-! ### Spectral gap ⟹ quadratic-form coercivity bridge

These convert the abstract eigenvalue-set hypotheses (`Module.End.PointSpectrumIn A U s`) into the
quadratic-form bounds `re ⟪A x, x⟫ ≤ c ‖x‖²` (or `≥`) that the dimension-free
operator-norm Sylvester/`sin Θ` machinery consumes.  This is the point where
finite-dimensional injectivity-surjectivity identifies point and algebra spectra.
The ensuing coercivity estimate is supplied by the generic spectral-order theorem. -/

section SpectralOrder

-- These operator-algebra instances must not change scalar elaboration outside this section.
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower

/-- In finite dimension, the real algebra spectrum is exactly the real point spectrum.
No symmetry is needed for this equality: a noninvertible square linear map has a kernel. -/
theorem real_spectrum_toContinuousLinearMap_eq (A : E →ₗ[𝕜] E) :
    spectrum ℝ A.toContinuousLinearMap = Module.End.restrictedPointSpectrum A ⊤ := by
  have := FiniteDimensional.complete 𝕜 E
  ext r
  let S : E →L[𝕜] E := algebraMap ℝ (E →L[𝕜] E) r - A.toContinuousLinearMap
  have hc : algebraMap ℝ (E →L[𝕜] E) r =
      (algebraMap ℝ 𝕜 r) • (1 : E →L[𝕜] E) := by
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have hS (x : E) : S x = (r : 𝕜) • x - A x := by
    have happ : (algebraMap ℝ (E →L[𝕜] E) r) x = (r : 𝕜) • x := by
      rw [hc, smul_apply, one_apply_eq_self, RCLike.algebraMap_eq_ofReal]
    simp only [S, sub_apply, happ, LinearMap.coe_toContinuousLinearMap']
  rw [spectrum.mem_iff, Module.End.mem_restrictedPointSpectrum_iff]
  change (¬ IsUnit S) ↔ _
  constructor
  · intro hnot
    by_contra hnone
    have hzero : ∀ x : E, S x = 0 → x = 0 := by
      intro x hx
      by_contra hx0
      apply hnone
      exact ⟨x, Submodule.mem_top, hx0, (sub_eq_zero.mp ((hS x).symm.trans hx)).symm⟩
    have hinj : Function.Injective S := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply hzero
      rw [map_sub, hxy, sub_self]
    exact hnot (ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩)
  · rintro ⟨x, -, hx0, hAx⟩ hunit
    apply hx0
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    simp [hS, hAx]

/-- Spectral containment gives an upper form bound on an invariant subspace. -/
theorem upperFormBound_of_pointSpectrumIn {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : (U ∈ Module.End.invtSubmodule A)) {c : ℝ}
    (hSpec : Module.End.PointSpectrumIn A U (Set.Iic c)) :
    ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  have := FiniteDimensional.complete 𝕜 U
  have hsym : IsSelfAdjoint (A.restrict hU).toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (hA.restrict_invariant hU)
  have hspec : spectrum ℝ (A.restrict hU).toContinuousLinearMap ⊆ Set.Iic c := by
    rw [real_spectrum_toContinuousLinearMap_eq, restrictedPointSpectrum_restrict]
    intro lam hlam
    obtain ⟨x, hxU, hx0, hAx⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hlam
    exact (Module.End.pointSpectrumIn_iff.mp hSpec) x hxU hx0 lam hAx
  intro x hx
  exact ContinuousLinearMap.re_inner_le_of_spectrum_subset_Iic _ hsym hspec ⟨x, hx⟩

/-- Spectral containment gives a lower form bound on an invariant subspace. -/
theorem lowerFormBound_of_pointSpectrumIn {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : (U ∈ Module.End.invtSubmodule A)) {c : ℝ}
    (hSpec : Module.End.PointSpectrumIn A U (Set.Ici c)) :
    ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  have := FiniteDimensional.complete 𝕜 U
  have hsym : IsSelfAdjoint (A.restrict hU).toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (hA.restrict_invariant hU)
  have hspec : spectrum ℝ (A.restrict hU).toContinuousLinearMap ⊆ Set.Ici c := by
    rw [real_spectrum_toContinuousLinearMap_eq, restrictedPointSpectrum_restrict]
    intro lam hlam
    obtain ⟨x, hxU, hx0, hAx⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hlam
    exact (Module.End.pointSpectrumIn_iff.mp hSpec) x hxU hx0 lam hAx
  intro x hx
  exact ContinuousLinearMap.le_re_inner_of_spectrum_subset_Ici _ hsym hspec ⟨x, hx⟩

end SpectralOrder

end TauCeti
