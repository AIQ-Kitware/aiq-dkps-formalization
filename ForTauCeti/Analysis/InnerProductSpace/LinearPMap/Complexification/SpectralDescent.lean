/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Generalized from:
  `DavisKahan/SpectralTheory/Real/SpectralRestriction.lean`.
* Extraction class: **representation migration and generalization**.  The original
  argument was tied to the historical bundled real closed-operator type.  This
  module ports the spectral descent directly to Mathlib `LinearPMap` using the raw
  complexification in `LinearPMap.Complexification`.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Complexification
public import ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure.Construction

/-!
# Spectral descent for real partial linear maps

A real self-adjoint partial map is complexified canonically.  Its complexified
operator commutes with canonical conjugation.  Resolvent uniqueness then forces
its Cayley transform and spectral projections to respect the same real structure.
Consequently each complex spectral projection descends to a bounded real
orthogonal projection.

This module deliberately works directly with Mathlib `LinearPMap`.  It introduces
no parallel closed-operator bundle and no theorem-specific compatibility wrapper.
-/

public section

open scoped InnerProductSpace ComplexConjugate

namespace TauCeti
namespace LinearPMap

open RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Eℂ" => RealComplexification E

/-- Canonical conjugation preserves the coordinatewise domain of a complexified
real partial map. -/
noncomputable def complexifyRealConjugationDomain (A : E →ₗ.[ℝ] E)
    (z : (complexifyReal A).domain) : (complexifyReal A).domain :=
  ⟨conjugation (z : Eℂ), by
    have hz := (mem_complexifyReal_domain_iff A (z : Eℂ)).mp z.property
    rw [mem_complexifyReal_domain_iff]
    exact ⟨by simpa using hz.1, by simpa using A.domain.neg_mem hz.2⟩⟩

omit [CompleteSpace E] in
/-- The conjugated domain point has the expected underlying vector. -/
private theorem complexifyRealConjugationDomain_coe (A : E →ₗ.[ℝ] E)
    (z : (complexifyReal A).domain) :
    ((complexifyRealConjugationDomain A z : (complexifyReal A).domain) : Eℂ) =
      conjugation (z : Eℂ) := by
  rfl

omit [CompleteSpace E] in
/-- A raw complexified real partial map commutes with canonical conjugation on
its operator domain. -/
theorem complexifyReal_apply_conjugationDomain (A : E →ₗ.[ℝ] E)
    (z : (complexifyReal A).domain) :
    complexifyReal A (complexifyRealConjugationDomain A z) =
      conjugation (complexifyReal A z) := by
  have hz := (mem_complexifyReal_domain_iff A (z : Eℂ)).mp z.property
  let xr : A.domain := ⟨re (z : Eℂ), hz.1⟩
  let xi : A.domain := ⟨im (z : Eℂ), hz.2⟩
  let zr : (complexifyReal A).domain := complexifyRealOfRealDomain A xr
  let zi : (complexifyReal A).domain := complexifyRealOfRealDomain A xi
  have hzdecomp : z = zr + Complex.I • zi := by
    apply Subtype.ext
    change (z : Eℂ) =
      (complexifyRealOfRealDomain A xr : Eℂ) +
        Complex.I • (complexifyRealOfRealDomain A xi : Eℂ)
    rw [complexifyRealOfRealDomain_coe, complexifyRealOfRealDomain_coe]
    exact RealComplexification.eq_ofReal_add_I_smul_ofReal (z : Eℂ)
  have hjdecomp : complexifyRealConjugationDomain A z = zr - Complex.I • zi := by
    apply Subtype.ext
    change conjugation (z : Eℂ) =
      (complexifyRealOfRealDomain A xr : Eℂ) -
        Complex.I • (complexifyRealOfRealDomain A xi : Eℂ)
    rw [complexifyRealOfRealDomain_coe, complexifyRealOfRealDomain_coe]
    apply RealComplexification.ext <;> simp [xr, xi]
  rw [hjdecomp, hzdecomp, _root_.LinearPMap.map_sub, _root_.LinearPMap.map_add,
    _root_.LinearPMap.map_smul]
  apply RealComplexification.ext <;> simp [zr, zi]

omit [CompleteSpace E] in
/-- Resolvents of a raw complexified real partial map at conjugate spectral
parameters are exchanged by canonical conjugation.  Self-adjointness is not
needed: this follows purely from the two-sided inverse property. -/
theorem conjugateOperator_resolvent_complexifyReal
    (A : E →ₗ.[ℝ] E) {z : ℂ}
    (hz : z ∈ resolventSet (complexifyReal A))
    (hzc : (starRingEnd ℂ) z ∈ resolventSet (complexifyReal A)) :
    conjugateOperator (resolvent (complexifyReal A) hz) =
      resolvent (complexifyReal A) hzc := by
  apply ContinuousLinearMap.ext
  intro ξ
  let r : Eℂ := resolvent (complexifyReal A) hz (conjugation ξ)
  have hrdom : r ∈ (complexifyReal A).domain := resolvent_mem_domain hz (conjugation ξ)
  have hsolve : complexifyReal A ⟨r, hrdom⟩ - z • r = conjugation ξ :=
    sub_smul_resolvent hz (conjugation ξ)
  let jr : (complexifyReal A).domain :=
    complexifyRealConjugationDomain A ⟨r, hrdom⟩
  have happ : complexifyReal A jr =
      conjugation (complexifyReal A ⟨r, hrdom⟩) :=
    complexifyReal_apply_conjugationDomain A ⟨r, hrdom⟩
  have hjsolve : complexifyReal A jr - (starRingEnd ℂ) z • (jr : Eℂ) = ξ := by
    have h1 : complexifyReal A jr - (starRingEnd ℂ) z • (jr : Eℂ) =
        conjugation (complexifyReal A ⟨r, hrdom⟩ - z • r) := by
      rw [map_sub, conjugation_complex_smul, ← happ,
        complexifyRealConjugationDomain_coe]
    rw [h1, hsolve, conjugation_involutive]
  have hleft := resolvent_apply_sub_smul hzc jr
  rw [hjsolve] at hleft
  rw [conjugateOperator_apply]
  change conjugation r = resolvent (complexifyReal A) hzc ξ
  calc
    conjugation r = (jr : Eℂ) := by
      change conjugation r =
        ((complexifyRealConjugationDomain A ⟨r, hrdom⟩ :
          (complexifyReal A).domain) : Eℂ)
      exact (complexifyRealConjugationDomain_coe A ⟨r, hrdom⟩).symm
    _ = resolvent (complexifyReal A) hzc ξ := hleft.symm

/-- The Cayley transform of a complexified real self-adjoint partial map is sent
to its adjoint by canonical conjugation. -/
theorem conjugateOperator_cayley_complexifyReal
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A) :
    conjugateOperator (cayley (isSelfAdjoint_complexifyReal hA)) =
      star (cayley (isSelfAdjoint_complexifyReal hA)) := by
  set hAℂ := isSelfAdjoint_complexifyReal hA with hhAc
  have hni := negI_mem_resolventSet hAℂ
  have hi := I_mem_resolventSet hAℂ
  have hconjI : ((starRingEnd ℂ) (-Complex.I)) ∈ resolventSet (complexifyReal A) := by
    simpa using hi
  have hkey : conjugateOperator (resolvent (complexifyReal A) hni) =
      ContinuousLinearMap.adjoint (resolvent (complexifyReal A) hni) := by
    rw [conjugateOperator_resolvent_complexifyReal A hni hconjI,
      adjoint_resolvent hAℂ hni hconjI]
  simp only [cayley_def, conjugateOperator_sub, conjugateOperator_one,
    conjugateOperator_complex_smul, hkey, star_sub, star_one, star_smul,
    ContinuousLinearMap.star_eq_adjoint]
  rfl

/-- If a normal bounded operator on a real complexification satisfies `J U J = U⋆`,
canonical conjugation carries its continuous functional calculus at `f` to the
calculus at the conjugate symbol `f⋆`. -/
theorem conjugateOperator_cfcHom_of_adjoint
    {U : Eℂ →L[ℂ] Eℂ} (hU : IsStarNormal U)
    (hUc : conjugateOperator U = star U) (f : C(_root_.spectrum ℂ U, ℂ)) :
    conjugateOperator (cfcHom hU f) = cfcHom hU (star f) := by
  let Ψ : C(_root_.spectrum ℂ U, ℂ) →⋆ₐ[ℂ] (Eℂ →L[ℂ] Eℂ) :=
    { toFun := fun g => conjugateOperator (cfcHom hU (star g))
      map_one' := by rw [star_one, map_one, conjugateOperator_one]
      map_mul' := fun g h => by
        rw [star_mul', map_mul, conjugateOperator_mul]
      map_zero' := by rw [star_zero, map_zero, conjugateOperator_zero]
      map_add' := fun g h => by rw [star_add, map_add, conjugateOperator_add]
      commutes' := fun c => by
        simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one,
          conjugateOperator_complex_smul, conjugateOperator_one,
          Algebra.algebraMap_eq_smul_one]
        congr 1
        simp
      map_star' := fun g => by
        change conjugateOperator (cfcHom hU (star (star g))) =
          star (conjugateOperator (cfcHom hU (star g)))
        rw [star_star, ContinuousLinearMap.star_eq_adjoint,
          ← conjugateOperator_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
          ← map_star, star_star] }
  have hdist : ∀ g h : C(_root_.spectrum ℂ U, ℂ), dist (star g) (star h) ≤ dist g h := by
    intro g h
    refine (ContinuousMap.dist_le dist_nonneg).mpr fun x => ?_
    have hx : dist ((star g) x) ((star h) x) = dist (g x) (h x) := by
      simp only [ContinuousMap.star_apply, Complex.dist_eq, ← star_sub, norm_star]
    rw [hx]
    exact ContinuousMap.dist_apply_le_dist x
  have hstarcont : Continuous (star : C(_root_.spectrum ℂ U, ℂ) →
      C(_root_.spectrum ℂ U, ℂ)) := by
    refine (Isometry.of_dist_eq fun g h => le_antisymm (hdist g h) ?_).continuous
    simpa only [star_star] using hdist (star g) (star h)
  have hcont : Continuous Ψ := by
    change Continuous (fun g : C(_root_.spectrum ℂ U, ℂ) =>
      conjugateOperator (cfcHom hU (star g)))
    exact (isometry_conjugateOperator (E := E)).continuous.comp
      ((cfcHom_continuous hU).comp hstarcont)
  have hid : Ψ ((ContinuousMap.id ℂ).restrict (_root_.spectrum ℂ U)) = U := by
    change conjugateOperator (cfcHom hU (star ((ContinuousMap.id ℂ).restrict _))) = U
    rw [map_star, cfcHom_id hU, ← hUc, conjugateOperator_involutive]
  have heq : cfcHom hU = Ψ := cfcHom_eq_of_continuous_of_map_id hU Ψ hcont hid
  have happ : cfcHom hU (star f) =
      conjugateOperator (cfcHom hU (star (star f))) := DFunLike.congr_fun heq (star f)
  rw [star_star] at happ
  exact happ.symm

/-- The diagonal spectral measures of the Cayley transform of a complexified real
self-adjoint partial map are conjugation invariant. -/
theorem diagMeasure_conjugation_complexifyReal
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A) (η : Eℂ) :
    BorelCalculus.diagMeasure (isStarNormal_cayley (isSelfAdjoint_complexifyReal hA))
        (conjugation η) =
      BorelCalculus.diagMeasure (isStarNormal_cayley (isSelfAdjoint_complexifyReal hA)) η := by
  have hUc := conjugateOperator_cayley_complexifyReal hA
  refine BorelCalculus.diagMeasure_congr _ (DFunLike.ext _ _ fun g => ?_)
  rw [BorelCalculus.diagFunctional_apply, BorelCalculus.diagFunctional_apply]
  set T := cfcHom (isStarNormal_cayley (isSelfAdjoint_complexifyReal hA))
    (BorelCalculus.ofRealLM g.toContinuousMap) with hT
  have hfix : conjugateOperator T = T := by
    rw [hT, conjugateOperator_cfcHom_of_adjoint _ hUc,
      BorelCalculus.star_ofRealLM]
  have hstep : ⟪conjugation η, T (conjugation η)⟫_ℂ = ⟪T η, η⟫_ℂ := by
    have h1 : T (conjugation η) = conjugation (conjugateOperator T η) := by
      rw [conjugateOperator_apply, conjugation_involutive]
    rw [h1, hfix, inner_conjugation]
  rw [hstep, ← inner_conj_symm]
  simp

/-- Every measurable spectral projection of a raw complexified real self-adjoint
partial map is fixed by canonical conjugation. -/
theorem conjugateOperator_specProjection_complexifyReal
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    conjugateOperator (specProjection (isSelfAdjoint_complexifyReal hA) S hS) =
      specProjection (isSelfAdjoint_complexifyReal hA) S hS := by
  set hAℂ := isSelfAdjoint_complexifyReal hA with hhAc
  set hU := isStarNormal_cayley hAℂ with hhU
  set κ := cayleyInv hAℂ with hκ
  have hSm : MeasurableSet (κ ⁻¹' S) := measurable_cayleyInv hAℂ hS
  set ind : _root_.spectrum ℂ (cayley hAℂ) → ℂ :=
    (κ ⁻¹' S).indicator (fun _ => (1 : ℂ)) with hind
  have hIreal : ∀ η : Eℂ,
      (starRingEnd ℂ) (∫ w, ind w ∂(BorelCalculus.diagMeasure hU η)) =
        ∫ w, ind w ∂(BorelCalculus.diagMeasure hU η) := by
    intro η
    rw [hind, MeasureTheory.integral_indicator_const _ hSm]
    simp
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [conjugateOperator_apply, inner_conjugation_right, ← inner_conj_symm,
    specProjection_eq_borelCalculus hAℂ S hS,
    BorelCalculus.inner_borelCalculus, BorelCalculus.inner_borelCalculus]
  have h1 : conjugation ξ + conjugation ψ = conjugation (ξ + ψ) :=
    (map_add _ _ _).symm
  have h2 : conjugation ξ + Complex.I • conjugation ψ =
      conjugation (ξ - Complex.I • ψ) := by
    rw [map_sub, conjugation_complex_smul, Complex.conj_I]
    module
  have h3 : conjugation ξ - conjugation ψ = conjugation (ξ - ψ) :=
    (map_sub _ _ _).symm
  have h4 : conjugation ξ - Complex.I • conjugation ψ =
      conjugation (ξ + Complex.I • ψ) := by
    rw [map_add, conjugation_complex_smul, Complex.conj_I]
    module
  simp only [BorelCalculus.pair_def, h1, h2, h3, h4,
    diagMeasure_conjugation_complexifyReal hA]
  have e1 := hIreal (ξ + ψ)
  have e2 := hIreal (ξ + Complex.I • ψ)
  have e3 := hIreal (ξ - ψ)
  have e4 := hIreal (ξ - Complex.I • ψ)
  simp only [map_mul, map_sub, map_add, map_one, map_div₀, Complex.conj_I,
    Complex.conj_ofNat]
  rw [e1, e2, e3, e4]
  ring

/-- The canonical real spectral projection of a raw real self-adjoint partial map,
obtained by descending the complex spectral projection. -/
noncomputable def realSpecProjection
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) : E →L[ℝ] E :=
  realPartOperator (specProjection (isSelfAdjoint_complexifyReal hA) S hS)

/-- Complexifying the descended real spectral projection recovers exactly the
canonical complex spectral projection. -/
theorem complexify_realSpecProjection
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    RealComplexification.complexify (realSpecProjection hA S hS) =
      specProjection (isSelfAdjoint_complexifyReal hA) S hS := by
  exact complexify_realPartOperator
    (conjugateOperator_specProjection_complexifyReal hA S hS)

/-- The complex spectral projection acts on the real copy exactly as the descended
real projection. -/
theorem specProjection_complexifyReal_ofReal
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) (x : E) :
    specProjection (isSelfAdjoint_complexifyReal hA) S hS (ofReal x) =
      ofReal (realSpecProjection hA S hS x) := by
  rw [← complexify_realSpecProjection hA S hS]
  simp

/-- The descended real spectral projection is idempotent. -/
theorem realSpecProjection_idem
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSpecProjection hA S hS * realSpecProjection hA S hS =
      realSpecProjection hA S hS := by
  change realSpecProjection hA S hS ∘L realSpecProjection hA S hS =
    realSpecProjection hA S hS
  apply RealComplexification.complexify_injective
  rw [RealComplexification.complexify_comp, complexify_realSpecProjection]
  change specProjection (isSelfAdjoint_complexifyReal hA) S hS *
      specProjection (isSelfAdjoint_complexifyReal hA) S hS = _
  exact isIdempotentElem_specProjection (isSelfAdjoint_complexifyReal hA) S hS

/-- The descended real spectral projection is self-adjoint. -/
theorem realSpecProjection_isSelfAdjoint
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    _root_.IsSelfAdjoint (realSpecProjection hA S hS) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply RealComplexification.complexify_injective
  rw [RealComplexification.complexify_adjoint, complexify_realSpecProjection]
  exact (isSelfAdjoint_specProjection (isSelfAdjoint_complexifyReal hA) S hS).adjoint_eq

end

end LinearPMap
end TauCeti
