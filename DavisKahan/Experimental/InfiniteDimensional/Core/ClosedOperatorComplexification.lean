/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.ComplexificationSubspace
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded
import Spectra.Resolvent.Spectrum

/-!
# Complexification of real closed operators

This file transports the domain, action, graph, adjoint relation, form bounds,
resolvent, and domain-aware Sylvester equation of a real closed operator to the
concrete complexification of its Hilbert space.

The construction is coordinatewise.  The complexified domain consists of
vectors whose real and imaginary coordinates both lie in the original domain,
and the operator applies the original map to those two coordinates.  The graph
proof is the product closed-graph proof transported through the L2 coordinate
homeomorphism.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter Topology

noncomputable section

universe v

namespace ClosedOperatorComplexification

open Foundation
open Foundation.RealComplexification

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev Eℂ := RealComplexification E
abbrev Fℂ := RealComplexification F

/-- Each coordinate norm is bounded by the L2 norm. -/
theorem norm_re_le (z : Eℂ) : ‖re z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), RealComplexification.norm_sq]
  nlinarith [sq_nonneg ‖im z‖]

/-- Each coordinate norm is bounded by the L2 norm. -/
theorem norm_im_le (z : Eℂ) : ‖im z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), RealComplexification.norm_sq]
  nlinarith [sq_nonneg ‖re z‖]

/-- Coordinatewise complexification of a real closed-operator domain. -/
def domain (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    Submodule ℂ Eℂ :=
  complexifySubmodule A.domain

@[simp] theorem mem_domain_iff
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : Eℂ) :
    z ∈ domain A ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

/-- Real coordinate of a vector in the complexified operator domain. -/
def domainRe
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : domain A) : A.domain :=
  ⟨re (z : Eℂ), (mem_domain_iff A z).mp z.property |>.1⟩

/-- Imaginary coordinate of a vector in the complexified operator domain. -/
def domainIm
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : domain A) : A.domain :=
  ⟨im (z : Eℂ), (mem_domain_iff A z).mp z.property |>.2⟩

/-- Coordinatewise action on the complexified domain. -/
def linearMap
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    domain A →ₗ[ℂ] Eℂ where
  toFun z := mk (A.toLinearMap (domainRe A z))
    (A.toLinearMap (domainIm A z))
  map_add' z w := by
    apply RealComplexification.ext <;> simp [domainRe, domainIm]
  map_smul' c z := by
    apply RealComplexification.ext
    · change A.toLinearMap
          ⟨c.re • re (z : Eℂ) - c.im • im (z : Eℂ), _⟩ =
        c.re • A.toLinearMap (domainRe A z) -
          c.im • A.toLinearMap (domainIm A z)
      simpa [domainRe, domainIm] using
        A.toLinearMap.map_sub
          (c.re • domainRe A z) (c.im • domainIm A z)
    · change A.toLinearMap
          ⟨c.im • re (z : Eℂ) + c.re • im (z : Eℂ), _⟩ =
        c.im • A.toLinearMap (domainRe A z) +
          c.re • A.toLinearMap (domainIm A z)
      simpa [domainRe, domainIm] using
        A.toLinearMap.map_add
          (c.im • domainRe A z) (c.re • domainIm A z)

@[simp] theorem re_linearMap
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : domain A) :
    re (linearMap A z) = A.toLinearMap (domainRe A z) := rfl

@[simp] theorem im_linearMap
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : domain A) :
    im (linearMap A z) = A.toLinearMap (domainIm A z) := rfl

private theorem domain_dense
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    Dense ((domain A : Submodule ℂ Eℂ) : Set Eℂ) := by
  have hprod : Dense
      ((A.domain : Set E) ×ˢ (A.domain : Set E)) :=
    A.dense_domain.prod A.dense_domain
  have himage : Dense
      ((WithLp.homeomorphProd 2 E E).symm ''
        ((A.domain : Set E) ×ˢ (A.domain : Set E))) :=
    (((WithLp.homeomorphProd 2 E E).symm.isDenseEmbedding.dense_image).2 hprod)
  rw [show ((domain A : Submodule ℂ Eℂ) : Set Eℂ) =
      (WithLp.homeomorphProd 2 E E).symm ''
        ((A.domain : Set E) ×ˢ (A.domain : Set E)) by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, (mem_domain_iff A z).mp hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact (mem_domain_iff A _).2 hp]
  exact himage

private theorem linearMap_closedGraph
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    IsClosed (Set.range fun z : domain A =>
      ((z : Eℂ), linearMap A z)) := by
  let coords : (Eℂ × Eℂ) → ((E × E) × (E × E)) :=
    fun p => ((re p.1, re p.2), (im p.1, im p.2))
  have hcoords : Continuous coords := by
    fun_prop
  have hclosed : IsClosed
      ((Set.range fun x : A.domain => ((x : E), A.toLinearMap x)) ×ˢ
       (Set.range fun y : A.domain => ((y : E), A.toLinearMap y))) :=
    A.closed_graph.prod A.closed_graph
  rw [show Set.range (fun z : domain A => ((z : Eℂ), linearMap A z)) =
      coords ⁻¹'
        ((Set.range fun x : A.domain => ((x : E), A.toLinearMap x)) ×ˢ
         (Set.range fun y : A.domain => ((y : E), A.toLinearMap y))) by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨
        ⟨domainRe A z, by ext <;> rfl⟩,
        ⟨domainIm A z, by ext <;> rfl⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx0 : (x : E) = re p.1 := congrArg Prod.fst hx
      have hx1 : A.toLinearMap x = re p.2 := congrArg Prod.snd hx
      have hy0 : (y : E) = im p.1 := congrArg Prod.fst hy
      have hy1 : A.toLinearMap y = im p.2 := congrArg Prod.snd hy
      let z : domain A :=
        ⟨p.1, (mem_domain_iff A p.1).2
          ⟨hx0 ▸ x.property, hy0 ▸ y.property⟩⟩
      have hzr : domainRe A z = x := Subtype.ext hx0.symm
      have hzi : domainIm A z = y := Subtype.ext hy0.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply RealComplexification.ext
      · simpa [hzr] using hx1
      · simpa [hzi] using hy1]
  exact hclosed.preimage hcoords

/-- Coordinatewise complexification of a real closed operator. -/
def complexify
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := Eℂ) where
  domain := domain A
  toLinearMap := linearMap A
  dense_domain := domain_dense A
  closed_graph := linearMap_closedGraph A

@[simp] theorem complexify_domain
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    (complexify A).domain = domain A := rfl

@[simp] theorem mem_complexify_domain_iff
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : Eℂ) :
    z ∈ (complexify A).domain ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

@[simp] theorem complexify_apply_re
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : (complexify A).domain) :
    re ((complexify A).toLinearMap z) =
      A.toLinearMap ⟨re (z : Eℂ), (mem_complexify_domain_iff A z).mp z.property |>.1⟩ :=
  rfl

@[simp] theorem complexify_apply_im
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : (complexify A).domain) :
    im ((complexify A).toLinearMap z) =
      A.toLinearMap ⟨im (z : Eℂ), (mem_complexify_domain_iff A z).mp z.property |>.2⟩ :=
  rfl

/-- The real copy of a domain vector lies in the complexified domain. -/
def ofRealDomain
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (x : A.domain) : (complexify A).domain :=
  ⟨ofReal (x : E), by simpa using x.property⟩

@[simp] theorem complexify_apply_ofReal
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (x : A.domain) :
    (complexify A).toLinearMap (ofRealDomain A x) =
      ofReal (A.toLinearMap x) := by
  apply RealComplexification.ext <;> simp [ofRealDomain]

/-- The imaginary copy of a domain vector lies in the complexified domain. -/
def ofImaginaryDomain
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (x : A.domain) : (complexify A).domain :=
  ⟨Complex.I • ofReal (x : E), by
    rw [mem_complexify_domain_iff]
    simp only [I_smul_ofReal, re_mk, im_mk]
    exact ⟨A.domain.zero_mem, x.property⟩⟩

@[simp] theorem complexify_apply_ofImaginary
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (x : A.domain) :
    (complexify A).toLinearMap (ofImaginaryDomain A x) =
      Complex.I • ofReal (A.toLinearMap x) := by
  apply RealComplexification.ext <;> simp [ofImaginaryDomain]

/-- Complexification commutes with embedding a bounded operator as a closed
operator. -/
theorem complexify_ofBounded
    (T : E →L[ℝ] E) :
    complexify (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded T) =
      ForMathlib.DavisKahanExt.ClosedOperator.ofBounded
        (RealComplexification.complexify T) := by
  apply ForMathlib.DavisKahanExt.ClosedOperator.ext
  · ext z
    simp [domain, complexifySubmodule]
  · intro z
    apply RealComplexification.ext <;> simp [complexify, linearMap, domainRe, domainIm]

/-- A real domain map complexifies to a complex domain map. -/
theorem mapsDomainTo_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := F)}
    {X : F →L[ℝ] E}
    (hX : A.MapsDomainTo B X) :
    (complexify A).MapsDomainTo (complexify B)
      (RealComplexification.complexify X) := by
  intro z
  rw [mem_complexify_domain_iff]
  exact ⟨hX ⟨re (z : Fℂ), (mem_complexify_domain_iff B z).mp z.property |>.1⟩,
    hX ⟨im (z : Fℂ), (mem_complexify_domain_iff B z).mp z.property |>.2⟩⟩

/-- The domain-aware Sylvester equation complexifies coordinatewise. -/
theorem closedSylvesterEquation_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := F)}
    {X C : F →L[ℝ] E}
    (hEq : HasClosedSylvesterEquation A B X C) :
    HasClosedSylvesterEquation (complexify A) (complexify B)
      (RealComplexification.complexify X)
      (RealComplexification.complexify C) := by
  refine {
    mapsTo_domain := mapsDomainTo_complexify hEq.mapsTo_domain
    equation := ?_
  }
  intro z
  apply RealComplexification.ext
  · have h := hEq.equation
        ⟨re (z : Fℂ), (mem_complexify_domain_iff B z).mp z.property |>.1⟩
    simpa [mapsDomainTo_complexify] using h
  · have h := hEq.equation
        ⟨im (z : Fℂ), (mem_complexify_domain_iff B z).mp z.property |>.2⟩
    simpa [mapsDomainTo_complexify] using h

/-- A lower quadratic-form bound is preserved exactly by complexification. -/
theorem semiboundedBelow_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    {c : ℝ} (hA : SemiboundedBelow A c) :
    SemiboundedBelow (complexify A) c := by
  intro z
  have hr := hA (domainRe A z)
  have hi := hA (domainIm A z)
  rw [RealComplexification.norm_sq]
  change c * (‖re (z : Eℂ)‖ ^ 2 + ‖im (z : Eℂ)‖ ^ 2) ≤
    ⟪A.toLinearMap (domainRe A z), re (z : Eℂ)⟫_ℝ +
      ⟪A.toLinearMap (domainIm A z), im (z : Eℂ)⟫_ℝ
  nlinarith

/-- An upper quadratic-form bound is preserved exactly by complexification. -/
theorem semiboundedAbove_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    {c : ℝ} (hA : SemiboundedAbove A c) :
    SemiboundedAbove (complexify A) c := by
  intro z
  have hr := hA (domainRe A z)
  have hi := hA (domainIm A z)
  rw [RealComplexification.norm_sq]
  change
    ⟪A.toLinearMap (domainRe A z), re (z : Eℂ)⟫_ℝ +
      ⟪A.toLinearMap (domainIm A z), im (z : Eℂ)⟫_ℝ ≤
      c * (‖re (z : Eℂ)‖ ^ 2 + ‖im (z : Eℂ)‖ ^ 2)
  nlinarith

/-- Symmetry is preserved by coordinatewise complexification. -/
theorem isSymmetric_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    (hA : A.IsSymmetric) :
    (complexify A).IsSymmetric := by
  intro z w
  apply Complex.ext
  · change
      ⟪A.toLinearMap (domainRe A z), domainRe A w⟫_ℝ +
        ⟪A.toLinearMap (domainIm A z), domainIm A w⟫_ℝ =
      ⟪domainRe A z, A.toLinearMap (domainRe A w)⟫_ℝ +
        ⟪domainIm A z, A.toLinearMap (domainIm A w)⟫_ℝ
    rw [hA, hA]
  · change
      ⟪A.toLinearMap (domainRe A z), domainIm A w⟫_ℝ -
        ⟪A.toLinearMap (domainIm A z), domainRe A w⟫_ℝ =
      ⟪domainRe A z, A.toLinearMap (domainIm A w)⟫_ℝ -
        ⟪domainIm A z, A.toLinearMap (domainRe A w)⟫_ℝ
    rw [hA, hA]

/-- Membership in the adjoint domain separates into the two real adjoint-domain
conditions.  This is the maximality step in the real-to-complex self-adjoint
transport. -/
theorem mem_complexify_adjoint_domain_iff
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (z : Eℂ) :
    z ∈ (complexify A).toLinearPMap.adjoint.domain ↔
      re z ∈ A.toLinearPMap.adjoint.domain ∧
      im z ∈ A.toLinearPMap.adjoint.domain := by
  rw [LinearPMap.mem_adjoint_domain_iff]
  constructor
  · intro hz
    have hofReal : Continuous (ofRealDomain A) := by fun_prop
    have hofImaginary : Continuous (ofImaginaryDomain A) := by fun_prop
    constructor
    · rw [LinearPMap.mem_adjoint_domain_iff]
      have hrestrict : Continuous fun x : A.domain =>
          ⟪z, (complexify A).toLinearPMap (ofRealDomain A x)⟫_ℂ :=
        hz.comp hofReal
      exact (by
        have hre := hrestrict.cl.re
        simpa [complexify_apply_ofReal, inner_apply] using hre)
    · rw [LinearPMap.mem_adjoint_domain_iff]
      have hrestrict : Continuous fun x : A.domain =>
          ⟪z, (complexify A).toLinearPMap (ofImaginaryDomain A x)⟫_ℂ :=
        hz.comp hofImaginary
      exact (by
        have hre := hrestrict.cl.re
        simpa [complexify_apply_ofImaginary, inner_apply] using hre)
  · rintro ⟨hr, hi⟩
    rw [LinearPMap.mem_adjoint_domain_iff] at hr hi
    have hdomainRe : Continuous (domainRe A) := by fun_prop
    have hdomainIm : Continuous (domainIm A) := by fun_prop
    change Continuous fun w : domain A => ⟪z, linearMap A w⟫_ℂ
    apply Complex.continuous_iff.mpr
    constructor
    · simpa [inner_apply, domainRe, domainIm] using
        (hr.comp hdomainRe).add (hi.comp hdomainIm)
    · simpa [inner_apply, domainRe, domainIm] using
        (hr.comp hdomainIm).sub (hi.comp hdomainRe)

/-- Self-adjointness of a real closed operator is preserved by
complexification. -/
theorem isSelfAdjoint_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    (hA : A.IsSelfAdjoint) :
    (complexify A).IsSelfAdjoint := by
  rw [ForMathlib.DavisKahanExt.ClosedOperator.isSelfAdjoint_iff_toLinearPMap_adjoint_eq]
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext z
    rw [mem_complexify_adjoint_domain_iff]
    rw [hA.toLinearPMap_adjoint_eq]
    exact mem_complexify_domain_iff A z
  · intro z hzAdj hzA
    let zAdj : Eℂ := (complexify A).toLinearPMap.adjoint ⟨z, hzAdj⟩
    let zAct : Eℂ := (complexify A).toLinearPMap ⟨z, hzA⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (complexify A).toLinearPMap_dense ⟨z, hzAdj⟩
    have hsymm := isSymmetric_complexify hA.isSymmetric
    have hinner :
        (fun x : Eℂ => ⟪zAdj, x⟫_ℂ) = fun x : Eℂ => ⟪zAct, x⟫_ℂ := by
      apply Continuous.ext_on (complexify A).dense_domain
      · exact continuous_const.inner continuous_id
      · exact continuous_const.inner continuous_id
      · intro x hx
        let xDom : (complexify A).domain := ⟨x, hx⟩
        calc
          ⟪zAdj, x⟫_ℂ = ⟪z, (complexify A).toLinearPMap xDom⟫_ℂ := by
            simpa [zAdj, xDom] using hformal xDom
          _ = ⟪zAct, x⟫_ℂ := by
            simpa [zAct, xDom] using
              (hsymm ⟨z, hzA⟩ xDom).symm
    have hzero : ⟪zAdj - zAct, zAdj - zAct⟫_ℂ = 0 := by
      rw [inner_sub_left, congrFun hinner (zAdj - zAct), sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- A real bounded inverse complexifies to a complex bounded inverse of every
real shift. -/
theorem realResolvent_mem_complexify
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    {lam : ℝ} (hlam : lam ∈ A.realResolventSet) :
    lam ∈ (complexify A).realResolventSet := by
  rcases hlam with ⟨R, hleft, hright⟩
  refine ⟨RealComplexification.complexify R, ?_, ?_⟩
  · intro z
    apply RealComplexification.ext
    · exact hleft (domainRe A z)
    · exact hleft (domainIm A z)
  · intro w
    obtain ⟨hrdom, hr⟩ := hright (re w)
    obtain ⟨hidom, hi⟩ := hright (im w)
    refine ⟨(mem_complexify_domain_iff A _).2 ⟨hrdom, hidom⟩, ?_⟩
    apply RealComplexification.ext
    · exact hr
    · exact hi

/-- A complex resolvent of the coordinatewise complexification descends to a
real resolvent by restricting to the real copy and taking real coordinates. -/
theorem complexify_realResolvent_mem
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    {lam : ℝ} (hlam : lam ∈ (complexify A).realResolventSet) :
    lam ∈ A.realResolventSet := by
  rcases hlam with ⟨R, hleft, hright⟩
  let RrLinear : E →ₗ[ℝ] E :=
    { toFun := fun y => re (R (ofReal y))
      map_add' := fun y z => by simp
      map_smul' := fun r y => by simp }
  let Rr : E →L[ℝ] E :=
    RrLinear.mkContinuous ‖R‖ (fun y => by
      calc
        ‖RrLinear y‖ ≤ ‖R (ofReal y)‖ := norm_re_le _
        _ ≤ ‖R‖ * ‖ofReal y‖ := R.le_opNorm _
        _ = ‖R‖ * ‖y‖ := by rw [ofReal.norm_map])
  refine ⟨Rr, ?_, ?_⟩
  · intro x
    have hx := hleft (ofRealDomain A x)
    exact congrArg re hx
  · intro y
    obtain ⟨hdom, hy⟩ := hright (ofReal y)
    refine ⟨(mem_complexify_domain_iff A (R (ofReal y))).mp hdom |>.1, ?_⟩
    exact congrArg re hy

/-- Real resolvent membership is exactly preserved by closed-operator
complexification. -/
theorem mem_realResolventSet_complexify_iff
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    (lam : ℝ) :
    lam ∈ (complexify A).realResolventSet ↔ lam ∈ A.realResolventSet := by
  exact ⟨complexify_realResolvent_mem A, realResolvent_mem_complexify A⟩

/-- Closed-operator real spectrum is exactly preserved by
coordinatewise complexification. -/
theorem closed_realSpectrum_complexify
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    (complexify A).realSpectrum = A.realSpectrum := by
  ext lam
  change lam ∉ (complexify A).realResolventSet ↔
    lam ∉ A.realResolventSet
  rw [mem_realResolventSet_complexify_iff A lam]

/-- The real spectrum of a real closed operator is the genuine real spectrum
of its complexification. -/
theorem realSpectrum_complexify
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)) :
    A.realSpectrum = Spectra.Resolvent.spectrum (complexify A).toLinearPMap := by
  rw [← closed_realSpectrum_complexify A]
  ext lam
  rfl

/-- Complexification preserves every constructor of the manuscript gap
predicate. -/
theorem unboundedSylvesterGap_complexify
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := F)}
    {δ : ℝ} (hgap : UnboundedSylvesterGap A B δ) :
    UnboundedSylvesterGap (complexify A) (complexify B) δ := by
  cases hgap with
  | intervalExterior hβα hgap =>
      apply UnboundedSylvesterGap.intervalExterior hβα
      rcases hgap with hgap | hgap
      · left
        constructor
        · intro lam hlam
          have hlam' : lam ∈ A.realSpectrum := by
            rwa [closed_realSpectrum_complexify A] at hlam
          exact hgap.1 hlam'
        · intro lam hlam
          have hlam' : lam ∈ B.realSpectrum := by
            rwa [closed_realSpectrum_complexify B] at hlam
          exact hgap.2 hlam'
      · right
        constructor
        · intro lam hlam
          have hlam' : lam ∈ B.realSpectrum := by
            rwa [closed_realSpectrum_complexify B] at hlam
          exact hgap.1 hlam'
        · intro lam hlam
          have hlam' : lam ∈ A.realSpectrum := by
            rwa [closed_realSpectrum_complexify A] at hlam
          exact hgap.2 hlam'
  | leftAboveRightBelow c hA hB =>
      exact UnboundedSylvesterGap.leftAboveRightBelow c
        (semiboundedBelow_complexify hA) (semiboundedAbove_complexify hB)
  | leftBelowRightAbove c hA hB =>
      exact UnboundedSylvesterGap.leftBelowRightAbove c
        (semiboundedAbove_complexify hA) (semiboundedBelow_complexify hB)

end ClosedOperatorComplexification

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
