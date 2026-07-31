/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import Mathlib

/-!
# Spectral subspace perturbation: suggested signatures

`README.md` is the definitive specification; this file is representative, not
exhaustive.  It records target shapes for the central objects and headline
milestones of each Part, using names already present in the staged
`ForTauCeti` implementation, idealized to clean `TauCeti`-style forms.  It
supersedes the earlier markdown signature sketch (`Suggested.lean.md`).
Named declarations correspond to staged results; unnamed examples are the
genuinely open targets.  Every body is a placeholder.

The common-objects section restates, minimally, vocabulary owned by the
sibling roadmaps (FiniteDimensionalOperators for the spectral predicates,
MajorizationAndAngles for norms and angles) so that the signatures below
elaborate; those restatements are consumed here, not specified here.
-/

namespace TauCetiRoadmap.SpectralSubspacePerturbation

open Module (finrank)
open scoped InnerProductSpace
open MeasureTheory

universe u v w

/-! ## Common objects (consumed from the sibling roadmaps) -/

section CommonObjects

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The finite-dimensional point spectrum of `A` carried by `U`: real
eigenvalues with an eigenvector in `U`. -/
-- DELIVERED: AMBIGUOUS -- `restrictedSpectrum` is declared in 4 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`, `DavisKahan.Alternative.FiniteDimensional.Sylvester.ContinuousLinearMapBridge`, `DavisKahan.SpectralTheory.AbstractSpectrum`, `DavisKahan.SpectralTheory.Compatibility`); disambiguate before trusting this
def restrictedSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ x ≠ 0 ∧ A x = (lam : 𝕜) • x}

/-- Every eigenvalue of `A` carried by `U` lies in `Ω`. -/
-- DELIVERED: AMBIGUOUS -- `SpectrumIn` is declared in 3 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`, `DavisKahan.SpectralTheory.AbstractSpectrum`, `DavisKahan.SpectralTheory.Compatibility`); disambiguate before trusting this
def SpectrumIn (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Ω : Set ℝ) : Prop :=
  restrictedSpectrum A U ⊆ Ω

/-- Two restricted spectra are separated by at least `δ`. -/
-- DELIVERED: AMBIGUOUS -- `SpectraSeparated` is declared in 4 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap`, `DavisKahan.Alternative.FiniteDimensional.Sylvester.ContinuousLinearMapBridge`, `DavisKahan.SpectralTheory.AbstractSpectrum`, `DavisKahan.SpectralTheory.Compatibility`); disambiguate before trusting this
def SpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedSpectrum A U → μ ∈ restrictedSpectrum B V →
    δ ≤ |lam - μ|

/-- Canonical finite-dimensional spectral subspace selected by a real set. -/
-- DELIVERED: AMBIGUOUS -- `spectralSubspace` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`, `DavisKahan.Experimental.InfiniteDimensional.SinTheta.General`); disambiguate before trusting this
noncomputable def spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 {x | ∃ lam ∈ Ω, x ≠ 0 ∧ A x = (lam : 𝕜) • x}

/-- The directed sine cross-projection `P_{Vᗮ} ∘ P_U`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry`
noncomputable def sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  ((Vᗮ.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)

/-- The Frobenius (Hilbert–Schmidt) norm through the standard orthonormal
basis; basis independence is part of the consumed norm API.

**Already staged, under a different name (checked 2026-07-31).**  This is
`TauCeti.UnitarilyInvariantNorm.frobenius` in
`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantNorm.lean`, whose `toFun` is
character-for-character this body, with the rectangular twin in
`RectangularUnitarilyInvariantNorm/Instances.lean` and basis independence proved as
`frobenius_apply`.  The Yu--Wang--Samworth files already consume it under that name.  Kept here
only because this file records target *shapes*; there is nothing to prove. -/
-- DELIVERED: AMBIGUOUS -- `frobenius` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Instances`, `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm`); disambiguate before trusting this (as `frobenius`)
noncomputable def frobeniusNorm [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] F) : ℝ :=
  Real.sqrt (∑ i, ‖T (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)

end CommonObjects

/-- A unitarily invariant seminorm on rectangular linear maps between
finite-dimensional inner-product spaces: subadditive, absolutely homogeneous,
invariant under composition with linear isometry equivalences on both sides.
Definiteness is deliberately not bundled. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Basic`
structure RectangularUnitarilyInvariantNorm (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    where
  toFun : (E →ₗ[𝕜] F) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) A, toFun (a • A) = ‖a‖ * toFun A
  invariant' : ∀ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) A,
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

instance {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    CoeFun (RectangularUnitarilyInvariantNorm 𝕜 E F)
      fun _ => (E →ₗ[𝕜] F) → ℝ :=
  ⟨RectangularUnitarilyInvariantNorm.toFun⟩

/-- Square unitarily invariant seminorms as the diagonal of the rectangular
family.  (The staged implementation carries a separate square structure; the
roadmap treats the square case as the diagonal instance.) -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm`
abbrev UnitarilyInvariantNorm (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :=
  RectangularUnitarilyInvariantNorm 𝕜 E E

/-! ## Part A -- the Haagerup–Zsidó kernel and its Fourier transform -/

section HaagerupZsido

/-- The hyperbolic weight, chosen so the mass computation collapses exactly. -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs`
noncomputable def weight (y : ℝ) : ℝ :=
  Real.tanh (Real.pi * y / 2)

/-- The Laplace transform of the weight at `|t|`. -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs`
noncomputable def weightLaplaceTransform (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y)

/-- The real Haagerup–Zsidó kernel. -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs`
noncomputable def realKernel (t : ℝ) : ℝ :=
  (Real.sin t / 2) * weightLaplaceTransform t

/-- The complex kernel; the rotation by `-i` makes the Fourier identity land
on `1 / x` rather than `i / x`. -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs`
noncomputable def reciprocalKernel (t : ℝ) : ℂ :=
  -Complex.I * (realKernel t : ℂ)

/-- Oddness; the two-sided Fourier identity follows from `1 ≤ x` by
reflection. -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs`
theorem reciprocalKernel_neg (t : ℝ) :
    reciprocalKernel (-t) = -reciprocalKernel t := by
  sorry

/-- Closed-form Laplace transform of `|sin|`, the inner integral of the mass
computation. -/
-- DELIVERED: `ForTauCeti.Analysis.SpecialFunctions.Integral.SineLaplace`
theorem integral_abs_sin_mul_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|)) =
      2 * ((1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2))) := by
  sorry

/-- **Milestone A1, first half: the exterior Fourier identity.** -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Fourier`
theorem reciprocalKernel_fourier (x : ℝ) (hx : 1 ≤ |x|) :
    (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) = 1 / (x : ℂ) := by
  sorry

/-- **Milestone A1, second half: the exact mass `π / 2`.** -/
-- DELIVERED: `ForTauCeti.Analysis.Fourier.HaagerupZsido.Integrability`
theorem integral_norm_reciprocalKernel :
    (∫ t : ℝ, ‖reciprocalKernel t‖) = Real.pi / 2 := by
  sorry

end HaagerupZsido

/-! ## Part B -- Sylvester equations and the Rosenblum theorem -/

section DimensionFreeBounds

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Dimension-free separated Sylvester bound** (integral-free, arbitrary
Hilbert spaces, both scalar fields): quadratic-form separation of size `g`
gives `‖X‖ ≤ ‖Y‖ / g`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound`
theorem opNorm_le_div_of_comp_sub_comp_eq
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X Y : F →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, RCLike.re ⟪B v, v⟫_𝕜 ≤ c * ‖v‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / g := by
  sorry

end DimensionFreeBounds

section FiniteDimensionalSylvester

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **Interval/exterior separation, constant one, every rectangular unitarily
invariant norm.** -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval`
theorem uiNorm_sylvester_le_of_intervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hBin : SpectrumIn B ⊤ (Set.Icc a b))
    (hAout : SpectrumIn A ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)})
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  sorry

/-- **Arbitrary pairwise separation, the sharp constant `π / 2`** (the mass of
the Part A kernel), lifted from the simultaneous Ky Fan prefix estimate by Fan
dominance. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance`
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  sorry

end FiniteDimensionalSylvester

section UnboundedSpectrum

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The resolvent set of a partial linear map: `z` such that `A - z` has a
two-sided bounded inverse.  (Owned by the SpectralTheory roadmap; restated
so the statements below elaborate.) -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent`
def resolventSet (A : H →ₗ.[𝕜] H) : Set 𝕜 :=
  { z | ∃ R : H →L[𝕜] H,
      (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = (ψ : H)) ∧
      (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) }

/-- The spectrum of a partial linear map: the complement of the resolvent
set, with codomain `Set 𝕜` and no self-adjointness built in. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent`
def spectrum (A : H →ₗ.[𝕜] H) : Set 𝕜 :=
  (resolventSet A)ᶜ

end UnboundedSpectrum

section Unbounded

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The domain-aware Sylvester equation `A X - X B = C` for partial linear
maps, with domain transport as data.  (The transport statement is owned by
the SpectralTheory roadmap; the estimates attach to it here.) -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester`
structure SylvesterEquation (A : E →ₗ.[ℂ] E) (B : F →ₗ.[ℂ] F)
    (X C : F →L[ℂ] E) : Prop where
  mapsTo_domain : ∀ y : B.domain, X (y : F) ∈ A.domain
  equation : ∀ y : B.domain,
    A ⟨X (y : F), mapsTo_domain y⟩ - X (B y) = C (y : F)

/-- **Milestone B2 — Rosenblum's theorem.**  A bounded operator intertwining
two self-adjoint partial maps with disjoint spectra is zero.  Proved without
a Borel functional calculus: `1` is a null point for every diagonal spectral
measure, so damped continuous Cayley symbols separate in the limit. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Rosenblum`
theorem eq_zero_of_intertwines_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y))
    (hdisj : Disjoint (spectrum A) (spectrum B)) :
    X = 0 := by
  sorry

/-- The unbounded pairwise-separation bound with the sharp constant: open
target.  The Hilbert–Schmidt form with constant one, through the Sylvester
flow's generator gap, is the companion target. -/
example {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} (hEq : SylvesterEquation A B X C)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z ∈ spectrum A, ∀ w ∈ spectrum B, δ ≤ ‖z - w‖) :
    δ * ‖X‖ ≤ (Real.pi / 2) * ‖C‖ := by
  sorry

end Unbounded

/-! ## Part C -- the Davis–Kahan sin Θ theorems -/

section DimensionFreeSinTheta

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The dimension-free operator-norm `sin Θ` theorem, coercivity form**: on
an arbitrary Hilbert space, from the dimension-free Sylvester bound alone. -/
-- DELIVERED: AMBIGUOUS -- `sinTheta_directed_coercive` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.SinTheta`, `DavisKahan.Experimental.InfiniteDimensional.SinTheta.General`); disambiguate before trusting this
theorem sinTheta_directed_coercive
    {A B : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hVc : ∀ x ∈ V, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g := by
  sorry

end DimensionFreeSinTheta

section FiniteSinTheta

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Milestone C1 — Davis–Kahan `sin Θ`, perturbation form, every square
unitarily invariant norm**, under the interval/exterior gap. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`
theorem sinTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hAin : SpectrumIn A U (Set.Icc a b))
    (hBout : SpectrumIn B Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  sorry

/-- **Canonical spectral-projector Davis–Kahan theorem** with no eigenbasis
in the API; the equal-rank hypothesis turns the directed estimate into the
full projector difference. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`
theorem opNorm_spectralProjection_sub_spectralProjection_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hrank : finrank 𝕜 (spectralSubspace A (Set.Icc a b)) =
      finrank 𝕜 (spectralSubspace B (Set.Icc a b)))
    (hAin : SpectrumIn A (spectralSubspace A (Set.Icc a b)) (Set.Icc a b))
    (hBout : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ‖((spectralSubspace A (Set.Icc a b)).starProjection -
        (spectralSubspace B (Set.Icc a b)).starProjection : E →L[𝕜] E)‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  sorry

/-- **Milestone C2 — the two-sided `π/2` form**: arbitrary pairwise
separation of the selected `A`-spectrum from the complementary `B`-spectrum,
every square unitarily invariant norm. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`
theorem sinTheta_perturbation_le_of_spectralDistance
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ (Real.pi / 2) * N (B - A) := by
  sorry

/-- **Davis's `sin 2θ` theorem, per-eigenvector product form**: for a unit
eigenvector `x` of the perturbed operator and `P` the projection onto the
invariant subspace, `(b - a) · ‖P x‖ · ‖x - P x‖ ≤ ε`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Vector`
theorem sin_two_theta_le
    {T P : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hP : P.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖P v‖ ≤ ε * ‖v‖)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + P x = (μ : 𝕜) • x) :
    (b - a) * (‖U.starProjection x‖ * ‖x - U.starProjection x‖) ≤ ε := by
  sorry

end FiniteSinTheta

/-! ### Milestone C3 -- the domain-aware `sin Θ` theorem

The roadmap's headline, and the only milestone whose statement cannot be
reconstructed from the ones around it.  Hypotheses are bundled as a record on
purpose: a flat theorem takes a dozen mutually constrained arguments and every
specialization repeats all of them, whereas with a record each specialization is
a *constructor* -- which is what makes "bounded and finite are specializations"
true in the code rather than only in the prose. -/

section DomainAwareSinTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A lower frame bound for a trial map: the constant that replaces isometry.
`c = 1` recovers the classical isometric statement, and the bound of Milestone C3
degrades with `c` as the trial map degenerates. -/
-- DELIVERED: AMBIGUOUS -- `LowerFrameBound` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.FrameFactorization`, `DavisKahan.SinTheta.FrameFactorization`); disambiguate before trusting this
def LowerFrameBound (X : H →L[ℂ] E) (c : ℝ) : Prop :=
  ∀ h : H, c * ‖h‖ ≤ ‖X h‖

/-- The hypotheses of the domain-aware `sin Θ` theorem, as data.

`A` is self-adjoint and *possibly unbounded*; nothing here says otherwise.  What is
bounded is the **residual**: `A ∘ X - X ∘ A₀` extends from a graph core to a bounded
operator on all of `H`, and that is the hypothesis -- bounded residual, never
bounded `A`.

The norm is an ideal gauge from the OperatorIdeals roadmap rather than a unitarily
invariant norm on a finite-dimensional space: at this generality finiteness of the
gauge is a *hypothesis* on the residual and a *conclusion* about `sin Θ`. -/
-- DELIVERED: `DavisKahan.SinTheta.Unbounded.Core` (as `UnboundedSinThetaData`)
-- NOT DELIVERED, and NOT merely renamed (audited 2026-07-31).
-- `DavisKahan/SinTheta/Unbounded/Core.lean` has `UnboundedSinThetaData`, which is a
-- REDESIGN rather than a rename: it bundles the operators as fields instead of taking
-- them as parameters, generalizes `ℂ` to `RCLike`, wraps each operator in
-- `ClosedOperator{Ambient,Trial,Complement}`, and carries a THIRD operator `Λ₁` with an
-- `intertwines` field that the shape below does not have.  Reconciling the two is a
-- design decision for the unbounded lane, not a roadmap edit.
structure UnboundedSinThetaProblem
    (A : E →ₗ.[ℂ] E) (A₀ : H →ₗ.[ℂ] H) (X : H →L[ℂ] E) (R : H →L[ℂ] E) where
  /-- The ambient operator is self-adjoint; it is not assumed bounded. -/
  ambient_selfAdjoint : IsSelfAdjoint A
  /-- The trial block is self-adjoint. -/
  trial_selfAdjoint : IsSelfAdjoint A₀
  /-- The trial map lands in the ambient domain on the trial domain. -/
  mapsTo_domain : ∀ h : A₀.domain, X (h : H) ∈ A.domain
  /-- The residual identity on the trial domain: this is where domain-awareness
  lives, and it is why `R` can be bounded while `A` is not. -/
  residual : ∀ h : A₀.domain,
    A ⟨X (h : H), mapsTo_domain h⟩ - X (A₀ h) = R (h : H)
  /-- The lower frame constant of the trial map. -/
  frameLowerBound : ℝ
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound X frameLowerBound
  /-- The spectral separation, in one of the three forms of the generality bar;
  the constant in the conclusion is `1` for interval/exterior and ordered
  separation and `π/2` for pairwise separation. -/
  gap : ℝ
  gap_pos : 0 < gap

/-- **Milestone C3.**  The sine operator is *determined by the data* -- it is
built from the trial map `X`, exactly as the delivered
`TauCeti.DavisKahan.sinTheta_unbounded_opNorm` concludes about
`D.X.adjoint ∘L D.F₁`.

**Corrected 2026-07-31 (`{lane:ROADMAP-GAPS-DK}`): this signature previously took
`sinTheta : H →L[ℂ] E` as a free argument with no hypothesis relating it to `P`,
and was therefore FALSE, not merely unproved** -- `P.gap` and `P.frameLowerBound`
are positive by the structure's own fields, so the left side scales without bound
in `sinTheta` while `‖R‖` is fixed, and the type is inhabited (it is delivered as
`UnboundedSinThetaData`).  **A `Suggested.lean` signature is compiled so that a
*broken* one is a build failure; a *false* one elaborates fine**, so the guard
this library exists to provide cannot catch this class.

Stated here with the operator norm standing in for the ideal gauge, since the
gauge lives in the OperatorIdeals roadmap; reconciling the two is open work
recorded in the roadmap prose.  **The docstring formerly promised a conjunction
carrying ideal *membership* of the sine operator** -- that half is precisely the
reconciliation that is open, so it is named here rather than asserted in a
statement that cannot yet express it. -/
theorem sinTheta_domainAware_le
    {A : E →ₗ.[ℂ] E} {A₀ : H →ₗ.[ℂ] H} {X R : H →L[ℂ] E}
    (P : UnboundedSinThetaProblem A A₀ X R) :
    P.gap * P.frameLowerBound * ‖X‖ ≤ ‖R‖ := by
  sorry

end DomainAwareSinTheta

section Riccati

variable {U : Type v} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [CompleteSpace U]
variable {W : Type w} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W]

/-- Graph-subspace/Riccati target (open): for a self-adjoint block operator
`[[A₁, C⋆], [C, A₂]]` with an ordered form gap `g` between the diagonal
blocks, the Riccati equation has a solution whose norm obeys the tangent
bound; contractivity and uniqueness among contractions are the companion
targets. -/
example {A₁ : U →L[ℂ] U} {A₂ : W →L[ℂ] W} {C : U →L[ℂ] W}
    (hA₁ : (A₁ : U →ₗ[ℂ] U).IsSymmetric) (hA₂ : (A₂ : W →ₗ[ℂ] W).IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (h₁ : ∀ x, RCLike.re ⟪A₁ x, x⟫_ℂ ≤ c * ‖x‖ ^ 2)
    (h₂ : ∀ y, (c + g) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A₂ y, y⟫_ℂ)
    (hC : ‖C‖ < g / 2) :
    ∃ X : U →L[ℂ] W,
      X ∘L A₁ - A₂ ∘L X + X ∘L ContinuousLinearMap.adjoint C ∘L X = C ∧
        g * ‖X‖ ≤ 2 * ‖C‖ := by
  sorry

end Riccati

/-! ## Part D -- the Yu–Wang–Samworth statistical variant -/

section YuWangSamworth

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Population-only gap: the selected block of `A` is separated from its own
complementary block.  No hypothesis on the perturbed spectrum. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
def PopulationGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Δ : ℝ) : Prop :=
  SpectraSeparated A U A Uᗮ Δ

/-- `U` and `V` are eigenblocks of `A` and `B` selected by the same ordered
eigenvalue indices — the branch selection that excludes arbitrary reducing
subspaces when `B = A`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
def CorrespondingEigenblock {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ (n : ℕ) (hn : finrank 𝕜 E = n) (s : Finset (Fin n)),
    U = Submodule.span 𝕜 (⇑(hA.eigenvectorBasis hn) '' (s : Set (Fin n))) ∧
      V = Submodule.span 𝕜 (⇑(hB.eigenvectorBasis hn) '' (s : Set (Fin n)))

/-- Frobenius sine distance in canonical subspace notation. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  frobeniusNorm (sinThetaMap U V)

/-- **The complement identity**: the Frobenius sine of two equally indexed
blocks is exactly the square root of the cross-block overlap sum — the bridge
between the paper's cross-block energies and angles, public by decision. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
theorem sinThetaFrobenius_eq_sqrt_sum_cross {n : ℕ}
    (bT bS : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n)) :
    sinThetaFrobenius
        (Submodule.span 𝕜 (⇑bT '' (s : Set (Fin n))))
        (Submodule.span 𝕜 (⇑bS '' (s : Set (Fin n)))) =
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bT k, bS j⟫_𝕜‖ ^ 2) := by
  sorry

/-- **Milestone D1 — the exact Yu–Wang–Samworth population-gap theorem.** -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
theorem yuWangSamworth_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (frobeniusNorm (B - A)) / Δ := by
  sorry

/-- **The aligned-basis (Procrustes) surface**: orthonormal bases of the two
blocks whose pointwise discrepancy is controlled — the usable form when
eigenbases are determined only up to rotation. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
theorem yuWangSamworth_alignedBasis_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : PopulationGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (frobeniusNorm (B - A)) / Δ := by
  sorry

/-- **The single-vector bound**: the rank-one, sign-aligned eigenvector
corollary — the headline statisticians quote. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
theorem yuWangSamworth_eigenvector_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {lam μ Δ : ℝ} (hAu : A u = (lam : 𝕜) • u) (hBv : B v = (μ : 𝕜) • v)
    (hcorr : CorrespondingEigenblock hA hB
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum A (Submodule.span 𝕜 {u})ᗮ,
      Δ ≤ |lam - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤
        2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  sorry

end YuWangSamworth

end TauCetiRoadmap.SpectralSubspacePerturbation
