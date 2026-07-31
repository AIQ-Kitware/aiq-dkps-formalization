import Mathlib

/-!
# Finite-dimensional operator theory: suggested signatures

The roadmap prose (`README.md`) is definitive.  This file is representative,
not exhaustive: it records target shapes for the central objects and headline
milestones of each part, using names that follow the staged `ForTauCeti`
implementation.  Bodies are placeholders; the statements are the content.

## ✅ DELIVERED — every signature below is proved (verified 2026-07-31)

**This topic is complete.**  All 32 declarations in this file exist and are
proved in `ForTauCeti/**`; `README.md` records where each one landed.  Read
this file as a *record* of the target shapes, not as a list of open work.

Re-check with `python3 scripts/check_roadmap_delivered.py --topic
FiniteDimensionalOperators`.

**The `sorry` bodies here are deliberate and must not be "fixed".**  As
`ForTauCetiRoadmap.lean` puts it, the library exists so that a broken
suggested signature is a build failure.  Replacing a body with a proof would
duplicate the library; deleting a signature would remove that guard.  The
only thing that should ever change here is a *statement*, and only to track
a deliberate rename in `ForTauCeti`.

Two hand-rolled passes over this topic both under-counted, in different ways:
one reported `sqrt` missing (it is `_root_.LinearMap.IsPositive.sqrt`); the
other missed `norm_modulus_apply` and `singularValues_adjoint` entirely,
because both are written `@[simp] theorem ...` with the attribute inline and
the pattern was anchored on the declaration keyword.  Use the script.
-/

namespace TauCetiRoadmap.FiniteDimensionalOperators

open Module (finrank)
open scoped InnerProductSpace

universe u v w

/-! ## Part A -- the functional calculus, the positive square root, and the two moduli -/

section FunctionalCalculus

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {n : ℕ}

/-- Apply a real function to the spectrum of a symmetric endomorphism: the
finite `RCLike` counterpart of the continuous functional calculus. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`
noncomputable def selfAdjointFunctionalCalculus
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) •
      (InnerProductSpace.rankOne 𝕜 (hT.eigenvectorBasis rfl i)
        (hT.eigenvectorBasis rfl i)).toLinearMap

/-- The calculus on an arbitrary eigenvector.  Unlike the eigenbasis lemma,
this form is stable on repeated eigenspaces, and it is the key to the
commutant property. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`
theorem selfAdjointFunctionalCalculus_apply_of_apply_eq_smul
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    {x : E} {lam : ℝ} (hx : T x = (lam : 𝕜) • x) :
    selfAdjointFunctionalCalculus hT f x = ((f lam : ℝ) : 𝕜) • x := by
  sorry

/-- The positive square root: the calculus at `Real.sqrt`, by definition. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`
noncomputable def sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  selfAdjointFunctionalCalculus hT.isSymmetric Real.sqrt

/-- Uniqueness: any positive operator squaring to `T` is the square root
(Horn--Johnson 7.2.6). -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.PositiveSqrt`
theorem sqrt_unique {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
    (h : S ∘ₗ S = T) : S = sqrt hT := by
  sorry

/-- Courant--Fischer min-max equality (Horn--Johnson 4.2.6). -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.CourantFischer`
theorem eigenvalues_eq_iSup_iInf_re_inner
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    hT.eigenvalues hn k =
      ⨆ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
        ⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
          RCLike.re ⟪T (x : E), (x : E)⟫_𝕜 := by
  sorry

/-- Weyl's perturbation inequality: a symmetric perturbation moves each sorted
eigenvalue by at most the operator norm. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.CourantFischer`
theorem abs_eigenvalues_sub_le_opNorm
    {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤
      ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  sorry

end FunctionalCalculus

section ComplexModulus

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The rectangular complex modulus `|T| = (T⋆T)^(1/2)`, through Mathlib's
continuous functional calculus.  The second modulus of the roadmap: complex
and rectangular where `sqrt` above is `RCLike` and square. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.OperatorModulus`
noncomputable def modulus (T : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

/-- The modulus reproduces the norms of the original operator pointwise. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.OperatorModulus`
@[simp] theorem norm_modulus_apply (T : E →L[ℂ] F) (x : E) :
    ‖modulus T x‖ = ‖T x‖ := by
  sorry

end ComplexModulus

/-! ## Part B -- polar decomposition and partial isometries -/

section SquarePolar

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Partial isometry, algebraically: `u * star u * u = u`.  Stated in a star
monoid so that one notion serves every carrier in the roadmap. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.PartialIsometry`
def IsPartialIsometry {R : Type*} [Monoid R] [StarMul R] (u : R) : Prop :=
  u * star u * u = u

/-- Operator characterization: a partial isometry is exactly a map that is
norm-preserving on the orthogonal complement of its kernel (Conway VI.3.2). -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.PartialIsometry`
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] E} :
    IsPartialIsometry u ↔ ∀ x ∈ (LinearMap.ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  sorry

/-- The square `RCLike` modulus `|A| = (A⋆A)^(1/2)`, via the spectral square
root (Horn--Johnson 7.3.1). -/
-- DELIVERED: AMBIGUOUS -- `abs` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition`, `DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances`); disambiguate before trusting this
noncomputable def abs (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  sqrt (LinearMap.isPositive_adjoint_comp_self A)

/-- Polar decomposition with a genuine unitary factor, available for every
endomorphism of a finite-dimensional space (Horn--Johnson 7.3.1; the factor
is not unique when `A` is singular). -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition`
theorem exists_polar_decomposition_unitary (A : E →ₗ[𝕜] E) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ abs A := by
  sorry

end SquarePolar

section RectangularPolar

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The initial space of the rectangular polar decomposition: the closure of
the range of the modulus. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry`
noncomputable def polarInitial (M : E →L[ℂ] F) : Submodule ℂ E :=
  (LinearMap.range (modulus M).toLinearMap).topologicalClosure

/-- The polar partial isometry of a bounded rectangular complex operator:
isometric on the initial space, zero on its orthogonal complement.  Open
construction target. -/
-- DELIVERED: AMBIGUOUS -- `polarPartial` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry`, `DavisKahan.Geometry.Polar.PolarIsometryFinal`); disambiguate before trusting this
noncomputable def polarPartial (M : E →L[ℂ] F) : E →L[ℂ] F :=
  sorry

/-- The rectangular polar decomposition `M = W |M|` (Conway VI.3.9). -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry`
theorem polarPartial_comp_modulus (M : E →L[ℂ] F) :
    polarPartial M ∘L modulus M = M := by
  sorry

/-- The initial space is exactly the orthogonal complement of the kernel:
the content of the general decomposition, proved rather than defined. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry`
theorem polarInitial_orthogonal_eq_ker (M : E →L[ℂ] F) :
    (polarInitial M)ᗮ = LinearMap.ker M.toLinearMap := by
  sorry

end RectangularPolar

/-! ## Part C -- singular values and the singular system -/

section SingularSystem

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Adjoint invariance of the singular values.  Both sequences vanish past the
common rank, so no relation between the two dimensions is required; the proof
is the rectangular spectral bridge between `A⋆A` and `AA⋆`. -/
-- DELIVERED: AMBIGUOUS -- `singularValues_adjoint` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues`, `ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace`); disambiguate before trusting this
@[simp] theorem singularValues_adjoint (A : E →ₗ[𝕜] F) :
    A.adjoint.singularValues = A.singularValues := by
  sorry

/-- The right singular basis: the sorted orthonormal eigenbasis of `A⋆A`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Singular.System`
noncomputable def rightSingularBasis (A : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- The left singular vector `σᵢ⁻¹ • A vᵢ`, total through field inversion, so
it is zero at a zero singular value; orthonormality is asserted only on the
subtype of nonzero singular values. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Singular.System`
noncomputable def leftSingularVector (A : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) : F :=
  ((A.singularValues i : ℝ) : 𝕜)⁻¹ • A (rightSingularBasis A i)

/-- The singular relation `A vᵢ = σᵢ • uᵢ`, including the zero case. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Singular.System`
theorem apply_rightSingularBasis_eq_smul_leftSingularVector
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    A (rightSingularBasis A i) =
      ((A.singularValues i : ℝ) : 𝕜) • leftSingularVector A i := by
  sorry

/-- The intrinsic rank-one singular expansion of `A`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Singular.System`
theorem eq_sum_singularValue_rankOne (A : E →ₗ[𝕜] F) :
    A = ∑ i : Fin (finrank 𝕜 E),
      ((A.singularValues i : ℝ) : 𝕜) •
        (InnerProductSpace.rankOne 𝕜
          (leftSingularVector A i) (rightSingularBasis A i)).toLinearMap := by
  sorry

/-- The nonzero left singular family extends to an orthonormal basis of the
codomain -- the statement downstream consumers need, and not automatic for a
rectangular map. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Singular.System`
theorem exists_orthonormalBasis_extending_leftSingularVector
    (A : E →ₗ[𝕜] F) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F,
      Set.range
          (fun i : {j : Fin (finrank 𝕜 E) // A.singularValues j ≠ 0} =>
            leftSingularVector A i.1) ⊆ Set.range b := by
  sorry

/-- The Moore--Penrose inverse, reconstructed from the right singular basis
and the Gram eigenvalues; zero singular values contribute zero through total
field inversion. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.MoorePenroseInverse`
noncomputable def moorePenroseInverse (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    ((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ •
      (InnerProductSpace.rankOne 𝕜 (rightSingularBasis A i)
        (A (rightSingularBasis A i))).toLinearMap

/-- The Penrose characterization: anything satisfying all four identities is
the constructed pseudoinverse (Penrose 1955).  This converse is what earns the
name. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.MoorePenroseInverse`
theorem eq_moorePenroseInverse_of_penrose (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (h1 : A ∘ₗ B ∘ₗ A = A) (h2 : B ∘ₗ A ∘ₗ B = B)
    (h3 : (A ∘ₗ B).IsSymmetric) (h4 : (B ∘ₗ A).IsSymmetric) :
    B = moorePenroseInverse A := by
  sorry

end SingularSystem

/-! ## Part D -- Gram matrices, orthogonal projections, and spectral subspaces -/

section GramRigidity

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type*}

/-- Isometric first isomorphism theorem: two linear maps out of a common
module with equal pullback inner products have canonically isometric ranges,
by `S x ↦ T x`.  No finiteness is assumed and the ambient spaces may differ. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix`
noncomputable def rangeEquivOfInnerEq {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    (S : M →ₗ[𝕜] E) (T : M →ₗ[𝕜] F)
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) :
    LinearMap.range S ≃ₗᵢ[𝕜] LinearMap.range T :=
  sorry

/-- Gram rigidity: families with equal pairwise inner products differ by a
linear isometry equivalence of the ambient space. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix`
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq
    [FiniteDimensional 𝕜 E] {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

end GramRigidity

section ProjectionGap

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The sharp projector-gap identity: the gap between two subspaces is the max
of the two one-sided defects.  An equality, with factor one and no equal-rank
hypothesis. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Projection.Gap`
theorem norm_starProjection_sub_eq_max (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ =
      max ‖(1 - V.starProjection) ∘L U.starProjection‖
          ‖(1 - U.starProjection) ∘L V.starProjection‖ := by
  sorry

/-- A pairwise orthogonal family of vectors spans an orthogonal family of
lines: the vector-level constructor whose upstream counterpart requires unit
vectors. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.OrthogonalSeries`
theorem orthogonalFamily_of_pairwise_inner_eq_zero {ι : Type*} {f : ι → E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) :
    OrthogonalFamily 𝕜 (fun i => (𝕜 ∙ f i : Submodule 𝕜 E))
      fun i => (𝕜 ∙ f i).subtypeₗᵢ := by
  sorry

end ProjectionGap

section SpectralVocabulary

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- A nonzero eigenvector of an operator at a real eigenvalue. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`
def IsEigenvectorAt (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) : Prop :=
  x ≠ 0 ∧ A x = (lam : 𝕜) • x

/-- The finite-dimensional point spectrum of `A` carried by `U`. -/
-- DELIVERED: AMBIGUOUS -- `restrictedSpectrum` is declared in 4 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`, `DavisKahan.Alternative.FiniteDimensional.Sylvester.ContinuousLinearMapBridge`, `DavisKahan.SpectralTheory.AbstractSpectrum`, `DavisKahan.SpectralTheory.Compatibility`); disambiguate before trusting this
def restrictedSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ IsEigenvectorAt A lam x}

/-- Canonical spectral subspace selected by a real set. -/
-- DELIVERED: AMBIGUOUS -- `spectralSubspace` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`, `DavisKahan.Experimental.InfiniteDimensional.SinTheta.General`); disambiguate before trusting this
noncomputable def spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 {x | ∃ lam ∈ Ω, IsEigenvectorAt A lam x}

/-- Two restricted spectra are separated by at least `δ`: the base predicate
of the shared spectral-gap vocabulary. -/
-- DELIVERED: AMBIGUOUS -- `SpectraSeparated` is declared in 4 modules (`ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap`, `DavisKahan.Alternative.FiniteDimensional.Sylvester.ContinuousLinearMapBridge`, `DavisKahan.SpectralTheory.AbstractSpectrum`, `DavisKahan.SpectralTheory.Compatibility`); disambiguate before trusting this
def SpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedSpectrum A U → μ ∈ restrictedSpectrum B V →
    δ ≤ |lam - μ|

end SpectralVocabulary

end TauCetiRoadmap.FiniteDimensionalOperators
