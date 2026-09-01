/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib

/-!
# Davis--Kahan 1970: the four Section 2 theorems

Candidate Challenge.  The namespace is `RotationOfEigenvectors`, after the
paper's title, only so that this file can be compiled inside the development
repository for testing; a standalone entry would use any name it liked.  Everything below is written in ordinary Mathlib
vocabulary; the only non-Mathlib names are the source objects defined here, and
each of them is an ordinary mathematical definition rather than a re-export of a
proof-oriented abstraction.

## Deliberately no functional calculus

Davis and Kahan's angle operators are usually built by a continuous functional
calculus.  Nothing here needs one.  A unitarily invariant norm sees only the
singular-value sequence, so every angle quantity is either an explicit block of
orthogonal projections or an operator *characterised* by its singular values,
which is how the paper itself introduces them.
-/

namespace RotationOfEigenvectors

open scoped InnerProductSpace NNReal ENNReal

universe u v w

/-! ## 1. Singular values -/

section SingularValues

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `n`-th singular value of a bounded operator, zero-based: the
operator-norm distance from `T` to the operators of rank at most `n`.

`a₀ T = ‖T‖`, and for a compact operator this is the usual decreasing sequence
of singular values. -/
noncomputable def singularValue (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // LinearMap.rank (R.1 : E →ₗ[𝕜] F) ≤ (n : Cardinal)},
    ‖T - R.1‖

end SingularValues

/-! ## 2. Unitarily invariant norms

Davis and Kahan quantify over an arbitrary unitarily invariant norm.  Such a
norm is determined by a symmetric norming function on singular values, and the
form used here is the dimension-coherent one: a two-sided unitarily invariant
seminorm on `n × n` complex matrices for every `n`, normalised on a rank-one
matrix, and unchanged by appending a zero singular value.  Its value on an
operator is the supremum over the prefixes of the singular-value sequence. -/

section Norms

/-- The operator with real diagonal `x` in an orthonormal basis. -/
noncomputable def diagOp {n : ℕ} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis (Fin n) ℂ E) (x : Fin n → ℝ) :
    E →ₗ[ℂ] E :=
  ∑ i, ((x i : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap

/-- A two-sided unitarily invariant seminorm on the operators of a
finite-dimensional complex inner product space. -/
structure UISeminorm (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The underlying function on operators. -/
  toFun : (E →ₗ[ℂ] E) → ℝ
  /-- Subadditivity. -/
  add_le : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  /-- Absolute homogeneity. -/
  smul : ∀ (a : ℂ) (A), toFun (a • A) = ‖a‖ * toFun A
  /-- Two-sided unitary invariance -- the defining property. -/
  invariant : ∀ (U V : E ≃ₗᵢ[ℂ] E) (A),
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

/-- The symmetric gauge of a unitarily invariant seminorm: its value on the
diagonal operator with diagonal `x`. -/
noncomputable def UISeminorm.gauge {n : ℕ} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (N : UISeminorm E)
    (b : OrthonormalBasis (Fin n) ℂ E) (x : Fin n → ℝ) : ℝ :=
  N.toFun (diagOp b x)

/-- Append one trailing zero to a finite vector of singular values. -/
def zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 x

/-- **A unitarily invariant norm in Davis and Kahan's sense**: a normalised,
dimension-coherent symmetric norming function. -/
structure UINorm where
  /-- A unitarily invariant seminorm in each finite dimension. -/
  finiteNorm : ∀ n : ℕ, UISeminorm (EuclideanSpace ℂ (Fin n))
  /-- Normalisation on a single unit singular value. -/
  normalized :
    (finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) (fun _ => 1) = 1
  /-- Appending a zero singular value does not change the value. -/
  zero_pad : ∀ {n : ℕ} (x : Fin n → ℝ),
    (finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (zeroPad x) =
      (finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x

section NormEval

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The extended value of a unitarily invariant norm on a bounded operator: the
supremum over prefixes of its singular-value sequence.  It is `⊤` exactly off
the norm's ideal. -/
noncomputable def UINorm.eval (N : UINorm) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal
    ((N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ)
      (fun i => singularValue T (i : ℕ)))

/-- The operator lies in the norm's ideal. -/
def UINorm.Finite (N : UINorm) (T : E →L[𝕜] F) : Prop := N.eval T ≠ ⊤

/-- The real-valued norm, meaningful on the ideal. -/
noncomputable def UINorm.norm (N : UINorm) (T : E →L[𝕜] F) : ℝ := (N.eval T).toReal

end NormEval

end Norms

/-! ## 3. The paper's block data

Section 1 fixes a self-adjoint `A`, a bounded self-adjoint perturbation `H`, and
two reducing decompositions: `E₀` spans the trial subspace with block `A₀`, and
`F₀, F₁` span the exact subspaces of `A + H` with complementary block `Λ₁`.  The
residual is `R = (A + H) E₀ − E₀ A₀`.  All of this is equations between bounded
maps and one domain condition. -/

section BlockData

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- A coordinate map is an isometry onto its range. -/
def IsIsometric (T : E →L[𝕜] F) : Prop := ∀ x, ‖T x‖ = ‖x‖

/-- The trial-coordinate half of the setup: `E₀` is an isometric coordinate map
for the trial subspace, and `R` is the residual `A E₀ − E₀ A₀`. -/
structure IsTrialResidual (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E) (R : F →L[𝕜] E) : Prop where
  /-- The trial coordinate map is isometric. -/
  isometry : IsIsometric E₀
  /-- It carries the trial domain into the ambient domain. -/
  mapsDomain : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain
  /-- `R` is the residual there. -/
  residualEquation : ∀ x : A₀.domain,
    A ⟨E₀ (x : F), mapsDomain x⟩ - E₀ (A₀ x) = R (x : F)

/-- The exact-coordinate half: `F₀` and `F₁` are complementary exhaustive
isometries, and `F₁` intertwines the ambient operator with the complementary
block `Λ₁`. -/
structure IsExactDecomposition (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) : Prop where
  /-- The desired coordinate map is isometric. -/
  desiredIsometry : IsIsometric F₀
  /-- The complementary coordinate map is isometric. -/
  complementIsometry : IsIsometric F₁
  /-- The two ranges are orthogonal. -/
  orthogonal : F₀.adjoint ∘L F₁ = 0
  /-- Together they exhaust the space. -/
  complete : F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint = ContinuousLinearMap.id 𝕜 E
  /-- `F₁` carries the block domain into the ambient domain. -/
  mapsDomain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  /-- and intertwines the two operators there. -/
  intertwines : ∀ y : Λ₁.domain, A ⟨F₁ (y : G), mapsDomain y⟩ = F₁ (Λ₁ y)

end BlockData

/-! ## 4. The source separation

Davis and Kahan separate two spectral blocks either by a compact interval whose
enlargement the other block's spectrum avoids, or -- and they say so explicitly --
by half-infinite intervals, in which case both blocks may be unbounded.  The
three configurations are the three constructors below.  The ordered ones are
stated as quadratic-form bounds, which is how an unbounded semibounded operator
is separated in practice. -/

section Separation

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The real resolvent set: the shifted operator has a bounded two-sided
inverse. -/
def realResolventSet (A : E →ₗ.[𝕜] E) : Set ℝ :=
  {lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A ⟨R y, h⟩ - (lam : 𝕜) • R y = y)}

/-- The real spectrum. -/
def realSpectrum (A : E →ₗ.[𝕜] E) : Set ℝ := (realResolventSet A)ᶜ

/-- The quadratic form of `A` is at least `c` on its domain. -/
def SemiboundedBelow (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜

/-- The quadratic form of `A` is at most `c` on its domain. -/
def SemiboundedAbove (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ c * ‖(x : E)‖ ^ 2

/-- **The source separation of two blocks by a gap of width `δ`.**

`intervalExterior` is the printed interval/exterior condition, symmetric in the
two blocks.  The two ordered constructors are the half-infinite configurations
the source explicitly permits, in which both blocks may have unbounded
spectrum. -/
inductive SylvesterGap (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop where
  | intervalExterior {β α : ℝ} (hβα : β ≤ α)
      (hgap :
        (realSpectrum A ⊆ Set.Icc β α ∧
          realSpectrum B ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (realSpectrum B ⊆ Set.Icc β α ∧
          realSpectrum A ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}))
  | leftAboveRightBelow (c : ℝ)
      (hA : SemiboundedBelow A (c + δ)) (hB : SemiboundedAbove B c)
  | leftBelowRightAbove (c : ℝ)
      (hA : SemiboundedAbove A c) (hB : SemiboundedBelow B (c + δ))

end Separation

/-! ## 5. Reducing subspaces and their blocks

The ambient conclusions are about a subspace that reduces the operator, and the
separation is between the two blocks it splits the operator into. -/

section Reducing

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A subspace reduces a partial map when both orthogonal projections preserve
its domain and both summands are invariant. -/
def Reduces (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Prop :=
  (∀ x : A.domain, U.starProjection (x : E) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : E) ∈ A.domain) ∧
  (∀ x : A.domain, (x : E) ∈ U → A x ∈ U) ∧
  (∀ x : A.domain, (x : E) ∈ Uᗮ → A x ∈ Uᗮ)

/-- The block of `A` on a reducing subspace. -/
noncomputable def block (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (h : Reduces A U) : U →ₗ.[𝕜] U where
  domain :=
    { carrier := {x : U | (x : E) ∈ A.domain}
      zero_mem' := A.domain.zero_mem
      add_mem' := fun hx hy => A.domain.add_mem hx hy
      smul_mem' := fun c _ hx => A.domain.smul_mem c hx }
  toFun :=
    { toFun := fun x => ⟨A ⟨((x : U) : E), x.2⟩, h.2.2.1 _ ((x : U)).2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact congrArg (fun z : A.domain => (A z : E)) (Subtype.ext rfl) |>.trans
          (A.map_add ⟨((x : U) : E), x.2⟩ ⟨((y : U) : E), y.2⟩)
      map_smul' := fun c x => by
        apply Subtype.ext
        exact congrArg (fun z : A.domain => (A z : E)) (Subtype.ext rfl) |>.trans
          (A.map_smul c ⟨((x : U) : E), x.2⟩) }

/-- Adding a bounded operator to a partial map, on the same domain. -/
noncomputable def addBounded (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toFun + V.toLinearMap.domRestrict A.domain

end Reducing

/-! ## 6. The angle quantities

None of these needs a functional calculus.  The directed sine is the paper's own
`(I − F₀F₀⋆)E₀`; the two double-angle sines are explicit projection blocks; and
the tangents are characterised by their singular values, which is how Davis and
Kahan introduce `tan Θ` in the first place. -/

section Angles

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- `sin Θ₀`, the directed sine: the part of the trial coordinate map that
misses the exact subspace. -/
noncomputable def directedSine (E₀ : F →L[𝕜] E) (F₀ : K →L[𝕜] E) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀

/-- `sin 2Θ`, the ambient double-angle sine: the projector difference between
`U` and its mirror image in `V`.

Reflecting `U` in `V` doubles every principal angle, so this is the ambient sine
of the doubled angle. -/
noncomputable def ambientDoubleSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection - U.starProjection

/-- `sin 2Θ₀`, the directed double-angle sine: the overlap of `U` with the mirror
image of its own complement. -/
noncomputable def directedDoubleSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.starProjection ∘L
    (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection

/-- `T` is a tangent of the angle whose sine is `S`: singular value by singular
value, `tan θ` against `sin θ`. -/
def IsTangentOf {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (S : E →L[𝕜] F) (T : E' →L[𝕜] F') : Prop :=
  ∀ n, singularValue T n = Real.tan (Real.arcsin (singularValue S n))

/-- `T` is the branch-free double tangent of the angle whose sine is `S`:
`|tan 2θ|` against `sin θ`.  The absolute value is the source's own choice --
a unitarily invariant norm cannot see the sign, and `|tan 2Θ|` needs no
quarter-turn branch hypothesis. -/
def IsDoubleTangentOf {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (S : E →L[𝕜] F) (T : E' →L[𝕜] F') : Prop :=
  ∀ n, singularValue T n = |Real.tan (2 * Real.arcsin (singularValue S n))|

/-- The crossed defect subspaces are isometrically isomorphic.

This is the source's standing condition (3.5), assumed from Section 3 onward;
it is what makes the ambient angle between two subspaces meaningful when they
are not acute. -/
def CrossedDefectsEquivalent (U V : Submodule 𝕜 E) : Prop :=
  Nonempty ((U ⊓ Vᗮ : Submodule 𝕜 E) ≃ₗᵢ[𝕜] (Uᗮ ⊓ V : Submodule 𝕜 E))

/-- `sin Θ`, the ambient sine: the projector difference. -/
noncomputable def ambientSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  V.starProjection - U.starProjection

end Angles

/-! ### The complementary block

The orthogonal complement of a reducing subspace reduces the operator too, so
the separation hypothesis of the ambient theorems can name both blocks. -/

section ReducingComplement

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem Reduces.orthogonal {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : Reduces A U) : Reduces A Uᗮ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₂, ?_, h₄, ?_⟩
  · intro x
    simpa only [Submodule.orthogonal_orthogonal] using h₁ x
  · intro x hx
    rw [Submodule.orthogonal_orthogonal] at hx ⊢
    exact h₃ x hx

end ReducingComplement

/-! ## 7. The four theorems of Section 2

Davis and Kahan open with four unnumbered theorems.  Three of them print two
conclusions -- one *directed*, comparing the trial subspace with the exact one
through the residual, and one *ambient*, comparing the two subspaces through the
whole perturbation.  Each theorem below carries all of its printed conclusions,
with each clause quantified over its own data. -/

section Theorems

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- A subspace with an orthogonal projection inside a complete space is complete,
which is what lets a coordinate operator on it be measured by a norm. -/
local instance instCompleteSpaceOrthogonallyComplemented
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] : CompleteSpace W := by
  have hclosed : IsClosed (W : Set E) := by
    rw [← Submodule.orthogonal_orthogonal W]
    exact Submodule.isClosed_orthogonal _
  exact hclosed.completeSpace_coe

/-- **The `sin Θ` theorem.**

If the trial block `A₀` and the complementary exact block `Λ₁` are separated by a
gap of width `δ`, then `δ ‖sin Θ₀‖ ≤ ‖R‖` in every unitarily invariant norm.

The ambient operator may be unbounded, the space may have any dimension, the
separating interval may be half-infinite, and the norm is arbitrary. -/
theorem sinTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R := by
  sorry

/-- **The `sin 2Θ` theorem**, both printed conclusions.

Under one separation of the two blocks of `A`:

* directed -- `δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` for every trial subspace inside the domain,
  with `R` its residual;
* ambient -- `δ ‖sin 2Θ‖ ≤ 2 ‖H‖` for every bounded self-adjoint perturbation and
  every subspace reducing the perturbed operator.

The factor two is the paper's, and is sharp. -/
theorem sinTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ) :
    (∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
        {M : V →L[𝕜] V} {R : V →L[𝕜] E}
        (hVdom : ∀ v : V, ((v : V) : E) ∈ A.domain),
        (∀ v : V, A ⟨((v : V) : E), hVdom v⟩ = R v + ((M v : V) : E)) →
        N.Finite R →
          N.Finite (directedDoubleSine U V) ∧
            δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm R) ∧
      (∀ (H : E →L[𝕜] E), IsSelfAdjoint H →
        ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
        Reduces (addBounded A H) V → N.Finite H →
          N.Finite (ambientDoubleSine U V) ∧
            δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H) := by
  sorry

/-- **The `tan Θ` theorem**, both printed conclusions.

The separation is *ordered* -- the trial block sits at or below `α` and the
unwanted exact block at or above `α + δ` -- and the perturbation has vanishing
trial diagonal block, which is the Rayleigh--Ritz condition `H₀ = 0`.  Then
`δ ‖tan Θ₀‖ ≤ ‖R‖` and `δ ‖tan Θ‖ ≤ ‖H‖`, with the sharp factor one.

The tangents are named by their singular values, which is how the source
introduces them: `tan Θ₀` is any operator whose singular values are the tangents
of the principal angles. -/
theorem tanTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : ∀ u : U, ((u : U) : E) ∈ A.domain)
    (M : U →L[𝕜] U) (R : U →L[𝕜] E)
    (hres : ∀ u : U, A ⟨((u : U) : E), hU u⟩ = R u + ((M u : U) : E))
    (hVred : Reduces A Vᗮ)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    {α δ : ℝ} (hδ : 0 < δ)
    (htrial : ∀ u : U, RCLike.re ⟪M u, u⟫_𝕜 ≤ α * ‖(u : E)‖ ^ 2)
    (hunwanted : ∀ y : A.domain, ((y : E)) ∈ Vᗮ →
      (α + δ) * ‖(y : E)‖ ^ 2 ≤ RCLike.re ⟪A y, (y : E)⟫_𝕜)
    (hritz : R = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hcross : CrossedDefectsEquivalent U V)
    (hHmem : N.Finite H) :
    (∀ (T : U →L[𝕜] E), IsTangentOf R T → N.Finite R →
        N.Finite T ∧ δ * N.norm T ≤ N.norm R) ∧
      (∀ (T : E →L[𝕜] E), IsTangentOf (ambientSine U V) T →
        N.Finite T ∧ δ * N.norm T ≤ N.norm H) := by
  sorry

/-- **The `tan 2Θ` theorem**, both printed conclusions.

The separation is ordered on the two blocks of `A`, and the perturbation is
*off-diagonal* for the splitting -- `H₀ = H₁ = 0`.  Then
`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` and `δ ‖tan 2Θ‖ ≤ 2 ‖H‖`.

The source excludes the poles of `tan 2Θ` from its hypotheses rather than
assuming them away, and the branch-free `|tan 2Θ|` carries the same value in
every unitarily invariant norm. -/
theorem tanTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, ((x : E)) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, ((x : E)) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    (hHmem : N.Finite H)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
    (∀ (T : E →L[𝕜] E),
        IsDoubleTangentOf (U.starProjection ∘L Vᗮ.starProjection) T →
        N.Finite T ∧
          δ * N.norm T ≤ 2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection)) ∧
      (∀ (T : E →L[𝕜] E), IsDoubleTangentOf (ambientSine U V) T →
        N.Finite T ∧ δ * N.norm T ≤ 2 * N.norm H) := by
  sorry

end Theorems

end RotationOfEigenvectors
