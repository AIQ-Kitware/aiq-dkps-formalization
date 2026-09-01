/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib

/-!
# Davis--Kahan 1970: the four Section 2 theorems

Candidate Challenge.  The namespace is `RotationOfEigenvectors`, after the
paper's title.  Everything below is ordinary Mathlib vocabulary; the only
non-Mathlib names are the source objects defined here, each an ordinary
mathematical definition rather than a re-export of a proof abstraction.

## Deliberately no functional calculus

Davis and Kahan's angle operators are usually built by a continuous functional
calculus.  Nothing here needs one: a unitarily invariant norm sees only the
singular-value sequence, so every angle quantity is either an explicit block of
orthogonal projections or a *sequence* of trigonometric functions of singular
values, measured by the norm's own symmetric gauge.

## The tangents are quantities, not hypothetical witnesses

Davis and Kahan write `‖tan Θ‖`, an actual number.  Quantifying instead over an
operator whose singular values happen to be the tangents says nothing when no
such operator exists.  Sections 2 and 6 evaluate the norm on the tangent
*sequence* directly, and each tangent theorem *concludes* that the tangent has no
pole rather than assuming it away -- which is what the source does.
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

Davis and Kahan quantify over an arbitrary unitarily invariant norm: a symmetric
norming function on singular values, in the dimension-coherent form of a
two-sided unitarily invariant seminorm on `n × n` complex matrices for every `n`,
normalised on a rank-one matrix and unchanged by appending a zero singular value.
Its value on a sequence is the supremum over the sequence's prefixes, and on an
operator is its value on the singular-value sequence. -/

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

/-- **The extended value of a unitarily invariant norm on a scalar sequence**:
the supremum over the sequence's prefixes.

This is the primitive.  Davis and Kahan's norms are symmetric norming functions
of singular-value sequences, so a norm of `tan Θ` is the norm of the sequence
`tan θ₁, tan θ₂, …` and needs no operator carrying those singular values. -/
noncomputable def UINorm.evalSeq (N : UINorm) (s : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal
    ((N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ)
      (fun i => s (i : ℕ)))

/-- The sequence lies in the norm's ideal. -/
def UINorm.SeqFinite (N : UINorm) (s : ℕ → ℝ) : Prop := N.evalSeq s ≠ ⊤

/-- The real-valued norm of a sequence, meaningful on the ideal. -/
noncomputable def UINorm.seqNorm (N : UINorm) (s : ℕ → ℝ) : ℝ :=
  (N.evalSeq s).toReal

section NormEval

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The extended value of a unitarily invariant norm on a bounded operator: its
value on the operator's singular-value sequence.  It is `⊤` exactly off the
norm's ideal. -/
noncomputable def UINorm.eval (N : UINorm) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  N.evalSeq (fun n => singularValue T n)

/-- The operator lies in the norm's ideal. -/
def UINorm.Finite (N : UINorm) (T : E →L[𝕜] F) : Prop := N.eval T ≠ ⊤

/-- The real-valued norm, meaningful on the ideal. -/
noncomputable def UINorm.norm (N : UINorm) (T : E →L[𝕜] F) : ℝ := (N.eval T).toReal

end NormEval

end Norms

/-! ### Subspaces of a complete space

Every subspace named below carries an orthogonal projection, hence is closed,
hence is complete -- which is what lets an operator on it have singular values
and lets a partial map on it have an adjoint. -/

/-- A subspace with an orthogonal projection inside a complete space is
complete. -/
local instance instCompleteSpaceOfHasOrthogonalProjection {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] : CompleteSpace W := by
  have hclosed : IsClosed (W : Set E) := by
    rw [← Submodule.orthogonal_orthogonal W]
    exact Submodule.isClosed_orthogonal _
  exact hclosed.completeSpace_coe

/-! ## 3. The paper's block data

Section 1 fixes a self-adjoint `A`, a bounded self-adjoint perturbation `H`, and
two reducing decompositions: `E₀` spans the trial subspace with block `A₀`, and
`F₀, F₁` span the exact subspaces of `A + H` with complementary block `Λ₁`.  The
residual is `R = (A + H) E₀ − E₀ A₀`.

The source is explicit that neither decomposition is assumed spectral, and that
the trial block `A₀` may be unbounded when the ambient operator is; both are
respected below. -/

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
for the trial subspace, and `R` is the residual `A E₀ − E₀ A₀`.  The trial block
`A₀` is a partial map, so it may be unbounded. -/
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

/-- **The trial data of a subspace**, in the source's own shape `(1.8)`:
a trial operator `A₀` on the subspace, possibly unbounded, and a *bounded*
residual `R` with `A z = A₀ z + R z` on the trial domain.

Davis and Kahan's scope paragraph is explicit that useful unbounded conclusions
require the residual, not the compression, to extend boundedly.  Restricting the
compression to a bounded everywhere-defined operator would lose the Appendix
scope of the `tan Θ` theorem, so the compression here is a partial map. -/
structure TrialBlock (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] where
  /-- The trial block `A₀`, a partial map on the trial subspace. -/
  compression : U →ₗ.[𝕜] U
  /-- `A₀` is self-adjoint. -/
  compression_selfAdjoint : IsSelfAdjoint compression
  /-- The bounded residual `R`. -/
  residual : U →L[𝕜] E
  /-- Trial vectors in the compression's domain lie in the ambient domain. -/
  mem_domain : ∀ z : compression.domain, ((z : U) : E) ∈ A.domain
  /-- and there `A z = A₀ z + R z`, which is `(1.8)`. -/
  action_eq : ∀ z : compression.domain,
    A ⟨((z : U) : E), mem_domain z⟩ =
      ((compression z : U) : E) + residual ((z : U))

/-- **Rayleigh--Ritz trial data**: trial data whose residual is orthogonal to the
trial subspace.

This is the source's `H₀ = 0` in the form `(1.8)` takes when `A₀ = E₀^*(A+H)E₀`,
and it is exactly the extra hypothesis the `tan Θ` theorem imposes and the
`sin Θ` and `sin 2Θ` theorems do not. -/
structure RitzData (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] extends TrialBlock A U where
  /-- The residual is orthogonal to the trial subspace. -/
  residual_orthogonal : ∀ z z' : U, ⟪residual z, ((z' : U) : E)⟫_𝕜 = 0

end BlockData

/-! ## 4. The source separation

Davis and Kahan separate two blocks either by a compact interval whose
enlargement the other block's spectrum avoids, or -- and they say so explicitly --
by half-infinite intervals, in which case both blocks may be unbounded.  Those
are the three constructors below; the ordered two are stated as quadratic-form
bounds, which is how an unbounded semibounded operator is separated. -/

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

Section 1 says in as many words that neither `P` nor `Q` is assumed to be a
spectral projector.  What the theorems assume of a decomposition is that it
*reduces* the operator and that its two blocks are separated; the separation is
what makes the decomposition spectral, and it is a hypothesis rather than a
construction. -/

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

omit [CompleteSpace E] in
/-- The orthogonal complement of a reducing subspace reduces the operator too,
so the separation hypothesis of the ambient theorems can name both blocks. -/
theorem Reduces.orthogonal {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : Reduces A U) : Reduces A Uᗮ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₂, ?_, h₄, ?_⟩
  · intro x
    simpa only [Submodule.orthogonal_orthogonal] using h₁ x
  · intro x hx
    rw [Submodule.orthogonal_orthogonal] at hx ⊢
    exact h₃ x hx

end Reducing

/-! ## 6. The angle quantities

None of these needs a functional calculus.

The *sines* are explicit operators: the paper's own `(I − F₀F₀⋆)E₀` for the
directed single angle, the projector difference `P_V − P_U` for the ambient
single angle, and two explicit projection blocks for the double angles.

The *tangents* are not operators at all here.  A unitarily invariant norm is a
symmetric norming function of a singular-value sequence, so `‖tan Θ‖` is the
norm's value on the sequence `tan θ₁, tan θ₂, …`, and Section 2's `UINorm.seqNorm`
evaluates exactly that. -/

section Angles

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- `sin Θ₀`, the directed sine in coordinates: the part of the trial coordinate
map that misses the exact subspace.  This is the source's `Q^⊥E₀`. -/
noncomputable def directedSine (E₀ : F →L[𝕜] E) (F₀ : K →L[𝕜] E) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀

/-- `sin Θ₀` for a trial *subspace*: the same operator with the inclusion of `U`
as the coordinate map and `V` as the exact subspace, so `Q^⊥E₀ = P_{Vᗮ}|_U`. -/
noncomputable def directedSineBlock (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[𝕜] E :=
  Vᗮ.starProjection ∘L U.subtypeL

/-- `sin Θ`, the ambient sine: the projector difference.  Its singular values are
the sines of the principal angles, each occurring twice. -/
noncomputable def ambientSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  V.starProjection - U.starProjection

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

/-- `sin Θ₀` again, as the directed *ambient* block `P_U P_{Vᗮ}`, whose singular
values are the sines of the principal angles once over.  This is the sine whose
doubled tangent the `tan 2Θ` directed clause bounds. -/
noncomputable def directedSineCorner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.starProjection ∘L Vᗮ.starProjection

/-! ### Tangents of an angle presented by its sine

**The argument of `tanSeq` is a sine, never a residual.**  `tan Θ₀` is a
trigonometric function of the *angle*, and the angle is presented here by an
operator whose singular values are its sines; the residual is the right-hand
side of the inequality and has nothing to do with the left.  Writing
`tanSeq R` for a residual `R` would state a different -- and false -- theorem. -/

/-- The sequence `tan θ₀, tan θ₁, …`, where `sin θₙ` is the `n`-th singular value
of the sine operator `S`. -/
noncomputable def tanSeq {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  Real.tan (Real.arcsin (singularValue S n))

/-- The sequence `|tan 2θ₀|, |tan 2θ₁|, …`.

The absolute value is the source's own choice: a unitarily invariant norm cannot
see the sign, and `|tan 2Θ|` needs no quarter-turn branch hypothesis. -/
noncomputable def absTanTwoSeq {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  |Real.tan (2 * Real.arcsin (singularValue S n))|

/-- **No principal angle of `S` is a right angle**, so every `tan θₙ` is a
genuine tangent rather than the value Lean's field division assigns at a pole.

Davis and Kahan do not assume this; they derive it.  It therefore appears in the
`tan Θ` theorem as a *conclusion*. -/
def TangentDefined {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (S : X →L[𝕜] Y) : Prop :=
  ∀ n, Real.cos (Real.arcsin (singularValue S n)) ≠ 0

/-- **No principal angle of `S` is `π/4`**, so every `|tan 2θₙ|` is a genuine
tangent.  Section 7 of the source derives the nonvanishing of these `cos 2θⱼ`
during the proof rather than assuming it, so it appears below as a conclusion. -/
def DoubleTangentDefined {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (S : X →L[𝕜] Y) : Prop :=
  ∀ n, Real.cos (2 * Real.arcsin (singularValue S n)) ≠ 0

/-- The crossed defect subspaces are isometrically isomorphic.

This is the source's standing condition (3.5), assumed from Section 3 onward;
it is what makes the ambient angle between two subspaces meaningful when they
are not acute. -/
def CrossedDefectsEquivalent (U V : Submodule 𝕜 E) : Prop :=
  Nonempty ((U ⊓ Vᗮ : Submodule 𝕜 E) ≃ₗᵢ[𝕜] (Uᗮ ⊓ V : Submodule 𝕜 E))

end Angles

/-! ## 7. The four theorems of Section 2

Davis and Kahan open with four unnumbered theorems.  Three of them print two
conclusions -- one *directed*, comparing the trial subspace with the exact one
through the residual, and one *ambient*, comparing the two subspaces through the
whole perturbation.

**Each printed clause quantifies its own data and its own hypotheses.**  The
directed clause of `tan Θ` needs the residual to lie in the norm's ideal; the
ambient clause needs the whole perturbation to.  Sharing one membership premise
across both would make each clause carry the other's hypothesis, and in
particular would make the directed clauses weaker than what the source states.
The three two-clause theorems therefore conclude in a record whose fields are the
printed clauses. -/

section Theorems

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The `sin Θ` theorem.**

If the trial block `A₀` and the complementary exact block `Λ₁` are separated by a
gap of width `δ`, then `δ ‖sin Θ₀‖ ≤ ‖R‖` in every unitarily invariant norm.

The ambient operator may be unbounded, the trial block may be unbounded, the
space may have any dimension, the separating interval may be half-infinite, and
the norm is arbitrary.  This is the one Section 2 theorem with a single printed
conclusion. -/
theorem sinTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R := by
  sorry

/-! ### `tan Θ` -/

/-- **The two printed conclusions of the `tan Θ` theorem**, each with its own
data and its own hypotheses.

`A` is the ambient self-adjoint operator, `V` the exact subspace reducing it, and
`α, δ` the ordered separation: the trial block sits at or below `α` and the
unwanted exact block at or above `α + δ`.

* `directed` -- `δ ‖tan Θ₀‖ ≤ ‖R‖`, for every trial subspace with Rayleigh--Ritz
  data, needing only the *residual* in the norm's ideal;
* `ambient` -- `δ ‖tan Θ‖ ≤ ‖H‖`, for a bounded self-adjoint perturbation whose
  trial diagonal block vanishes, needing the *perturbation* in the ideal.

Each clause also concludes that its tangent has no pole, which is derived and not
assumed. -/
structure TanThetaResult (N : UINorm) (A : E →ₗ.[𝕜] E)
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] (α δ : ℝ) : Prop where
  /-- `δ ‖tan Θ₀‖ ≤ ‖R‖`: the directed conclusion, on the residual alone. -/
  directed : ∀ {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
      (D : RitzData A U), SemiboundedAbove D.compression α →
      N.Finite D.residual →
        TangentDefined (directedSineBlock U V) ∧
          N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
          δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual
  /-- `δ ‖tan Θ‖ ≤ ‖H‖`: the ambient conclusion, on the whole perturbation. -/
  ambient : ∀ {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
      (D : RitzData A U), SemiboundedAbove D.compression α →
      ∀ (H : E →L[𝕜] E), IsSelfAdjoint H →
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL →
      CrossedDefectsEquivalent U V →
      N.Finite H →
        TangentDefined (ambientSine U V) ∧
          N.SeqFinite (tanSeq (ambientSine U V)) ∧
          δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H

/-- **The `tan Θ` theorem**, both printed conclusions.

The separation is *ordered* -- the trial block sits at or below `α` and the
unwanted exact block at or above `α + δ` -- and the perturbation has vanishing
trial diagonal block, which is the Rayleigh--Ritz condition `H₀ = 0` carried by
`RitzData` and by `D.residual = P_{Uᗮ} H|_U`.  Then `δ ‖tan Θ₀‖ ≤ ‖R‖` and
`δ ‖tan Θ‖ ≤ ‖H‖`, with the sharp factor one.

The exact subspace `V` is any subspace reducing `A`; the source assumes no
spectral selection, only reduction together with the separation. -/
theorem tanTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ)) :
    TanThetaResult N A V α δ := by
  sorry

/-! ### `sin 2Θ` -/

/-- **The two printed conclusions of the `sin 2Θ` theorem.**

`U` is a subspace reducing `A` whose two blocks are separated by `δ`.

* `directed` -- `δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` for every trial subspace with a residual,
  needing only the residual in the norm's ideal;
* `ambient` -- `δ ‖sin 2Θ‖ ≤ 2 ‖H‖` for every bounded self-adjoint perturbation
  and every subspace reducing the perturbed operator, needing the perturbation
  in the ideal.

The factor two is the paper's, and is sharp.  Unlike `tan Θ`, no Rayleigh--Ritz
condition is imposed, so the trial data is a `TrialBlock` and not a
`RitzData`. -/
structure SinTwoThetaResult (N : UINorm) (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (δ : ℝ) : Prop where
  /-- `δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖`: the directed conclusion, on the residual alone. -/
  directed : ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
      (D : TrialBlock A V), N.Finite D.residual →
        N.Finite (directedDoubleSine U V) ∧
          δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual
  /-- `δ ‖sin 2Θ‖ ≤ 2 ‖H‖`: the ambient conclusion, on the whole perturbation. -/
  ambient : ∀ (H : E →L[𝕜] E), IsSelfAdjoint H →
      ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
      Reduces (addBounded A H) V → N.Finite H →
        N.Finite (ambientDoubleSine U V) ∧
          δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H

/-- **The `sin 2Θ` theorem**, both printed conclusions.

The separating interval may be half-infinite, the ambient operator may be
unbounded, and `U` is any subspace reducing `A` whose two blocks the source
separation puts a gap `δ` between. -/
theorem sinTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ) :
    SinTwoThetaResult N A U δ := by
  sorry

/-! ### `tan 2Θ` -/

/-- **The two printed conclusions of the `tan 2Θ` theorem.**

`U` is a subspace reducing `A`, ordered below `α` with its complement above
`α + δ`, and `H` is a bounded self-adjoint perturbation that is off-diagonal for
that splitting -- the source's `H₀ = H₁ = 0`.

* `directed` -- `δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖`, where the residual is the corner
  `P_{Uᗮ} H P_U`; this clause needs only that *corner* in the norm's ideal;
* `ambient` -- `δ ‖tan 2Θ‖ ≤ 2 ‖H‖`, which needs the whole perturbation in the
  ideal.

Each clause also concludes that its tangent has no pole.  The source is explicit
that no independent hypothesis excluding the poles of `tan 2Θ` is part of the
printed theorem and that Section 7 derives the nonvanishing of the relevant
`cos 2θⱼ`, so the pole exclusion is stated here as a conclusion. -/
structure TanTwoThetaResult (N : UINorm) (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →L[𝕜] E) (δ : ℝ) : Prop where
  /-- `δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖`: the directed conclusion, on the residual corner. -/
  directed : ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
      Reduces (addBounded A H) V →
      N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection) →
        DoubleTangentDefined (directedSineCorner U V) ∧
          N.SeqFinite (absTanTwoSeq (directedSineCorner U V)) ∧
          δ * N.seqNorm (absTanTwoSeq (directedSineCorner U V)) ≤
            2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection)
  /-- `δ ‖tan 2Θ‖ ≤ 2 ‖H‖`: the ambient conclusion, on the whole perturbation. -/
  ambient : ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
      Reduces (addBounded A H) V → N.Finite H →
        DoubleTangentDefined (ambientSine U V) ∧
          N.SeqFinite (absTanTwoSeq (ambientSine U V)) ∧
          δ * N.seqNorm (absTanTwoSeq (ambientSine U V)) ≤ 2 * N.norm H

/-- **The `tan 2Θ` theorem**, both printed conclusions.

The separation is ordered on the two blocks of `A`, and the perturbation is
*off-diagonal* for the splitting -- `H₀ = H₁ = 0`.  Then
`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` and `δ ‖tan 2Θ‖ ≤ 2 ‖H‖`. -/
theorem tanTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : SemiboundedAbove (block A U hU) α)
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) (α + δ)) :
    TanTwoThetaResult N A U H δ := by
  sorry

end Theorems

end RotationOfEigenvectors
