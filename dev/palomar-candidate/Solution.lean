/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Challenge
import DavisKahan.All

/-!
# Solution: the four Section 2 theorems

The Challenge states Davis and Kahan's four theorems in ordinary mathematical
vocabulary.  This module proves them from the development, and the first job is
to show that the Challenge's vocabulary *is* the development's -- not merely
analogous to it.
-/

namespace RotationOfEigenvectors

open TauCeti
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u v

/-- A subspace with an orthogonal projection inside a complete space is
complete; the Challenge's own `local instance` does not cross the import. -/
local instance instCompleteSpaceOfHasOrthogonalProjectionSolution {𝕜 : Type u}
    [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] :
    CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-! ## 1. The norm vocabulary is the development's -/

section NormBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's singular values are the development's approximation
numbers, definitionally. -/
theorem singularValue_eq_approximationNumber (T : E →L[𝕜] F) (n : ℕ) :
    singularValue T n = T.approximationNumber n := rfl

/-- A Challenge unitarily invariant seminorm is one of the development's. -/
def UISeminorm.toTauCeti {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G) :
    TauCeti.UnitarilyInvariantSeminorm ℂ G where
  toFun := N.toFun
  add_le' := N.add_le
  smul' := N.smul
  invariant' := N.invariant

/-- The Challenge's diagonal operator is the development's. -/
theorem diagOp_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    diagOp b x = TauCeti.diagOp b x := rfl

/-- Hence so is its symmetric gauge. -/
theorem UISeminorm.gauge_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G)
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    N.gauge b x = N.toTauCeti.gauge b x := rfl

/-- **A Challenge unitarily invariant norm is a source unitarily invariant norm.**

Field for field: the finite seminorms, the normalisation and the zero-padding
axiom transfer with no adjustment, because the two definitions are the same
definition. -/
def UINorm.toPaper (N : UINorm) : PaperUnitaryInvariantNorm where
  finiteNorm n := (N.finiteNorm n).toTauCeti
  normalized := N.normalized
  zero_pad := N.zero_pad

/-- The two norms take the same value on every operator.

The Challenge evaluates its norm on the *sequence* of singular values and the
development on the operator, so this equation is also the statement that the
sequence-level and operator-level readings agree. -/
theorem UINorm.eval_eq (N : UINorm) (T : E →L[𝕜] F) :
    N.eval T = N.toPaper.extendedGauge T := rfl

/-- The sequence norm of an operator's singular values is the operator norm --
which is what makes `UINorm.seqNorm` the right home for `‖tan Θ‖`. -/
theorem UINorm.evalSeq_singularValue (N : UINorm) (T : E →L[𝕜] F) :
    N.evalSeq (fun n => singularValue T n) = N.toPaper.extendedGauge T := rfl

/-- **A sequence that is an operator's singular-value sequence is measured by
the operator's norm.**  This is the bridge every tangent conclusion needs: a
representative with the right approximation numbers turns a sequence norm into
an operator norm. -/
theorem UINorm.evalSeq_eq_of_approximationNumber (N : UINorm) (s : ℕ → ℝ)
    (T : E →L[𝕜] F) (h : ∀ n, T.approximationNumber n = s n) :
    N.evalSeq s = N.toPaper.extendedGauge T := by
  refine iSup_congr fun n => ?_
  congr 1
  exact congrArg _ (funext fun i => (h (i : ℕ)).symm)

/-- The two ideals are the same ideal. -/
theorem UINorm.finite_iff (N : UINorm) (T : E →L[𝕜] F) :
    N.Finite T ↔ N.toPaper.Mem T := Iff.rfl

/-- The two real-valued norms agree. -/
theorem UINorm.norm_eq (N : UINorm) (T : E →L[𝕜] F) :
    N.norm T = N.toPaper.gauge T := rfl

end NormBridge

/-! ## 2. The block data and the separation are the development's -/

section VocabularyBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's isometry condition is the development's. -/
theorem isIsometric_iff (T : F →L[𝕜] E) :
    IsIsometric T ↔ TauCeti.DavisKahan.IsometricEmbedding T := Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's trial-residual data is the development's. -/
theorem isTrialResidual_iff (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔ _root_.DavisKahan1970.IsTrialResidual A A₀ E₀ R := by
  constructor
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩

/-- The Challenge's exact decomposition is the development's. -/
theorem isExactDecomposition_iff (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) :
    IsExactDecomposition A Λ₁ F₀ F₁ ↔
      _root_.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ := by
  constructor
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩

omit [CompleteSpace E] in
/-- The Challenge's real resolvent set is the development's. -/
theorem realResolventSet_eq (A : E →ₗ.[𝕜] E) :
    realResolventSet A = TauCeti.LinearPMap.realResolventSet A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff]
  rfl

omit [CompleteSpace E] in
/-- Hence so is the real spectrum. -/
theorem realSpectrum_eq (A : E →ₗ.[𝕜] E) :
    realSpectrum A = TauCeti.LinearPMap.realSpectrum A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, realSpectrum, Set.mem_compl_iff,
    realResolventSet_eq]

omit [CompleteSpace E] in
/-- The Challenge's lower form bound is the development's. -/
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔ TauCeti.LinearPMap.SemiboundedBelow A c := by
  rw [TauCeti.LinearPMap.semiboundedBelow_iff]
  exact Iff.rfl

omit [CompleteSpace E] in
/-- The Challenge's upper form bound is the development's. -/
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔ TauCeti.LinearPMap.SemiboundedAbove A c := by
  rw [TauCeti.LinearPMap.semiboundedAbove_iff]
  exact Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Challenge's separation is the development's**, constructor by
constructor -- including both half-infinite configurations. -/
theorem sylvesterGap_iff (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) :
    SylvesterGap A B δ ↔ FormBoundedSylvesterGap A B δ := by
  constructor
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap, ← realSpectrum_eq, ← realSpectrum_eq]
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).1 hA)
        ((semiboundedAbove_iff _ _).1 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).1 hA)
        ((semiboundedBelow_iff _ _).1 hB)
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap] at hgap
      rw [← realSpectrum_eq, ← realSpectrum_eq] at hgap
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).2 hA)
        ((semiboundedAbove_iff _ _).2 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).2 hA)
        ((semiboundedBelow_iff _ _).2 hB)

end VocabularyBridge

/-! ## 3. Reduction, blocks and the perturbed operator -/

section ReducingBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's reduction predicate is the development's. -/
theorem reduces_iff (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    Reduces A U ↔ TauCeti.LinearPMap.ReducesSubspace A U := by
  constructor
  · exact fun h => TauCeti.LinearPMap.ReducesSubspace.of_components h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact fun h => ⟨h.projection_mem_domain, h.orthogonalProjection_mem_domain,
      h.invariant, h.orthogonal_invariant⟩

omit [CompleteSpace E] in
/-- **The Challenge's block is the development's reducing restriction**, as an
equality of partial maps: same domain, same action. -/
theorem block_eq (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (h : Reduces A U) :
    block A U h = TauCeti.LinearPMap.reducingRestriction A U ((reduces_iff A U).1 h) := by
  refine LinearPMap.ext ?_ ?_
  · refine Submodule.ext fun x => ?_
    rw [TauCeti.LinearPMap.reducingRestriction_domain,
      TauCeti.LinearPMap.mem_reducingRestrictionDomain_iff]
    exact Iff.rfl
  · intro x hf hg
    refine Subtype.ext ?_
    exact (TauCeti.LinearPMap.coe_reducingRestriction_apply A U
      ((reduces_iff A U).1 h) x hg).symm

omit [CompleteSpace E] in
/-- The Challenge's bounded perturbation of a partial map is the
development's. -/
theorem addBounded_eq (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    addBounded A V = TauCeti.LinearPMap.addBounded A V := by
  refine LinearPMap.ext ?_ ?_
  · rw [TauCeti.LinearPMap.addBounded_domain]
    rfl
  · intro x hf hg
    rw [TauCeti.LinearPMap.addBounded_apply]
    rfl


/-- **A Challenge Rayleigh--Ritz bundle is the development's unbounded Ritz
pair**, field for field.  The compression stays a partial map, so the Appendix
scope in which the Ritz operator is unbounded survives the translation. -/
def RitzData.toUnboundedRitzPair {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (D : RitzData A U) :
    TauCeti.DavisKahan.UnboundedRitzPair A U where
  trial :=
    { compression := D.compression
      compression_isSelfAdjoint := D.compression_selfAdjoint
      residual := D.residual
      residual_orthogonal := D.residual_orthogonal }
  mem_domain := D.mem_domain
  action_eq := fun z => (D.action_eq z).symm

omit [CompleteSpace E] in
/-- The Challenge's two vanishing diagonal blocks are the development's
odd-for-the-splitting condition: this is the source's `H₀ = H₁ = 0`. -/
theorem isOddFor_of_offDiagonal {H : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection]
    (h₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (h₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0) :
    TauCeti.IsOddFor U H := by
  constructor
  · intro x hx
    refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
    have hx0 := congrArg (fun T : E →L[𝕜] E => T x) h₀
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx0
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at hx0
  · intro x hx
    rw [← Submodule.orthogonal_orthogonal U]
    refine (Submodule.starProjection_apply_eq_zero_iff Uᗮ).1 ?_
    have hx1 := congrArg (fun T : E →L[𝕜] E => T x) h₁
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx1
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at hx1

/-- **A subspace reducing the perturbed operator gives the reflection data the
ambient double-angle theorems consume.** -/
theorem reflectionIntertwines_of_reduces {A : E →ₗ.[𝕜] E} {H : E →L[𝕜] E}
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
    TauCeti.DavisKahan.ReflectionIntertwines A H V :=
  TauCeti.DavisKahan.ReflectionIntertwines.ofReducesSubspace
    (by rw [← addBounded_eq]; exact (reduces_iff _ _).1 hV)

end ReducingBridge

/-! ## 4. The `sin Θ` theorem

Every Challenge object above is the development's, so the Challenge statement is
the development's statement.  What is left is the scalar field: the development
proves this at `ℝ` and at `ℂ`, and its `RCLike`-generic form carries two
capability binders that are instances at exactly those two fields. -/

section SinTheta

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The Challenge's `sin Θ` statement, discharged from the development.**

The two binders are the development's proof capabilities, not source hypotheses:
the unbounded Sylvester Ky Fan estimate and the min--max lower bound.  Both are
instances at `ℝ` and at `ℂ`, so at either of the paper's fields this theorem is
the Challenge statement with nothing assumed. -/
theorem sinTheta_of_capabilities
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    [HasUnboundedSylvesterKyFan.{u, v} 𝕜]
    (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R :=
  _root_.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike
    N.toPaper A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
    ((isTrialResidual_iff A A₀ E₀ R).1 hres)
    ((isExactDecomposition_iff A Λ₁ F₀ F₁).1 hdec)
    hδ ((sylvesterGap_iff A₀ Λ₁ δ).1 hgap) hR

end SinTheta

/-! ## 5. The ambient clause of `sin 2Θ`

This is the clause that fixes the reducing-versus-spectral question in the
Challenge's favour: the development's ambient double-angle theorem is already
stated for an *arbitrary* reducing subspace, and the source's `Q` reduces
`A + H`, so no spectral selection is needed on either side.  The only piece the
Challenge has to supply is that reflection through `V` preserves `dom A` and
intertwines, which is `reflectionIntertwines_of_reduces`. -/

section SinTwoThetaAmbient

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **The ambient clause of the Challenge's `sin 2Θ` theorem, discharged from the
development**, at an arbitrary reducing subspace and the full source gap.

`δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, with the angle read as the projector difference between
`U` and its mirror image in `V` -- which is exactly the Challenge's
`ambientDoubleSine`. -/
theorem sinTwoTheta_ambient_of_capabilities
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    [HasUnboundedSylvesterKyFan.{u, v} 𝕜]
    (N : UINorm) {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    N.Finite (ambientDoubleSine U V) ∧
      δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hRI := reflectionIntertwines_of_reduces hV
  have hHsym : TauCeti.DavisKahan.IsSelfAdjointOperator H :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [block_eq A U hU, block_eq A Uᗮ hU.orthogonal] at hgap
    exact (sylvesterGap_iff _ _ _).1 hgap
  refine TauCeti.DavisKahan1970.sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm
    N.toPaper hA H hHsym hUred hRI.mapsDomain ?_ hδ hgap' hHmem
  intro x
  have hc := hRI.commutes x
  have hD : TauCeti.DavisKahan.reflectionPerturbation V H
        (V.reflectionOperator ((x : E))) =
      H (V.reflectionOperator ((x : E))) - V.reflectionOperator (H ((x : E))) := by
    show H _ - TauCeti.DavisKahan.boundedUnitaryConjugate V.reflection H _ = _
    rw [TauCeti.DavisKahan.boundedUnitaryConjugate_apply, V.reflection_symm]
    change H (V.reflection ((x : E))) -
      V.reflection (H (V.reflection (V.reflection ((x : E))))) = _
    rw [Submodule.reflection_reflection]
    rfl
  rw [TauCeti.LinearPMap.addBounded_apply, hD, ← add_sub_assoc]
  exact sub_eq_iff_eq_add.mpr hc

end SinTwoThetaAmbient

/-! ## 6. The two capability classes at the paper's fields -/

section Capabilities

/-- Both capabilities are instances at `ℂ`. -/
example : ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{0, v} ℂ := inferInstance

example : HasUnboundedSylvesterKyFan.{0, v} ℂ := inferInstance

/-- And at `ℝ`. -/
example : ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{0, v} ℝ := inferInstance

example : HasUnboundedSylvesterKyFan.{0, v} ℝ := inferInstance

end Capabilities

/-! ## 7. Status

This file is a **feasibility candidate**, not a finished submission.  The honest
state of each printed clause is recorded here and, clause by clause with the
paper, in `dev/palomar-section-two-challenge-statement-audit.md`.

### Discharged

* **`sinTheta`** — `sinTheta_of_capabilities` *is* the Challenge statement,
  proved from `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`.
* **`sinTwoTheta`, ambient clause** — `sinTwoTheta_ambient_of_capabilities`,
  proved from `TauCeti.DavisKahan1970.sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm`
  at an *arbitrary reducing* subspace, which is the source's own scope.

Both carry the two capability binders, which are instances at `ℝ` and at `ℂ`.

### The scalar field

`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜` and
`HasUnboundedSylvesterKyFan 𝕜` are proof capabilities of the development, not
source hypotheses, and they never appear in the Challenge.  Both quantify over
*every* `𝕜`-Hilbert space, so proving them at an arbitrary `RCLike` field means
splitting on `RCLike.I_eq_zero_or_im_I_eq_one` and transporting a Hilbert space
along a scalar-field isomorphism.

* `I = 0` branch: `InnerProductSpace.rclikeToReal 𝕜 E` already supplies the real
  structure, and `𝕜`-linearity and `ℝ`-linearity coincide because the `𝕜`-scalars
  *are* the real ones, so ranks -- hence approximation numbers -- agree.
* `im I = 1` branch: Mathlib has no counterpart.  The `ℂ`-module structure has to
  be built from `RCLike.complexRingEquiv` through `Module.compHom`, and the
  branch cannot be routed through `ℝ` instead: real and complex rank differ by a
  factor two, so approximation numbers would not agree.

Either way, what must transport is the same list -- `→L`, `→ₗ.`, rank and
approximation numbers, `IsSelfAdjoint`, the quadratic-form bounds,
`realSpectrum`, and the Ky Fan gauge.

**Of the two routes for the Challenge, proving the two class instances once is
the smaller.**  Dispatching each Challenge theorem to its fixed-field endpoints
instead needs exactly the same transport, repeated per theorem and specialized to
each theorem's data, and it would leave the development's own generic Section 2
surface still owing it.

### Open correspondences

* **`sinTwoTheta`, directed clause.** The development's directed endpoint fixes
  its subspace spectrally and takes a *bounded* trial compression.  Both are
  narrowings of the printed scope, and the first is mechanical: the underlying
  estimate consumes only reducing facts.
* **`tanTheta`, both clauses.** The development takes the tangent representative
  as a parameter, so it neither derives `TangentDefined` nor produces a
  representative; the Challenge's non-vacuous form needs both.
  `UINorm.evalSeq_eq_of_approximationNumber` is the bridge that will consume a
  representative once one exists.  For the ambient clause the representative is
  already `paperTanAngleOperatorC U V`; what is missing is the statement that its
  approximation numbers are `tanSeq (ambientSine U V)`.
* **`tanTwoTheta`, both clauses.** The same, with
  `reflectionTangentCorner` and `paperAbsTanTwoAngleOperatorC` as the
  representatives, plus the spectral-to-reducing generalization.

What this file does establish is the part that was in doubt: the Challenge's
vocabulary is not an approximation of the development's, it *is* the
development's.  The norm -- the object most at risk of being quietly weakened in
a compact restatement -- corresponds by `rfl`; the separation corresponds
constructor by constructor including both half-infinite branches; the trial data
corresponds field for field with the compression still a partial map; and the
off-diagonal condition corresponds to the development's `IsOddFor`. -/

end

end RotationOfEigenvectors
