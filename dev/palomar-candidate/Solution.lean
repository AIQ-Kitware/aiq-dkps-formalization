/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Challenge
import DavisKahan.All
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ScalarTransport
import ForTauCeti.Analysis.InnerProductSpace.Projection.ScalarTransport

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

open scoped InnerProductSpace

noncomputable section

universe u v w

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

omit [CompleteSpace E] [CompleteSpace F] in
/-- `TangentDefined S` is `‖S‖ < 1` read off the singular-value sequence: the
`n`-th cosine vanishes exactly when the `n`-th singular value is one. -/
theorem tangentDefined_of_approximationNumber_lt_one (S : E →L[𝕜] F)
    (h : ∀ n, S.approximationNumber n < 1) : TangentDefined S := by
  intro n
  rw [Real.cos_arcsin]
  have h0 : 0 ≤ singularValue S n := S.approximationNumber_nonneg n
  have h1 : singularValue S n < 1 := h n
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))

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

omit [CompleteSpace E] in
/-- The ordered form bound on the trial block, in the ambient indexing the
development's ordered-gap endpoints take.  Reading the bound ambiently rather
than through `block` is what lets it cross a change of scalar field with no
transport of the subspace's own Hilbert structure. -/
theorem formBound_upper_of_semiboundedAbove {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U) {α : ℝ}
    (hlow : SemiboundedAbove (block A U hU) α) :
    ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2 := fun x hxU =>
  hlow ⟨⟨(x : E), hxU⟩, x.2⟩

omit [CompleteSpace E] in
/-- The ordered form bound on the complementary block, likewise. -/
theorem formBound_lower_of_semiboundedBelow {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U) {c : ℝ}
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) c) :
    ∀ x : A.domain, (x : E) ∈ Uᗮ →
      c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜 := fun x hxU =>
  hhigh ⟨⟨(x : E), hxU⟩, x.2⟩

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

/-- **The Challenge's `sin Θ` statement, discharged from the development at an
arbitrary `RCLike` field.**

There are no capability binders: `ContinuousLinearMap.hasMinMaxLowerBoundEverywhere`
and `ExactSinTheta.hasUnboundedSylvesterKyFan` are now instances at every `RCLike`
field, proved by transport through `TauCeti.ScalarTransport`.  So this is the
Challenge's `sinTheta` statement with nothing assumed beyond the source
hypotheses. -/
theorem sinTheta_proof
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
theorem sinTwoTheta_ambient_proof
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

/-! ## 6. The ambient tangent correspondence

The Challenge's ambient `tan Θ` quantity is `N.seqNorm (tanSeq (ambientSine U V))`: the
norm's value on the sequence `tan θ₀, tan θ₁, …` of tangents of the principal angles.  The
development's ambient `tan Θ` estimate is about the *operator*
`paperTanAngleOperatorC U V`.  These carry the same content exactly when the operator's
approximation numbers are that sequence, which
`DavisKahan1970.approximationNumber_paperTanAngleOperatorC` now proves.

That closes the correspondence over `ℂ`; only the scalar field separates it from the
Challenge's clause. -/

section AmbientTangentBridge

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The Challenge's ambient tangent sequence is the development's tangent operator's
singular-value sequence.** -/
theorem tanSeq_ambientSine_eq_approximationNumber
    (htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1) (n : ℕ) :
    tanSeq (ambientSine U V) n =
      (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V).approximationNumber n := by
  rw [TauCeti.DavisKahan1970.approximationNumber_paperTanAngleOperatorC U V htr n,
    TauCeti.DavisKahan1970.approximationNumber_sinAngleOperatorC U V n]
  rfl

/-- **Under uniform transversality no principal angle is a right angle**, so the
Challenge's `TangentDefined` conclusion holds. -/
theorem tangentDefined_ambientSine
    (htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1) :
    TangentDefined (ambientSine U V) := by
  intro n
  have hnorm : ‖ambientSine U V‖ < 1 := by
    have h : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ = ‖ambientSine U V‖ := by
      rw [TauCeti.DavisKahanExt.sinAngleOperatorC, ContinuousLinearMap.norm_modulus,
        norm_sub_rev]
      rfl
    rwa [h] at htr
  have hle : singularValue (ambientSine U V) n ≤ ‖ambientSine U V‖ :=
    (ambientSine U V).approximationNumber_le_norm n
  have h0 : 0 ≤ singularValue (ambientSine U V) n :=
    (ambientSine U V).approximationNumber_nonneg n
  have hlt : singularValue (ambientSine U V) n < 1 := lt_of_le_of_lt hle hnorm
  rw [Real.cos_arcsin]
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))

/-- **The Challenge's ambient tangent sequence norm is the development's paper norm of
`tan Θ`.**  This is the bridge the ambient `tan Θ` clause consumes. -/
theorem evalSeq_tanSeq_ambientSine (N : UINorm)
    (htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1) :
    N.evalSeq (tanSeq (ambientSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) :=
  N.evalSeq_eq_of_approximationNumber _ _
    (fun n => (tanSeq_ambientSine_eq_approximationNumber U V htr n).symm)

end AmbientTangentBridge

/-! ## 7. The directed `tan Θ` clause, over `ℂ`

The directed clause is the one whose left-hand side is a *sequence* norm with no operator
in sight, so it is the clearest test of the Challenge's tangent convention.  The
development supplies all three parts of it at the Appendix's own scope — the pole
exclusion, a representative with exactly the paper's approximation numbers, and the
inequality — in `tanTheta_directed_unboundedRitz_paperUINorm_exists_complex`.  What is
left here is the translation, and the scalar field. -/

section DirectedTangent

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's directed sine block *is* the development's. -/
theorem directedSineBlock_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSineBlock U V = TauCeti.DavisKahan.ExactTanTheta.theorem63DirectedSineBlock U V :=
  rfl

/-- **The directed clause of the Challenge's `tan Θ` theorem, discharged from the
development over `ℂ`.**

All three printed parts: the tangent has no pole, the tangent sequence lies in the norm's
ideal, and `δ ‖tan Θ₀‖ ≤ ‖R‖`.  The compression is a partial map, the ambient operator is
an unbounded self-adjoint partial map, only the residual is bounded, the dimension is
arbitrary, the separation is the half-infinite ordered one, and the norm is arbitrary. -/
theorem tanTheta_directed_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ))
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α) (hR : N.Finite D.residual) :
    TangentDefined (directedSineBlock U V) ∧
      N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
      δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
  -- the ordered lower bound, read off the reducing complement rather than the block
  have hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ := by
    intro y hyV hy
    exact hunwanted ⟨⟨y, hyV⟩, hy⟩
  obtain ⟨hlt, tanTheta0, htan, hmem, hbound⟩ :=
    TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_exists_complex
      N.toPaper D.toUnboundedRitzPair
      (TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV))
      hδ ((semiboundedAbove_iff _ _).1 hupper) hUnwanted hR
  -- the Challenge's sequence is the representative's approximation-number sequence
  have hseq : ∀ n, (tanTheta0.approximationNumber n) = tanSeq (directedSineBlock U V) n :=
    fun n => htan n
  have heval : N.evalSeq (tanSeq (directedSineBlock U V)) =
      N.toPaper.extendedGauge tanTheta0 :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have h := hlt n
    rw [Real.cos_arcsin]
    have h0 : 0 ≤ singularValue (directedSineBlock U V) n :=
      (directedSineBlock U V).approximationNumber_nonneg n
    exact ne_of_gt (Real.sqrt_pos.mpr (by
      have : singularValue (directedSineBlock U V) n < 1 := h
      nlinarith))
  · show N.evalSeq (tanSeq (directedSineBlock U V)) ≠ ⊤
    rw [heval]
    exact hmem
  · show δ * (N.evalSeq (tanSeq (directedSineBlock U V))).toReal ≤ N.norm D.residual
    rw [heval]
    exact hbound

end DirectedTangent

/-! ## 8. The ambient `tan Θ` clause, over `ℂ` -/

section AmbientTangentClause

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The ambient clause of the Challenge's `tan Θ` theorem, discharged from the
development over `ℂ`.**

`δ ‖tan Θ‖ ≤ ‖H‖` on the tangent *sequence* of the ambient angle, with the pole exclusion
as a conclusion.  Uniform transversality is derived from the two form bounds and the
standing condition (3.5) by
`DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_unboundedRitz`, and the sequence is
identified with the development's operator `tan Θ` by
`DavisKahan1970.approximationNumber_paperTanAngleOperatorC`. -/
theorem tanTheta_ambient_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ))
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hres : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (h35 : CrossedDefectsEquivalent U V) (hHmem : N.Finite H) :
    TangentDefined (ambientSine U V) ∧
      N.SeqFinite (tanSeq (ambientSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H := by
  have hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ := by
    intro y hyV hy
    exact hunwanted ⟨⟨y, hyV⟩, hy⟩
  have hVc : TauCeti.DavisKahan.ReducingComplement A V :=
    TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV)
  have hupper' : TauCeti.LinearPMap.SemiboundedAbove
      D.toUnboundedRitzPair.trial.compression α := (semiboundedAbove_iff _ _).1 hupper
  have htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1 :=
    TauCeti.DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_unboundedRitz
      D.toUnboundedRitzPair hVc hδ hupper' hUnwanted h35
  obtain ⟨hmem, hbound⟩ :=
    TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_complex
      N.toPaper D.toUnboundedRitzPair hVc H hH hδ hupper' hUnwanted h35 hres hHmem
  have heval := evalSeq_tanSeq_ambientSine U V N htr
  refine ⟨tangentDefined_ambientSine U V htr, ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · show δ * (N.evalSeq (tanSeq (ambientSine U V))).toReal ≤ N.norm H
    rw [heval]; exact hbound

end AmbientTangentClause

/-! ## 9. The two `tan 2Θ` clauses, over `ℂ`

Both clauses read the doubled tangent off the **double-angle sine**, through the
same monotone `u ↦ tan (arcsin u)` that `tan Θ` uses.  That is forced: the map
`θ ↦ sin 2θ` is not monotone on `[0, π/2]`, so `n ↦ sin (2 arcsin aₙ(sin Θ))` is
not in general the ordered singular-value sequence of `sin 2Θ` — principal angles
`75°` and `30°` already invert the order — and no indexwise theorem can carry a
doubled angle from the single-angle sine at arbitrary dimension.

The development supplies both halves.  For the ambient clause,
`approximationNumber_paperAbsTanTwoAngleOperatorC_projectorDifference` says the
paper's `|tan 2Θ|` has exactly the sequence `tan (arcsin aₙ(sin 2Θ))`; for the
directed clause,
`tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_paperUINorm_complex`
says the same of the directed corner against `sin 2Θ₀`, with each directed
principal angle counted once. -/

section TanTwoThetaClauses

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's directed double-angle sine *is* the development's directed
`sin 2Θ₀` block. -/
theorem directedDoubleSine_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedDoubleSine U V = TauCeti.DavisKahan.sinTwoThetaIdealBlock U V := rfl

omit [CompleteSpace E] in
/-- The Challenge's ambient double-angle sine is the development's projector
difference between `U` and its mirror image in `V`. -/
theorem ambientDoubleSine_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ambientDoubleSine U V =
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection -
        U.starProjection := rfl

/-- **The directed clause of the Challenge's `tan 2Θ` theorem, discharged from
the development over `ℂ`.**

`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` on the residual corner alone, with the pole exclusion as a
conclusion and each directed principal angle counted once.  The trial subspace is
any subspace reducing `A` with the ordered separation; no spectral selection. -/
theorem tanTwoTheta_directed_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℂ] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have hblk : TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H =
      Uᗮ.starProjection ∘L H ∘L U.starProjection := rfl
  have hgap : N.toPaper.extendedGauge
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) :=
    N.toPaper.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock_same_compression Uᗮ U H)
  have hRmem0 : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
    rw [hblk]
    exact (N.finite_iff _).1 hRmem
  have hRmem' : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
    unfold PaperUnitaryInvariantNorm.Mem at hRmem0 ⊢
    rwa [← hgap]
  obtain ⟨hlt, hseq, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_paperUINorm_complex
      N.toPaper V hA ((reduces_iff A U).1 hU)
      (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      (reflectionIntertwines_of_reduces hV)
      hlow hhigh (by linarith) hRmem'
  have heval : N.evalSeq (tanSeq (directedDoubleSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan1970.reflectionTangentCorner U
        V.reflectionOperator) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ hlt, ?_, ?_⟩
  · show N.evalSeq (tanSeq (directedDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hg : N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
        N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
      unfold PaperUnitaryInvariantNorm.gauge
      rw [hgap]
    have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (directedDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge
          (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
      rw [heval, hg]
      exact hle
    rw [← hblk]
    exact hgoal

/-- **The ambient clause of the Challenge's `tan 2Θ` theorem, discharged from the
development over `ℂ`.**

`δ ‖tan 2Θ‖ ≤ 2 ‖H‖` on the whole perturbation, with each ambient principal angle
counted with its ambient multiplicity, and the quarter-turn exclusion derived. -/
theorem tanTwoTheta_ambient_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    TangentDefined (ambientDoubleSine U V) ∧
      N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
  obtain ⟨hcos, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_reducing_paperUINorm_complex
      N.toPaper V hA ((reduces_iff A U).1 hU) hH
      (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      (reflectionIntertwines_of_reduces hV)
      hlow hhigh (by linarith) hHmem
  have hseq : ∀ n,
      (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC U V).approximationNumber n =
        tanSeq (ambientDoubleSine U V) n := fun n =>
    TauCeti.DavisKahan1970.approximationNumber_paperAbsTanTwoAngleOperatorC_projectorDifference
      U V hcos n
  have heval : N.evalSeq (tanSeq (ambientDoubleSine U V)) =
      N.toPaper.extendedGauge
        (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC U V) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ (fun n =>
    TauCeti.DavisKahan1970.approximationNumber_projectorDifference_lt_one U V hcos n), ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (ambientDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge H := by
      rw [heval]; exact hle
    exact hgoal

end TanTwoThetaClauses

section TanTwoThetaDirectedReal

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The directed clause of the Challenge's `tan 2Θ` theorem, discharged from
the development over `ℝ`.**

`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` on the residual corner alone, with the pole exclusion as a
conclusion and each directed principal angle counted once.  The trial subspace is
any subspace reducing `A` with the ordered separation; no spectral selection. -/
theorem tanTwoTheta_directed_proof_real (N : UINorm)
    {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℝ] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℝ)
    {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have hblk : TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H =
      Uᗮ.starProjection ∘L H ∘L U.starProjection := rfl
  have hgap : N.toPaper.extendedGauge
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) :=
    N.toPaper.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock_same_compression Uᗮ U H)
  have hRmem0 : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
    rw [hblk]
    exact (N.finite_iff _).1 hRmem
  have hRmem' : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
    unfold PaperUnitaryInvariantNorm.Mem at hRmem0 ⊢
    rwa [← hgap]
  have hlow' : ∀ x : A.domain, (x : E) ∈ U →
      ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2 := by
    intro x hx; simpa using hlow x hx
  have hhigh' : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ := by
    intro x hx; simpa using hhigh x hx
  obtain ⟨hlt, hseq, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_sineSequence_paperUINorm_real
      N.toPaper V hA ((reduces_iff A U).1 hU)
      (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      (reflectionIntertwines_of_reduces hV)
      hlow' hhigh' (by linarith) hRmem'
  have heval : N.evalSeq (tanSeq (directedDoubleSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan1970.reflectionTangentCorner U
        V.reflectionOperator) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ hlt, ?_, ?_⟩
  · show N.evalSeq (tanSeq (directedDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hg : N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
        N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
      unfold PaperUnitaryInvariantNorm.gauge
      rw [hgap]
    have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (directedDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge
          (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
      rw [heval, hg]
      exact hle
    rw [← hblk]
    exact hgoal


end TanTwoThetaDirectedReal


/-! ## 10. The directed clause of `sin 2Θ`, over `ℂ`

The clause the Appendix bounds by a **bounded** trial compression: `V` sits
inside `dom A`, so `M` is bounded by the closed-graph theorem and the two are the
same hypothesis.  What is *not* assumed is that `U` was selected spectrally --
`sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_paperUINorm_complex`
takes any subspace reducing `A`, which is the source's own hypothesis. -/

section SinTwoThetaDirected

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The directed clause of the Challenge's `sin 2Θ` theorem, discharged from
the development over `ℂ`.**

`δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` on the residual alone, at an arbitrary reducing `U` and
the full form-bounded gap, so the separating interval may be half-infinite. -/
theorem sinTwoTheta_directed_proof_complex
    (N : UINorm) {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    {V : Submodule ℂ E} [V.HasOrthogonalProjection] (D : BoundedTrialBlock A V)
    (hRmem : N.Finite D.residual) :
    N.Finite (directedDoubleSine U V) ∧
      δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hgap' : TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [block_eq A U hU, block_eq A Uᗮ hU.orthogonal] at hgap
    exact (sylvesterGap_iff _ _ _).1 hgap
  have hres : ∀ v : V, A ⟨(v : E), D.mem_domain v⟩ =
      D.residual v + ((D.compression v : V) : E) := fun v =>
    (D.action_eq v).trans (add_comm _ _)
  exact TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_paperUINorm_complex
    N.toPaper hA hUred D.mem_domain hres hδ hgap' hRmem

end SinTwoThetaDirected

/-! ## 11. The scalar field

Every Challenge quantity above is a function of an operator's singular-value
sequence, and `TauCeti.ScalarTransport` changes neither the vectors, the norm,
the operators, nor therefore that sequence.  So a clause proved at `ℝ` and at `ℂ`
is a clause at every `RCLike` field: `RCLike.I_eq_zero_or_im_I_eq_one` says there
is an isomorphism onto one of the two, and the dictionary below carries the
statement across it. -/

section Transport

open TauCeti.ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : TauCeti.RCLikeIso 𝕜 𝕂}
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transport is multiplicative on composable operators. -/
theorem clm_comp {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (X : F →L[𝕜] G) (Y : E →L[𝕜] F) :
    clm (e := e) (X ∘L Y) = clm (e := e) X ∘L clm (e := e) Y := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transport of the zero operator. -/
theorem clm_zero : clm (e := e) (0 : E →L[𝕜] F) = 0 := rfl

/-- **The transport preserves every value a unitarily invariant norm takes.**
Both sides read the same singular-value sequence. -/
theorem UINorm.eval_clm (N : UINorm) (T : E →L[𝕜] F) :
    N.eval (clm (e := e) T) = N.eval T :=
  congrArg N.evalSeq (funext fun n => approximationNumber_clm (e := e) T n)

/-- Ideal membership is unchanged by the transport. -/
theorem UINorm.finite_clm_iff (N : UINorm) (T : E →L[𝕜] F) :
    N.Finite (clm (e := e) T) ↔ N.Finite T := by
  unfold UINorm.Finite
  rw [UINorm.eval_clm]

/-- The real-valued norm is unchanged by the transport. -/
theorem UINorm.norm_clm (N : UINorm) (T : E →L[𝕜] F) :
    N.norm (clm (e := e) T) = N.norm T := by
  unfold UINorm.norm
  rw [UINorm.eval_clm]

omit [CompleteSpace F] in
/-- The Challenge's reducing predicate transports. -/
theorem reduces_pmap_iff {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] :
    Reduces (pmap (e := e) A) (submodule (e := e) U) ↔ Reduces A U := by
  rw [reduces_iff, reduces_iff, reducesSubspace_pmap_iff]

omit [CompleteSpace F] in
/-- The Challenge's bounded perturbation transports. -/
theorem addBounded_pmap {A : E →ₗ.[𝕜] E} (T : E →L[𝕜] E) :
    pmap (e := e) (addBounded A T) =
      addBounded (pmap (e := e) A) (clm (e := e) T) := by
  rw [addBounded_eq, addBounded_eq, pmap_addBounded]

omit [CompleteSpace F] in
/-- The ambient double-angle sine transports. -/
theorem ambientDoubleSine_pmap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ambientDoubleSine (submodule (e := e) U) (submodule (e := e) V) =
      clm (e := e) (ambientDoubleSine U V) := by
  show ((submodule (e := e) U).map _).starProjection -
      (submodule (e := e) U).starProjection = _
  rw [Submodule.starProjection_congr (submodule_map_reflection (e := e) U V).symm,
    starProjection_clm, starProjection_clm, ← clm_sub]
  rfl

omit [CompleteSpace F] in
/-- The directed double-angle sine transports. -/
theorem directedDoubleSine_pmap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedDoubleSine (submodule (e := e) U) (submodule (e := e) V) =
      clm (e := e) (directedDoubleSine U V) := by
  have hmap : ((submodule (e := e) U)ᗮ).map
      (((submodule (e := e) V).reflection.toLinearEquiv :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e E)) =
      submodule (e := e) (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)) := by
    rw [submodule_orthogonal]
    exact (submodule_map_reflection (e := e) Uᗮ V).symm
  show (submodule (e := e) U).starProjection ∘L
      ((submodule (e := e) U)ᗮ.map _).starProjection = _
  rw [Submodule.starProjection_congr hmap, starProjection_clm, starProjection_clm,
    ← clm_comp]
  rfl

omit [CompleteSpace F] in
/-- `TangentDefined` reads only the singular-value sequence, so it transports. -/
theorem tangentDefined_clm_iff (T : E →L[𝕜] F) :
    TangentDefined (clm (e := e) T) ↔ TangentDefined T := by
  constructor <;> intro h n
  · have := h n
    rwa [show singularValue (clm (e := e) T) n = singularValue T n from
      approximationNumber_clm (e := e) T n] at this
  · have := h n
    rwa [show singularValue (clm (e := e) T) n = singularValue T n from
      approximationNumber_clm (e := e) T n]

omit [CompleteSpace F] in
/-- and so does the tangent sequence itself. -/
theorem tanSeq_clm (T : E →L[𝕜] F) :
    tanSeq (clm (e := e) T) = tanSeq T :=
  funext fun n => congrArg (fun r => Real.tan (Real.arcsin r))
    (approximationNumber_clm (e := e) T n)

end Transport

/-! ## 12. The ambient `tan 2Θ` clause over `ℝ`, and at every `RCLike` field -/

section TanTwoThetaAmbientGeneric

/-- **The ambient clause of the Challenge's `tan 2Θ` theorem, over `ℝ`.**

The real sibling of `tanTwoTheta_ambient_proof_complex`, discharged from
`tanTwoTheta_ambient_unbounded_reducing_sineSequence_paperUINorm_real`, whose
proof is the complex one applied to the complexification. -/
theorem tanTwoTheta_ambient_proof_real (N : UINorm)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℝ)
    {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    TangentDefined (ambientDoubleSine U V) ∧
      N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
  have hlow' : ∀ x : A.domain, (x : E) ∈ U →
      ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2 := by
    intro x hx
    simpa using hlow x hx
  have hhigh' : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ := by
    intro x hx
    simpa using hhigh x hx
  obtain ⟨hlt, hseq, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_reducing_sineSequence_paperUINorm_real
      hA ((reduces_iff A U).1 hU) (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      hlow' hhigh' (by linarith : α < α + δ) N.toPaper V hH
      (reflectionIntertwines_of_reduces hV) hHmem
  have hlt' : ∀ n, (ambientDoubleSine U V).approximationNumber n < 1 := hlt
  have hseq' : ∀ n,
      (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR U V).approximationNumber n =
        tanSeq (ambientDoubleSine U V) n := hseq
  have heval : N.evalSeq (tanSeq (ambientDoubleSine U V)) =
      N.toPaper.extendedGauge
        (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR U V) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq'
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ hlt', ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (ambientDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge H := by
      rw [heval]; exact hle
    exact hgoal

open TauCeti.ScalarTransport in
/-- **The shared hypothesis package of the ordered-gap clauses, transported.**

Self-adjointness, reducing, the two vanishing diagonal blocks, the two ordered
form bounds and the reduction of the perturbed operator, all read at the
transported field.  Nothing here is specific to a single clause: it is the
Section 2 ordered-gap data. -/
theorem orderedGap_hypotheses_pmap {𝕜 : Type u} {𝕂 : Type} [RCLike 𝕜] [RCLike 𝕂]
    (e : TauCeti.RCLikeIso 𝕜 𝕂)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ}
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
      IsSelfAdjoint (pmap (e := e) A) ∧
      Reduces (pmap (e := e) A) (submodule (e := e) U) ∧
      ((submodule (e := e) U).starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U).starProjection = 0) ∧
      ((submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U)ᗮ.starProjection = 0) ∧
      (∀ y : (pmap (e := e) A).domain,
        (y : ScalarTransport e E) ∈ submodule (e := e) U →
        RCLike.re ⟪pmap (e := e) A y, (y : ScalarTransport e E)⟫_𝕂 ≤
          α * ‖(y : ScalarTransport e E)‖ ^ 2) ∧
      (∀ y : (pmap (e := e) A).domain,
        (y : ScalarTransport e E) ∈ (submodule (e := e) U)ᗮ →
        (α + δ) * ‖(y : ScalarTransport e E)‖ ^ 2 ≤
          RCLike.re ⟪pmap (e := e) A y, (y : ScalarTransport e E)⟫_𝕂) ∧
      Reduces (addBounded (pmap (e := e) A) (clm (e := e) H))
        (submodule (e := e) V) := by
  refine ⟨(isSelfAdjoint_pmap_iff (e := e)).mpr hA,
    (reduces_pmap_iff (e := e)).mpr hU, ?_, ?_, ?_, ?_, ?_⟩
  · rw [starProjection_clm, ← clm_comp, ← clm_comp, hoffdiag₀, clm_zero]
  · rw [Submodule.starProjection_congr (submodule_orthogonal (e := e) U),
      starProjection_clm, ← clm_comp, ← clm_comp, hoffdiag₁, clm_zero]
  · intro y hy
    have hmem : out (e := e) (y : ScalarTransport e E) ∈ A.domain := y.2
    have h := hlow ⟨out (e := e) (y : ScalarTransport e E), hmem⟩
      ((mem_submodule (e := e)).mp hy)
    show RCLike.re (inner 𝕂
        (of (e := e) (A ⟨out (e := e) (y : ScalarTransport e E), hmem⟩))
        (of (e := e) (out (e := e) (y : ScalarTransport e E)))) ≤
      α * ‖out (e := e) (y : ScalarTransport e E)‖ ^ 2
    rw [re_inner_of]
    exact h
  · intro y hy
    have hmem : out (e := e) (y : ScalarTransport e E) ∈ A.domain := y.2
    have hy' : out (e := e) (y : ScalarTransport e E) ∈ Uᗮ := by
      rw [← mem_submodule (e := e), ← submodule_orthogonal (e := e) U]
      exact hy
    have h := hhigh ⟨out (e := e) (y : ScalarTransport e E), hmem⟩ hy'
    show (α + δ) * ‖out (e := e) (y : ScalarTransport e E)‖ ^ 2 ≤
      RCLike.re (inner 𝕂
        (of (e := e) (A ⟨out (e := e) (y : ScalarTransport e E), hmem⟩))
        (of (e := e) (out (e := e) (y : ScalarTransport e E))))
    rw [re_inner_of]
    exact h
  · rw [← addBounded_pmap (e := e) H]
    exact (reduces_pmap_iff (e := e)).mpr hV

open TauCeti.ScalarTransport in
/-- **The ambient clause of the Challenge's `tan 2Θ` theorem, at an arbitrary
`RCLike` field.**

The two fixed-field proofs above, read through `TauCeti.ScalarTransport`.  Every
hypothesis is a statement about vectors, norms, inner-product real parts,
subspaces and operators, all of which the transport carries verbatim; every
conclusion is a function of one operator's singular-value sequence, which it also
carries.  So the case split of `RCLike.I_eq_zero_or_im_I_eq_one` is the whole
argument. -/
theorem tanTwoTheta_ambient_proof (N : UINorm)
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    TangentDefined (ambientDoubleSine U V) ∧
      N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
  -- the transported statement, whichever of the two fields we land in
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (TangentDefined (ambientDoubleSine (submodule (e := e) U) (submodule (e := e) V)) ∧
        N.SeqFinite (tanSeq (ambientDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ∧
        δ * N.seqNorm (tanSeq (ambientDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ≤ 2 * N.norm (clm (e := e) H)) →
      TangentDefined (ambientDoubleSine U V) ∧
        N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
        δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
    intro 𝕂 _ e h
    rw [ambientDoubleSine_pmap (e := e) U V, tanSeq_clm, tangentDefined_clm_iff,
      UINorm.norm_clm] at h
    exact h
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℝ) e
      (tanTwoTheta_ambient_proof_real N h1 h2 _ ((isSelfAdjoint_clm_iff (e := e)).mpr hH)
        h4 h5 hδ h6 h7 h8 ((UINorm.finite_clm_iff (e := e) N H).mpr hHmem))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℂ) e
      (tanTwoTheta_ambient_proof_complex N h1 h2 _ ((isSelfAdjoint_clm_iff (e := e)).mpr hH)
        h4 h5 hδ h6 h7 h8 ((UINorm.finite_clm_iff (e := e) N H).mpr hHmem))


open TauCeti.ScalarTransport in
/-- The residual corner `P_{Uᗮ} H P_U` transports. -/
theorem residualCorner_pmap {𝕜 : Type u} {𝕂 : Type} [RCLike 𝕜] [RCLike 𝕂]
    {e : TauCeti.RCLikeIso 𝕜 𝕂} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →L[𝕜] E) :
    (submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U).starProjection =
      clm (e := e) (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  rw [Submodule.starProjection_congr (submodule_orthogonal (e := e) U),
    starProjection_clm, starProjection_clm, ← clm_comp, ← clm_comp]

open TauCeti.ScalarTransport in
/-- **The directed clause of the Challenge's `tan 2Θ` theorem, at an arbitrary
`RCLike` field.** -/
theorem tanTwoTheta_directed_proof (N : UINorm)
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (TangentDefined (directedDoubleSine (submodule (e := e) U) (submodule (e := e) V)) ∧
        N.SeqFinite (tanSeq (directedDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ∧
        δ * N.seqNorm (tanSeq (directedDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ≤
          2 * N.norm ((submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
            (submodule (e := e) U).starProjection)) →
      TangentDefined (directedDoubleSine U V) ∧
        N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
        δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
          2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
    intro 𝕂 _ e h
    rw [directedDoubleSine_pmap (e := e) U V, tanSeq_clm, tangentDefined_clm_iff,
      residualCorner_pmap (e := e) U H, UINorm.norm_clm] at h
    exact h
  have pushR : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      N.Finite ((submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U).starProjection) := by
    intro 𝕂 _ e
    rw [residualCorner_pmap (e := e) U H]
    exact (UINorm.finite_clm_iff (e := e) N _).mpr hRmem
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℝ) e
      (tanTwoTheta_directed_proof_real N h1 h2 _ h4 h5 hδ h6 h7 h8 (pushR (𝕂 := ℝ) e))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℂ) e
      (tanTwoTheta_directed_proof_complex N h1 h2 _ h4 h5 hδ h6 h7 h8 (pushR (𝕂 := ℂ) e))

end TanTwoThetaAmbientGeneric

/-! ## 13. The two capability classes, at every `RCLike` field -/

section Capabilities

/-- The min--max lower bound, at an arbitrary `RCLike` field. -/
example (𝕜 : Type u) [RCLike 𝕜] :
    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜 := inferInstance

/-- The unbounded Sylvester Ky Fan estimate, likewise. -/
example (𝕜 : Type u) [RCLike 𝕜] : HasUnboundedSylvesterKyFan.{u, v} 𝕜 := inferInstance

end Capabilities

/-! ## 14. Status

This file is a **feasibility candidate**, not a finished submission.  The honest
state of each printed clause is recorded here and, clause by clause with the
paper, in `dev/palomar-section-two-challenge-statement-audit.md`.

### Discharged, unconditionally, at an arbitrary `RCLike` field

* **`sinTheta`** — `sinTheta_proof` *is* the Challenge statement, proved from
  `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`.
* **`sinTwoTheta`, ambient clause** — `sinTwoTheta_ambient_proof`, proved from
  `TauCeti.DavisKahan1970.sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm`
  at an *arbitrary reducing* subspace, which is the source's own scope.

Neither carries a capability binder any more; see below.

### The scalar field: closed

`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜` and
`HasUnboundedSylvesterKyFan 𝕜` are proof capabilities of the development, not
source hypotheses, and they never appear in the Challenge.  Both quantify over
*every* `𝕜`-Hilbert space, so proving them at an arbitrary `RCLike` field means
splitting on `RCLike.I_eq_zero_or_im_I_eq_one` and transporting a Hilbert space
along a scalar-field isomorphism.

**Both are now instances at every `RCLike` field**, and the two routes that were
weighed are settled in favour of the first: proving the classes once is smaller
than dispatching each theorem, needs the same transport either way, and leaves
the development's own generic Section 2 surface owing nothing.

The transport is one construction, used twice.
`TauCeti.RCLikeIso 𝕜 𝕂` is a field isomorphism fixing the reals and `I`, built
from Mathlib's `RCLike.realRingEquiv` and `RCLike.complexRingEquiv`;
`TauCeti.ScalarTransport e E` is `E` with the `𝕂`-structure `e` induces, which
changes the scalar action and the field the inner product takes values in and
changes **nothing else** -- not the vectors, not the additive group, not the
topology, not the norm.  So subspaces keep their carriers, operators keep their
functions and their operator norms, and `Module.rank` -- hence every
approximation number -- is unchanged.  That last point is why restriction of
scalars (`InnerProductSpace.rclikeToReal`) is *not* the right construction here:
over a complex-like `𝕜` it halves the scalars, doubling the rank and changing the
singular-value sequence.

* `ForTauCeti/Analysis/RCLike/ScalarTransport.lean` -- the field isomorphism and
  the transport, with subspaces, orthogonal complements, orthogonal projections,
  bounded operators (function, norm, adjoint, self-adjointness), `Module.rank`,
  and partial maps (domain, function, adjoint, self-adjointness).
* `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/ScalarTransport.lean` --
  approximation numbers, linear independence and spans, and hence
  `ContinuousLinearMap.hasMinMaxLowerBoundEverywhere`.
* `DavisKahan/Sylvester/ScalarTransport.lean` -- finite Ky Fan gauges, the
  operator-form semibounds, the real resolvent set and spectrum, the
  three-constructor separation, the domain-aware Sylvester equation, and hence
  `ExactSinTheta.hasUnboundedSylvesterKyFan`.

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
