/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import TauCeti.Analysis.InnerProductSpace.Polar.Isometry
public import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
public import ForTauCeti.Analysis.InnerProductSpace.Residual.TrialMap
public import ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic

/-!
# Generalized finite-dimensional Davis--Kahan theorems

This file records the finite-dimensional forms of the generalizations stated
after the four headline theorems in Davis--Kahan (1970).

Literature map:

* `prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 5--11.
* Davis--Kahan (1970), Theorems 6.1--6.3 and 8.2.

The important extra features are non-orthonormal trial vectors, comparison of
subspaces of unequal dimension, the square-norm fallback under arbitrary
spectral separation, and the continuation argument selecting the acute branch
of a double-angle estimate.  These are kept separate from the sharp clean API
so their conditioning losses are visible in theorem statements.
-/


/-! ## Construction status

TauCeti's finite polar factorization writes an injective rectangular trial map
as `X = Q T`, with `Q = X.polarIsometry hX` and `T = X.operatorAbsEquiv hX`.
The lower frame bound controls the inverse coordinate and its composition
cost in a unitarily invariant seminorm. The assembled sine estimate is
`ε * N (P_{Vᗮ} Q) ≤ N (P_{Vᗮ} X)`.

The paper's frame and Gram lower-bound predicates were moved here from
`ForTauCeti.Analysis.InnerProductSpace.FrameFactorization` (DKPS `b806b36`,
Jon Crall and GPT 5.6 High, Kitware copyright, Apache-2.0).

Theorem 6.1 is assembled below from this coordinate layer and the raw
projected Sylvester identity.  The source-complete endpoints accept either
interval/exterior orientation, derive injectivity from either the positive
lower frame bound or the paper's Gram-operator inequality, and keep coordinate
operators such as `M` in their original self-adjoint coordinates throughout.
The final wrapper also accepts any `sin Θ₀` operator with the canonical complete
singular-value sequence.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators Topology
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- A quantitative lower frame bound for a not-necessarily-isometric trial
map.  Davis--Kahan's parameter `e` is this lower singular-value bound. -/
@[expose]
def LowerFrameBound (X : F →ₗ[𝕜] E) (ε : ℝ) : Prop :=
  ∀ y, ε * ‖y‖ ≤ ‖X y‖

/-- Davis--Kahan's Gram-operator lower bound
`X⋆ X ≥ ε² I`, written as its quadratic-form inequality.

The real part makes the definition uniform over `ℝ` and `ℂ`; for the positive
Gram operator the quadratic form is real and equals `‖X y‖²`. -/
def GramLowerBound (X : F →ₗ[𝕜] E) (ε : ℝ) : Prop :=
  ∀ y, ε ^ 2 * ‖y‖ ^ 2 ≤
    RCLike.re ⟪(X.adjoint ∘ₗ X) y, y⟫_𝕜

/-- A nonnegative lower frame bound implies the corresponding Gram-operator
quadratic-form bound. -/
theorem LowerFrameBound.gramLowerBound {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hframe : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    GramLowerBound X ε := by
  intro y
  rw [re_inner_adjointCompSelf_self, ← mul_pow]
  exact (sq_le_sq₀ (mul_nonneg hε (norm_nonneg y)) (norm_nonneg _)).2 (hframe y)

/-- A Gram lower bound implies a norm lower bound for any sign of `ε`. -/
theorem GramLowerBound.lowerFrameBound {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hgram : GramLowerBound X ε) :
    LowerFrameBound X ε := by
  intro y
  by_cases hnonneg : 0 ≤ ε * ‖y‖
  · have hy := hgram y
    rw [re_inner_adjointCompSelf_self, ← mul_pow] at hy
    exact (sq_le_sq₀ hnonneg (norm_nonneg _)).1 hy
  · exact (le_of_not_ge hnonneg).trans (norm_nonneg _)

/-- For a nonnegative parameter, the paper's Gram lower bound and the norm-form
lower frame bound are equivalent. -/
theorem lowerFrameBound_iff_gramLowerBound (X : F →ₗ[𝕜] E) {ε : ℝ}
    (hε : 0 ≤ ε) :
    LowerFrameBound X ε ↔ GramLowerBound X ε := by
  constructor
  · intro hframe
    exact hframe.gramLowerBound hε
  · intro hgram
    exact hgram.lowerFrameBound

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A positive lower frame bound implies injectivity. -/
theorem LowerFrameBound.injective {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hframe : LowerFrameBound X ε) (hε : 0 < ε) :
    Function.Injective X := by
  intro x y hxy
  have hmul : ε * ‖x - y‖ ≤ 0 := by
    simpa [map_sub, hxy] using hframe (x - y)
  have hnorm : ‖x - y‖ ≤ 0 := by
    nlinarith [norm_nonneg (x - y)]
  apply sub_eq_zero.mp
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- A positive Gram lower bound implies injectivity. -/
theorem GramLowerBound.injective {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hgram : GramLowerBound X ε) (hε : 0 < ε) :
    Function.Injective X :=
  (hgram.lowerFrameBound).injective hε

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Put the positive frame bound in the form used by the inverse-modulus estimate. -/
theorem LowerFrameBound.norm_le_inv_mul {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hframe : LowerFrameBound X ε) (hε : 0 < ε) (x : F) :
    ‖x‖ ≤ ε⁻¹ * ‖X x‖ :=
  (le_inv_mul_iff₀ hε).2 (hframe x)

namespace DavisKahan.FiniteDimensional

/-- The geometric sine block is the raw complementary trial block followed by
the inverse frame coordinate. -/
theorem complementaryTrialBlock_comp_operatorAbsEquiv_symm
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    complementaryTrialBlock U X ∘ₗ
        (X.operatorAbsEquiv hX).symm.toLinearMap =
      sinThetaEmbedding U (X.polarIsometry hX) := by
  ext y
  change Uᗮ.starProjection (X ((X.operatorAbsEquiv hX).symm y)) =
    Uᗮ.starProjection (X.polarIsometry hX y)
  rw [X.polarIsometry_apply hX]

/-- Lower-frame transport from the raw complementary block to the canonical
sine-angle map in every rectangular unitarily invariant norm. -/
theorem lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {ε : ℝ} (hframe : LowerFrameBound X ε) (hε : 0 < ε) :
    ε * N (sinThetaEmbedding U (X.polarIsometry hX)) ≤
      N (complementaryTrialBlock U X) := by
  have hideal := N.map_comp_operatorAbsEquiv_symm_le (complementaryTrialBlock U X) hX
    (hframe.norm_le_inv_mul hε)
  rw [complementaryTrialBlock_comp_operatorAbsEquiv_symm U X hX] at hideal
  calc
    ε * N (sinThetaEmbedding U (X.polarIsometry hX)) ≤
        ε * (ε⁻¹ * N (complementaryTrialBlock U X)) :=
      mul_le_mul_of_nonneg_left hideal hε.le
    _ = N (complementaryTrialBlock U X) := by
      field_simp [hε.ne']

/-- Symmetric compression after whitening a full-column-rank trial map.

If `X = Q G^{1/2}` is the polar/whitening factorization, this is `Q⋆ A Q`.
The coordinate Rayleigh quotient `(X⋆X)⁻¹ X⋆ A X` is similar to this operator
but is generally only self-adjoint for the Gram inner product. -/
@[expose] noncomputable def generalizedCompression (A : E →ₗ[𝕜] E)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) : F →ₗ[𝕜] F :=
  compression A (X.polarIsometry hX)

/-- The whitened generalized compression is symmetric for a symmetric
ambient operator.

Signature audit: Valid because the public compression is now the whitened
ordinary-self-adjoint operator.
-/
theorem isSymmetric_generalizedCompression {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (generalizedCompression A X hX).IsSymmetric := by
  exact hA.adjoint_conj (X.polarIsometry hX).toLinearMap

/-- The interval/exterior spectral hypothesis for a generalized trial pair,
in either orientation.

The first branch places the coordinate spectrum of `M` in `[a,b]` and the
unwanted exact spectrum of `A` on `Vᗮ` outside the enlarged interval.  The
second branch reverses those roles, as allowed in Davis--Kahan Theorem 6.1. -/
def TrialComplementIntervalGap (M : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] E)
    (V : Submodule 𝕜 E) (a b δ : ℝ) : Prop :=
  Module.End.PointIntervalExteriorGap M ⊤ A Vᗮ a b δ ∨
    Module.End.PointIntervalExteriorGap A Vᗮ M ⊤ a b δ

/-- **Raw generalized sine-block residual estimate, every UI norm.**

For an arbitrary trial map `X`, the complementary block `P_{Vᗮ} X` satisfies
the sharp interval/exterior Sylvester estimate in either spectral orientation.
No injectivity or lower frame bound is needed at this stage. -/
theorem complementaryTrialBlock_residual_le_of_intervalGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : (V ∈ Module.End.invtSubmodule A))
    (X : F →ₗ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (_hδ : 0 < δ)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * N (complementaryTrialBlock V X) ≤ N (generalResidual A X M) := by
  rcases hgap with hforward | hreverse
  · have hbound := N.mul_map_starProjection_comp_le_map_sylvester_apply
      (A := A.toContinuousLinearMap) (M := M.toContinuousLinearMap) hA hM
      ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp hV)
      hforward X.toContinuousLinearMap
    rw [ContinuousLinearMap.sylvester_apply] at hbound
    exact hbound
  · have hVperp := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
      (LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hA hV)
    let Y := Vᗮ.starProjection ∘L X.toContinuousLinearMap
    have hbound := N.mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_of_mem
      (A := A.toContinuousLinearMap) (B := M.toContinuousLinearMap) hA hM hVperp
      (fun _ _ ↦ Submodule.mem_top) hreverse (X := Y)
      (fun y ↦ Vᗮ.starProjection_apply_mem (X y))
      (fun y hy ↦ by simp_all [Submodule.top_orthogonal_eq_bot])
    rw [ContinuousLinearMap.sylvester_apply] at hbound
    change δ * N (complementaryTrialBlock V X) ≤
      N (A ∘ₗ complementaryTrialBlock V X - complementaryTrialBlock V X ∘ₗ M) at hbound
    have hred := (hA.isReducing_iff_mem_invtSubmodule V).mpr hV
    have hEq : A ∘ₗ complementaryTrialBlock V X - complementaryTrialBlock V X ∘ₗ M =
        Vᗮ.starProjection.toLinearMap ∘ₗ generalResidual A X M :=
      hred.sylvester_starProjection_orthogonal_comp X M
    rw [hEq] at hbound
    exact hbound.trans (N.map_starProjection_comp_le Vᗮ (generalResidual A X M))

/-- **Davis--Kahan Theorem 6.1, source-complete interval/exterior form.**

A positive lower frame bound supplies injectivity automatically.  The theorem
allows either interval/exterior orientation and compares subspaces of unequal
dimension through the directed sine block. -/
theorem generalizedSinTheta_residual_le_of_intervalGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : (V ∈ Module.End.invtSubmodule A))
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * ε * N (sinThetaEmbedding V
      (X.polarIsometry (hframe.injective hε))) ≤
      N (generalResidual A X M) := by
  have htransport := lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    N V X (hframe.injective hε) hframe hε
  have hraw := complementaryTrialBlock_residual_le_of_intervalGap
    N hA hV X hM hδ hgap
  calc
    δ * ε * N (sinThetaEmbedding V
        (X.polarIsometry (hframe.injective hε))) =
        δ * (ε * N (sinThetaEmbedding V
          (X.polarIsometry (hframe.injective hε)))) := by ring
    _ ≤ δ * N (complementaryTrialBlock V X) :=
      mul_le_mul_of_nonneg_left htransport hδ.le
    _ ≤ N (generalResidual A X M) := hraw

/-- **Davis--Kahan Theorem 6.1 with the paper's Gram hypothesis.**

This source-facing wrapper accepts the operator inequality
`X⋆ X ≥ ε² I` through `GramLowerBound`, rather than requiring callers to
translate it into a pointwise norm bound. -/
theorem generalizedSinTheta_residual_le_of_gramLowerBound
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : (V ∈ Module.End.invtSubmodule A))
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hgram : GramLowerBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * ε * N (sinThetaEmbedding V
      (X.polarIsometry (hgram.injective hε))) ≤
      N (generalResidual A X M) := by
  exact generalizedSinTheta_residual_le_of_intervalGap
    N hA hV X hM hδ hε (hgram.lowerFrameBound) hgap

/-- **Davis--Kahan Theorem 6.1 in its permissive `sin Θ₀` form.**

The paper allows `sin Θ₀` to be any rectangular operator with the same complete
singular-value sequence as the canonical directed sine block.  Since every
rectangular unitarily invariant norm depends only on that sequence, the
canonical Gram-bound theorem transfers without loss. -/
theorem generalizedSinTheta0_residual_le_of_gramLowerBound
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : (V ∈ Module.End.invtSubmodule A))
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hgram : GramLowerBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ)
    (sinTheta0 : F →ₗ[𝕜] E)
    (hsin : sinTheta0.singularValues =
      (sinThetaEmbedding V
        (X.polarIsometry (hgram.injective hε))).singularValues) :
    δ * ε * N sinTheta0 ≤ N (generalResidual A X M) := by
  have hcanonical := generalizedSinTheta_residual_le_of_gramLowerBound
    N hA hV X hM hδ hε hgram hgap
  have hnorm : N sinTheta0 = N (sinThetaEmbedding V
      (X.polarIsometry (hgram.injective hε))) :=
    N.map_eq_of_singularValues_eq hsin
  rw [hnorm]
  exact hcanonical

/-- Compatibility specialization of Theorem 6.1 with the coordinate spectrum
inside `[a,b]` and the unwanted exact spectrum outside the enlarged interval.

The explicit injectivity argument is retained for callers of the earlier API;
the source-complete theorem above derives it from the positive lower frame
bound. -/
theorem generalizedSinTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : (V ∈ Module.End.invtSubmodule A))
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hMspec : Module.End.PointSpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : Module.End.PointSpectrumIn A Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ε * N (sinThetaEmbedding V (X.polarIsometry hX)) ≤
      N (generalResidual A X M) := by
  have htransport := lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    N V X hX hframe hε
  have hraw := complementaryTrialBlock_residual_le_of_intervalGap
    N hA hV X hM hδ (Or.inl ⟨hMspec, hAspec⟩)
  calc
    δ * ε * N (sinThetaEmbedding V (X.polarIsometry hX)) =
        δ * (ε * N (sinThetaEmbedding V (X.polarIsometry hX))) := by ring
    _ ≤ δ * N (complementaryTrialBlock V X) :=
      mul_le_mul_of_nonneg_left htransport hδ.le
    _ ≤ N (generalResidual A X M) := hraw

end DavisKahan.FiniteDimensional
end TauCeti
