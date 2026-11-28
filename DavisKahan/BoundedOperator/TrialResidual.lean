/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.BoundedOperator.Problem
public import DavisKahan.OperatorIdeal.CanonicalRealView
public import DavisKahan.SinTheta.FrameFactorization
public import DavisKahan.Sylvester.Spectrum
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.Analysis.OperatorIdeal.OperatorNorm
import TauCeti.Analysis.InnerProductSpace.RayleighRitz

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Trial residual and exact-range cross blocks

This file isolates the algebra shared by generalized tangent estimates,
reflection-defect residual estimates, and Ritz-pair perturbation theory.
For an isometric trial map `X`, the orthogonal projection onto its range is
`X X*`; consequently the ambient off-diagonal block factors through the trial
residual and `X*`.

`residual_eq_comp_subtypeL` is the companion identity for the other standard
trial map, the inclusion `P.subtypeL` of a closed subspace: when `P` is
invariant under `A`, the residual of `A + K` against the compression
`compressOperator P A` collapses to `K ∘L P.subtypeL`.  It is stated over an
arbitrary `RCLike` field and uses invariance alone, so it belongs here rather
than beside any one of its consumers.
-/

namespace TauCeti
namespace DavisKahan
namespace BoundedOperator

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The canonical residual of a closed trial subspace, viewed as a map from
that subspace into the ambient Hilbert space. -/
@[expose] noncomputable def trialResidualCore
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H :=
  Zᗮ.starProjection ∘L T ∘L Z.subtypeL

omit [CompleteSpace H] in
/-- The trial residual is the difference between the ambient action and the
lifted Ritz compression. -/
theorem trialResidualCore_eq_ritzDifference
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] :
    trialResidualCore T Z =
      T.sylvester (compressOperator Z T) Z.subtypeL := by
  rw [ContinuousLinearMap.sylvester_apply]
  apply ContinuousLinearMap.ext
  intro z
  change Zᗮ.starProjection (T (z : H)) =
    T (z : H) - (Z.subtypeL (Z.orthogonalProjectionOnto (T (z : H))))
  rw [Submodule.starProjection_orthogonal_val]
  rfl

omit [CompleteSpace H] in
/-- Every trial residual vector lies in the orthogonal complement of the trial
space. -/
theorem trialResidualCore_apply_mem_orthogonal
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] (z : Z) :
    trialResidualCore T Z z ∈ Zᗮ := by
  exact Zᗮ.starProjection_apply_mem _

/-! ### The residual of a subspace inclusion against an invariant compression -/

/-- **The paper's `R = (A + H) E₀ - E₀ A₀` equals `H E₀`.**

This is the Section 1 remark "`R`, left-multiplied by the isometry `(E₀⋆; E₁⋆)`,
gives the first column of `H`; or that `R = H E₀`", and it needs nothing beyond
invariance of `P` under the unperturbed operator: on `P` the compression `A₀` is
the honest restriction, so the two `A`-terms cancel.

Stated over an arbitrary `RCLike` field, with its own binders, because the real
Section 8 descent needs exactly this identity over `ℝ`; nothing in the argument
sees the scalars. -/
theorem residual_eq_comp_subtypeL {𝕜 : Type*} [RCLike 𝕜] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (A K : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (hPinv : ∀ x ∈ P, A x ∈ P) :
    (A + K).sylvester (compressOperator P A) P.subtypeL = K ∘L P.subtypeL := by
  rw [ContinuousLinearMap.sylvester_apply, compressOperator_eq_restrict_of_invariant A P hPinv]
  ext u
  simp [add_sub_cancel_left]

/-- The ambient complementary cross block of `A` relative to the range of an
isometric trial map. -/
@[expose]
noncomputable def isometricRangeCrossBlock
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (hX : IsometricEmbedding X) :
    H →L[ℂ] H := by
  letI := ContinuousLinearMap.hasOrthogonalProjection_range_of_isometry
    (AddMonoidHomClass.isometry_of_norm X hX)
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  exact Vᗮ.starProjection ∘L A ∘L V.starProjection

/-- The cross block factors exactly through any residual `A X - X M`.
The term involving `M` disappears because the complementary range projection
annihilates `X`. -/
theorem isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) :
    isometricRangeCrossBlock A X hX =
      ((by
        letI := ContinuousLinearMap.hasOrthogonalProjection_range_of_isometry
          (AddMonoidHomClass.isometry_of_norm X hX)
        let V : Submodule ℂ H := LinearMap.range X.toLinearMap
        exact Vᗮ.starProjection ∘L A.sylvester M X) : F →L[ℂ] H) ∘L X.adjoint := by
  have hIso : Isometry X := AddMonoidHomClass.isometry_of_norm X hX
  let := ContinuousLinearMap.hasOrthogonalProjection_range_of_isometry hIso
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  have hP : V.starProjection = X ∘L X.adjoint :=
    (ContinuousLinearMap.comp_adjoint_eq_starProjection_range hIso).symm
  change Vᗮ.starProjection ∘L A ∘L V.starProjection =
    (Vᗮ.starProjection ∘L A.sylvester M X) ∘L X.adjoint
  rw [hP, ContinuousLinearMap.starProjection_orthogonal_range_comp_sylvester A hIso M,
    ContinuousLinearMap.sylvester_compression A hIso]
  simp only [V, ContinuousLinearMap.comp_assoc]

/-- The exact-range cross block is bounded by the residual norm. -/
theorem norm_isometricRangeCrossBlock_le_residual
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) :
    ‖isometricRangeCrossBlock A X hX‖ ≤ ‖A.sylvester M X‖ := by
  let := ContinuousLinearMap.hasOrthogonalProjection_range_of_isometry
    (AddMonoidHomClass.isometry_of_norm X hX)
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint A X M hX]
  calc
    ‖(Vᗮ.starProjection ∘L A.sylvester M X) ∘L X.adjoint‖
        ≤ ‖Vᗮ.starProjection‖ * ‖A.sylvester M X‖ * ‖X.adjoint‖ := by
      calc
        ‖(Vᗮ.starProjection ∘L A.sylvester M X) ∘L X.adjoint‖
            ≤ ‖Vᗮ.starProjection ∘L A.sylvester M X‖ * ‖X.adjoint‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖Vᗮ.starProjection‖ * ‖A.sylvester M X‖) * ‖X.adjoint‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖A.sylvester M X‖ * 1 := by
      gcongr
      · exact Vᗮ.starProjection_norm_le
      · rw [ContinuousLinearMap.adjoint.norm_map]
        exact opNorm_le_one_of_isometry hX
    _ = ‖A.sylvester M X‖ := by ring

/-- Rectangular ideal membership of a residual implies membership of the exact
range cross block. -/
theorem isometricRangeCrossBlock_mem
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (A.sylvester M X)) :
    N.Mem (isometricRangeCrossBlock A X hX) := by
  let := ContinuousLinearMap.hasOrthogonalProjection_range_of_isometry
    (AddMonoidHomClass.isometry_of_norm X hX)
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint A X M hX]
  exact N.comp_mem Vᗮ.starProjection X.adjoint hR

-- The two-sided contraction estimate has to unify a triple composition against the
-- goal *through* `gaugeReal`, which is a reducible `abbrev` over
-- `(OperatorIdealFamily.gauge _).toReal`, so `isDefEq` unfolds the whole gauge chain on
-- both sides.  The neighbouring `comp_mem` call is cheap because it compares `Prop`s;
-- this one compares two real-valued gauge applications.  Explicit space arguments cut
-- the search but not enough.
set_option maxHeartbeats 1000000 in
/-- Rectangular ideal gauge of the exact-range cross block is bounded by the
trial residual gauge. -/
theorem gauge_isometricRangeCrossBlock_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (A.sylvester M X)) :
    N.gaugeReal (isometricRangeCrossBlock A X hX) ≤
      N.gaugeReal (A.sylvester M X) := by
  let := ContinuousLinearMap.hasOrthogonalProjection_range_of_isometry
    (AddMonoidHomClass.isometry_of_norm X hX)
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint A X M hX]
  refine N.gaugeReal_comp_le_of_contractions (E := F) (F := H) (G := H) (H := H)
    Vᗮ.starProjection X.adjoint hR
    Vᗮ.starProjection_norm_le ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact opNorm_le_one_of_isometry hX

end BoundedOperator
end DavisKahan
end TauCeti
