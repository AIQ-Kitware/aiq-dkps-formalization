/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.RayleighRitz
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# Ritz compression and residual

Finite-dimensional compressions, invariant-pair residuals, Galerkin
orthogonality and covariance. The Frobenius decomposition and minimality
are supplied by TauCeti’s Rayleigh–Ritz API.

## Sources

Ritz compressions and their residuals are the numerical-analysis form of the
Davis--Kahan `sin Θ` theorem; the source argument is distilled in
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex` and
`prose/distilled_literature/DavisKahan1970_part_III.tex`.  The generic-trial-map
shape here is this library's, not the paper's.

## Provenance

This file was moved from
`DavisKahan/FiniteDimensional/Residual/Ritz.lean`
when the finite sin-Θ foundations moved into the staging layer.
TauCeti's independently developed Rayleigh–Ritz API supersedes the
original Frobenius proofs. The local linear-map formulas and covariance
lemmas also apply where the paper uses algebraic trial coordinates.

-/

public section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Compression of `A` to the isometric coordinate space of `X`. -/
@[expose]
noncomputable def compression (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] F :=
  X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap

/-- Residual of an approximate invariant pair represented by an isometric
embedding. -/
@[expose]
noncomputable def residual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M


/-- Galerkin/Ritz residual. -/
@[expose]
noncomputable def ritzResidual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] E :=
  residual A X (compression A X)

/-- Vanishing Ritz residual is equivalent to invariance of the represented
subspace.
-/
theorem ritzResidual_eq_zero_iff_reduces {A : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) :
    ritzResidual A X = 0 ↔ (X.toLinearMap.range ∈ Module.End.invtSubmodule A) := by
  constructor
  · intro hR x hx
    rcases hx with ⟨y, rfl⟩
    have hpoint := LinearMap.congr_fun hR y
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change A (X y) - X (compression A X y) = 0 at hpoint
    exact ⟨compression A X y, (sub_eq_zero.mp hpoint).symm⟩
  · intro hred
    ext y
    have hmem : A (X y) ∈ X.toLinearMap.range :=
      hred ⟨y, rfl⟩
    rcases hmem with ⟨z, hz⟩
    have hz' : A (X.toLinearMap y) = X.toLinearMap z := hz.symm
    have hcomp : compression A X y = z := by
      -- states the goal with the definition unfolded, in the shape the next step needs.
      change X.toLinearMap.adjoint (A (X.toLinearMap y)) = z
      rw [hz']
      have hleft := LinearMap.congr_fun X.adjoint_comp_self' z
      -- restates the hypothesis with the definition unfolded, which is the form the
      -- following step matches against.
      change X.toLinearMap.adjoint (X.toLinearMap z) = z at hleft
      exact hleft
    -- unfolds the named residual/compression so the following rewrite sees its
    -- definition; there is no `_apply` lemma for it to route through.
    change A (X.toLinearMap y) - X.toLinearMap (compression A X y) = 0
    rw [hcomp, hz', sub_self]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Residuals transform naturally under a unitary change of approximate
coordinates.
-/
theorem residual_comp_unitary (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) (V : F ≃ₗᵢ[𝕜] F) :
    residual A (X.comp V.toLinearIsometry)
        (V.symm.toLinearMap ∘ₗ M ∘ₗ V.toLinearMap) =
      residual A X M ∘ₗ V.toLinearMap := by
  ext x
  simp [residual, LinearMap.comp_apply]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- If `(X,M)` is invariant for `B`, its residual for `A` is exactly the
perturbation applied to `X`.
-/
theorem residual_eq_perturbation_comp {A B : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    residual A X M = (A - B) ∘ₗ X.toLinearMap := by
  -- states the goal with the definition unfolded, in the shape the next step needs.
  change A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M = (A - B) ∘ₗ X.toLinearMap
  rw [LinearMap.sub_comp, hBX]

/-- A unitarily invariant norm of the invariant-pair residual is bounded by
that of the ambient perturbation.
-/
theorem opNorm_residual_le_perturbation
    {A B : E →ₗ[𝕜] E} (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    UnitarilyInvariantSeminorm.opNorm 𝕜 F E (residual A X M) ≤
      ‖(A - B).toContinuousLinearMap‖ := by
  rw [residual_eq_perturbation_comp X M hBX,
    UnitarilyInvariantSeminorm.opNorm_apply]
  have hcomp :
      ((A - B) ∘ₗ X.toLinearMap).toContinuousLinearMap =
        (A - B).toContinuousLinearMap ∘L X.toLinearMap.toContinuousLinearMap := by
    ext x
    rfl
  have hX : ‖X.toLinearMap.toContinuousLinearMap‖ ≤ 1 := by
    refine X.toLinearMap.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (X.norm_map x)
  rw [hcomp]
  calc
    ‖(A - B).toContinuousLinearMap ∘L X.toLinearMap.toContinuousLinearMap‖
        ≤ ‖(A - B).toContinuousLinearMap‖ *
            ‖X.toLinearMap.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(A - B).toContinuousLinearMap‖ * 1 :=
      mul_le_mul_of_nonneg_left hX (norm_nonneg _)
    _ = ‖(A - B).toContinuousLinearMap‖ := mul_one _

end TauCeti
