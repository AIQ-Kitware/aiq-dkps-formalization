/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Halmos.GenericReconstruction
import ForTauCeti.Analysis.InnerProductSpace.CompactSelfAdjointClassification

/-!
# Davis--Kahan 1970, Corollary 3.1: the compact case

When `P_U P_V P_U` is compact the angle operator is a compact positive operator
with trivial kernel, and such an operator is determined up to unitary
equivalence by its eigenvalue list with multiplicity.  So in the compact case
the invariant of Theorem 3.1 collapses to *numbers*: the four elementary Halmos
multiplicities, and the dimension of each eigenspace of `cos²Θ`.

The eigenvalue list is recorded here coordinate-free, as
`μ ↦ dim ker(cos²Θ - μ)`, rather than as a decreasing sequence.  The two carry
the same information — for a compact positive operator with trivial kernel the
nonzero eigenvalues have finite multiplicity and accumulate only at `0`, so the
dimension function is exactly the multiset of the decreasing list — and the
dimension function needs no ordering theory to state.

The paper's "including possible zero multiplicity" bookkeeping is not lost: a
zero or right angle is an *elementary* summand (`U ⊓ V`, `U ⊓ Vᗮ`, `Uᗮ ⊓ V`,
`Uᗮ ⊓ Vᗮ`), and those are carried by the four `Nonempty` fields, separately from
the generic angle data.

## Main results

* `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.SameCompactAngleData`
* `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open Frontier
open Module (finrank)
open Module.End (eigenspace)

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The angle operator is compact with trivial kernel -/

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The cosine block is the compression of `P_U P_V P_U` to the `U`-half.

On the `U`-half the outer `P_U` is the identity and the outer projection onto
the half agrees with `P_U`, so the two compressions coincide.  This is the form
in which the paper's compactness hypothesis reaches the angle operator. -/
theorem genericCosineBlock_eq_compress_halmos :
    genericCosineBlock U V =
      DavisKahanExt.compressOperator (genericLeftHalf U V)
        (projection U ∘L projection V ∘L projection U) := by
  refine ContinuousLinearMap.ext fun m => ?_
  apply Subtype.ext
  have hmU : U.starProjection (m : H) = (m : H) :=
    Submodule.starProjection_eq_self_iff.mpr m.2.1
  have hgen : V.starProjection (m : H) ∈ halmosGenericPart U V :=
    projection_mem_halmosGenericPart_right U V m.2.2
  have hMV : (genericLeftHalf U V).starProjection (V.starProjection (m : H)) =
      U.starProjection (V.starProjection (m : H)) :=
    starProjection_genericLeftHalf_of_mem_generic U V hgen
  have hLHS : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
      (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := by
    simp [genericCosineBlock, DavisKahanExt.compressOperator]
  have hRHS : ((DavisKahanExt.compressOperator (genericLeftHalf U V)
      (projection U ∘L projection V ∘L projection U) m : genericLeftHalf U V) : H) =
      (genericLeftHalf U V).starProjection
        (U.starProjection (V.starProjection (U.starProjection (m : H)))) := by
    simp [DavisKahanExt.compressOperator]
  rw [hLHS, hRHS, hmU, ← hMV,
    Submodule.starProjection_eq_self_iff.mpr
      ((genericLeftHalf U V).starProjection_apply_mem _)]

/-- **The angle operator is compact** when `P_U P_V P_U` is. -/
theorem isCompactOperator_genericCosineBlock
    (hc : IsCompactOperator (projection U ∘L projection V ∘L projection U)) :
    IsCompactOperator (genericCosineBlock U V) := by
  rw [genericCosineBlock_eq_compress_halmos, DavisKahanExt.compressOperator]
  exact (hc.comp_clm (genericLeftHalf U V).subtypeL).clm_comp
    (genericLeftHalf U V).orthogonalProjectionOnto

/-- **The angle operator has trivial kernel.**  Generic position: its quadratic
form is `‖P_V m‖²`, which vanishes only at `0`. -/
theorem eigenspace_genericCosineBlock_zero :
    eigenspace (genericCosineBlock U V).toLinearMap 0 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro m hm
  by_contra hne
  have hzero : genericCosineBlock U V m = 0 := by
    have := Module.End.mem_eigenspace_iff.mp hm
    simpa using this
  have hpos := re_inner_genericCosineBlock_pos U V hne
  rw [hzero] at hpos
  simp at hpos

end OneSpace

/-! ## The compact classification -/

section TwoSpaces

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Davis--Kahan 1970 Corollary 3.1's invariant.**  The four elementary Halmos
multiplicities, together with the multiplicity of every angle: the paper's
decreasing eigenvalue list, written as a dimension function. -/
structure SameCompactAngleData : Prop where
  common : Nonempty (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
  angleMultiplicity : ∀ μ : 𝕜,
    finrank 𝕜 (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ) =
      finrank 𝕜 (eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ)

/-- A unitary intertwining two operators carries eigenspaces onto eigenspaces,
hence preserves their dimensions. -/
theorem finrank_eigenspace_eq_of_intertwiner
    {W : genericLeftHalf U₁ V₁ ≃ₗᵢ[𝕜] genericLeftHalf U₂ V₂}
    (hW : ∀ m, W (genericCosineBlock U₁ V₁ m) = genericCosineBlock U₂ V₂ (W m))
    (μ : 𝕜) :
    finrank 𝕜 (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ) =
      finrank 𝕜 (eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ) := by
  have hsymm : ∀ y, W.symm (genericCosineBlock U₂ V₂ y) =
      genericCosineBlock U₁ V₁ (W.symm y) := by
    intro y
    apply W.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hW, LinearIsometryEquiv.apply_symm_apply]
  have hfwd : ∀ m : genericLeftHalf U₁ V₁,
      m ∈ eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ →
      W m ∈ eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ := by
    intro m hm
    have hm' : genericCosineBlock U₁ V₁ m = μ • m := Module.End.mem_eigenspace_iff.mp hm
    rw [Module.End.mem_eigenspace_iff]
    show genericCosineBlock U₂ V₂ (W m) = μ • W m
    rw [← hW m, hm', map_smul]
  have hbwd : ∀ y : genericLeftHalf U₂ V₂,
      y ∈ eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ →
      W.symm y ∈ eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ := by
    intro y hy
    have hy' : genericCosineBlock U₂ V₂ y = μ • y := Module.End.mem_eigenspace_iff.mp hy
    rw [Module.End.mem_eigenspace_iff]
    show genericCosineBlock U₁ V₁ (W.symm y) = μ • W.symm y
    rw [← hsymm y, hy', map_smul]
  have hmap : (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ).map
      (W.toLinearEquiv : genericLeftHalf U₁ V₁ →ₗ[𝕜] genericLeftHalf U₂ V₂) =
      eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact hfwd m hm
    · intro y hy
      exact ⟨W.symm y, hbwd y hy, by simp⟩
  have hinj : Function.Injective
      (W.toLinearEquiv : genericLeftHalf U₁ V₁ →ₗ[𝕜] genericLeftHalf U₂ V₂) :=
    W.injective
  have hequiv := Submodule.equivMapOfInjective
    (W.toLinearEquiv : genericLeftHalf U₁ V₁ →ₗ[𝕜] genericLeftHalf U₂ V₂) hinj
    (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ)
  rw [← hmap]
  exact hequiv.finrank_eq

variable [Algebra ℝ (genericLeftHalf U₁ V₁ →L[𝕜] genericLeftHalf U₁ V₁)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₁ V₁ →L[𝕜] genericLeftHalf U₁ V₁)]
  [ContinuousFunctionalCalculus ℝ (genericLeftHalf U₁ V₁ →L[𝕜] genericLeftHalf U₁ V₁)
    IsSelfAdjoint]
variable [Algebra ℝ (genericLeftHalf U₂ V₂ →L[𝕜] genericLeftHalf U₂ V₂)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₂ V₂ →L[𝕜] genericLeftHalf U₂ V₂)]
  [ContinuousFunctionalCalculus ℝ (genericLeftHalf U₂ V₂ →L[𝕜] genericLeftHalf U₂ V₂)
    IsSelfAdjoint]

/-- **Davis--Kahan 1970, Corollary 3.1.**

When `P_U P_V P_U` is compact on both sides, two ordered pairs of subspaces are
unitarily equivalent as pairs exactly when their four elementary Halmos summands
are isometric and every angle has the same multiplicity.

This is Theorem 3.1 with the operator invariant replaced by numbers.  The
replacement is legitimate precisely because compactness makes the angle operator
one for which the eigenvalue list *is* a complete invariant. -/
theorem pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    (hc₁ : IsCompactOperator (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hc₂ : IsCompactOperator (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    Frontier.PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameCompactAngleData U₁ V₁ U₂ V₂ := by
  constructor
  · intro h
    obtain ⟨hc, hs, ht, he, _⟩ := sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
    obtain ⟨W, hW⟩ := exists_cosineBlockEquiv_of_pairEquiv U₁ V₁ U₂ V₂ h
    exact ⟨hc, hs, ht, he, finrank_eigenspace_eq_of_intertwiner U₁ V₁ U₂ V₂ hW⟩
  · rintro ⟨⟨ec⟩, ⟨es⟩, ⟨et⟩, ⟨ee⟩, hmult⟩
    obtain ⟨W, hW⟩ :=
      TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq
        (isCompactOperator_genericCosineBlock U₁ V₁ hc₁)
        (isSelfAdjoint_genericCosineBlock U₁ V₁)
        (isCompactOperator_genericCosineBlock U₂ V₂ hc₂)
        (isSelfAdjoint_genericCosineBlock U₂ V₂)
        (eigenspace_genericCosineBlock_zero U₁ V₁)
        (eigenspace_genericCosineBlock_zero U₂ V₂) hmult
    exact pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv U₁ V₁ U₂ V₂ W hW
      ec es et ee

end TwoSpaces

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
