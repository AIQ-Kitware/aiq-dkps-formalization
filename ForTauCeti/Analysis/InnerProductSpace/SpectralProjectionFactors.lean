/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactSpectralDecomposition
public import ForTauCeti.Analysis.InnerProductSpace.PairedProjectionFamily
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# Independent spectral projection factors of a compact self-adjoint operator

Every family of orthogonal projections on its actual eigenspaces extends
uniquely to a commuting orthogonal projection on the ambient Hilbert
space. Infinite families and an arbitrary-dimensional kernel are allowed.

## Provenance

Classical spectral direct-sum geometry, implemented locally for DKPS.
No historical priority or accepted roadmap ownership is asserted.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Eigenspaces of bounded operators on a Hilbert space are complete. -/
instance completeSpace_eigenspace (S : E →L[𝕜] E) (μ : 𝕜) :
    CompleteSpace (Module.End.eigenspace S.toLinearMap μ) :=
  (isClosed_eigenspace S μ).completeSpace_coe

omit [CompleteSpace E] in
/-- A bounded operator commuting with S preserves every S-eigenspace. -/
theorem mapsTo_eigenspace_of_commute (S G : E →L[𝕜] E) (h : Commute G S) (μ : 𝕜) :
    ∀ x ∈ Module.End.eigenspace S.toLinearMap μ,
      G x ∈ Module.End.eigenspace S.toLinearMap μ := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change S x = μ • x at hx
  change S (G x) = μ • G x
  calc
    _ = G (S x) := (congrArg (fun A : E →L[𝕜] E => A x) h.eq).symm
    _ = _ := by rw [hx, map_smul]

end ContinuousLinearMap

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Equality on all eigenspaces of a compact self-adjoint operator
determines a bounded operator, including on a nonseparable kernel. -/
theorem eq_of_eq_on_compact_selfAdjoint_eigenspaces
    (S : E →L[𝕜] E) (hSc : IsCompactOperator S) (hS : IsSelfAdjoint S)
    (A B : E →L[𝕜] E)
    (heq : ∀ μ (x : Module.End.eigenspace S.toLinearMap μ), A x = B x) : A = B := by
  have hle : (⨆ μ : 𝕜, Module.End.eigenspace S.toLinearMap μ) ≤ (A - B).ker := by
    refine iSup_le fun μ x hx => ?_
    exact sub_eq_zero.mpr (heq μ ⟨x, hx⟩)
  have hdense : (⨆ μ : 𝕜, Module.End.eigenspace S.toLinearMap μ).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hSc hS.isSymmetric)
  have hall := Submodule.topologicalClosure_minimal _ hle (A - B).isClosed_ker
  rw [hdense] at hall
  ext x
  exact sub_eq_zero.mp (hall (Submodule.mem_top : x ∈ (⊤ : Submodule 𝕜 E)))

/-- **Independent infinite spectral projection assembly.** Arbitrary
orthogonal projections on all eigenspaces extend uniquely to a commuting
ambient orthogonal projection. No ambient finite dimension is assumed. -/
theorem exists_unique_commuting_spectral_projection
    (S : E →L[𝕜] E) (hSc : IsCompactOperator S) (hS : IsSelfAdjoint S)
    (Q : ∀ μ : 𝕜, Module.End.eigenspace S.toLinearMap μ →L[𝕜]
      Module.End.eigenspace S.toLinearMap μ)
    (hQ : ∀ μ, IsStarProjection (Q μ)) :
    ∃! P : E →L[𝕜] E, IsStarProjection P ∧ Commute P S ∧
      ∀ μ (x : Module.End.eigenspace S.toLinearMap μ), P x = (Q μ x : E) := by
  let N := fun μ : 𝕜 => Module.End.eigenspace S.toLinearMap μ
  let M := (⨆ μ : 𝕜, (Q μ).range.map (N μ).subtype).topologicalClosure
  let : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hPx (μ : 𝕜) (x : N μ) : M.starProjection x = (Q μ x : E) := by
    apply M.eq_starProjection_of_mem_of_inner_eq_zero
    · apply Submodule.le_topologicalClosure
      exact (le_iSup (fun ν : 𝕜 => (Q ν).range.map (N ν).subtype) μ)
        (Submodule.mem_map_of_mem (show Q μ x ∈ (Q μ).range from ⟨x, rfl⟩))
    · intro y hy
      have horth : (⨆ ν : 𝕜, (Q ν).range.map (N ν).subtype) ≤
          (Submodule.span 𝕜 {(x : E) - (Q μ x : E)})ᗮ := by
        refine iSup_le fun ν => ?_
        rintro z ⟨z₀, hz₀, rfl⟩
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        by_cases hν : ν = μ
        · subst ν
          change ⟪x - Q μ x, z₀⟫_𝕜 = 0
          obtain ⟨_, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp (hQ μ)
          rw [show Q μ x = (Q μ).range.starProjection x from
            congrArg (fun B : N μ →L[𝕜] N μ => B x) heq]
          exact (Q μ).range.starProjection_inner_eq_zero x z₀ hz₀
        · exact hS.isSymmetric.orthogonalFamily_eigenspaces (Ne.symm hν) (x - Q μ x) z₀
      have hyorth : y ∈ (Submodule.span 𝕜 {(x : E) - (Q μ x : E)})ᗮ :=
        Submodule.topologicalClosure_minimal _ horth (Submodule.isClosed_orthogonal _) hy
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyorth
  have hcomm : Commute M.starProjection S := by
    apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS
    intro μ x
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    have hQx := Module.End.mem_eigenspace_iff.mp (Q μ x).property
    change S (x : E) = μ • (x : E) at hx
    change S (Q μ x : E) = μ • (Q μ x : E) at hQx
    change M.starProjection (S x) = S (M.starProjection x)
    rw [hx, map_smul, hPx, hQx]
  refine ⟨M.starProjection, ⟨isStarProjection_starProjection, hcomm, hPx⟩, ?_⟩
  rintro P ⟨_, _, hP⟩
  apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS
  intro μ x
  rw [hP, hPx]

/-- The full commuting projection set is the product of the unrestricted
projection sets on the actual eigenspaces. This is a set equivalence;
operator-norm topology on ambient projections is not product topology
when infinitely many nonzero eigenspaces occur. -/
theorem exists_commuting_spectral_projection_equiv
    (S : E →L[𝕜] E) (hSc : IsCompactOperator S) (hS : IsSelfAdjoint S) :
    let N := fun μ : 𝕜 => Module.End.eigenspace S.toLinearMap μ
    ∃ e : (∀ μ, {Q : N μ →L[𝕜] N μ // IsStarProjection Q}) ≃
        {P : E →L[𝕜] E // IsStarProjection P ∧ Commute P S},
      ∀ Q μ (x : N μ), (e Q).val x = ((Q μ).val x : E) := by
  classical
  let N := fun μ : 𝕜 => Module.End.eigenspace S.toLinearMap μ
  let X := ∀ μ, {Q : N μ →L[𝕜] N μ // IsStarProjection Q}
  let Y := {P : E →L[𝕜] E // IsStarProjection P ∧ Commute P S}
  have hatt (Q : X) : ∃ P : Y, ∀ μ (x : N μ), P.val x = ((Q μ).val x : E) := by
    obtain ⟨P, ⟨hP, hPS, hPx⟩, _⟩ := exists_unique_commuting_spectral_projection
      S hSc hS (fun μ => (Q μ).val) (fun μ => (Q μ).property)
    exact ⟨⟨P, hP, hPS⟩, hPx⟩
  let f : X → Y := fun Q => (hatt Q).choose
  have hf (Q : X) : ∀ μ (x : N μ), (f Q).val x = ((Q μ).val x : E) :=
    (hatt Q).choose_spec
  have hinj : Function.Injective f := by
    intro Q Q' heq
    funext μ
    apply Subtype.ext
    ext x
    exact (hf Q μ x).symm.trans
      ((congrArg (fun P : Y => P.val (x : E)) heq).trans (hf Q' μ x))
  have hsurj : Function.Surjective f := by
    intro P
    have hinv (μ) : ∀ x ∈ N μ, P.val x ∈ N μ := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change S x = μ • x at hx
      change S (P.val x) = μ • P.val x
      calc
        _ = P.val (S x) := (congrArg (fun A : E →L[𝕜] E => A x) P.property.2.eq).symm
        _ = _ := by rw [hx, map_smul]
    let Q : X := fun μ => ⟨P.val.restrict (hinv μ),
      P.property.1.restrict_invariant (N μ) (hinv μ)⟩
    refine ⟨Q, Subtype.ext ?_⟩
    apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS
    intro μ x
    exact hf Q μ x
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end TauCeti
