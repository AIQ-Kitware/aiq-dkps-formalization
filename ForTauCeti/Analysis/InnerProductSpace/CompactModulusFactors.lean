/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SpectralProjectionFactors
public import ForTauCeti.Analysis.InnerProductSpace.SignedModulusProjection
public import ForTauCeti.Analysis.InnerProductSpace.CompactModulusFiber
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ParameterTopology

/-!
# Spectral factors of an entire compact fixed-modulus fiber

The self-adjoint roots of a compact positive modulus are the independent
orthogonal projections on its nonzero eigenspaces. The correspondence is
a homeomorphism for product topology on the factors and operator norm on
the roots. The kernel has no free factor. No separability is assumed.

## Provenance

New local proofs of classical spectral sign geometry for DKPS. No
historical priority or accepted roadmap ownership is asserted.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Independent nonzero spectral factors for a compact modulus.**
The eigenspaces are the actual ambient eigenspaces, so multiplicities
and zero-dimensional factors are retained literally. -/
theorem exists_compact_modulus_spectral_equiv
    (S : E →L[𝕜] E) (hS : S.IsPositive) (hSc : IsCompactOperator S) :
    let N := fun μ : {μ : 𝕜 // μ ≠ 0} => Module.End.eigenspace S.toLinearMap μ.val
    ∃ e : (∀ μ, {Q : N μ →L[𝕜] N μ // IsStarProjection Q}) ≃
        {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S},
      ∀ Q μ (x : N μ), (e Q).val x =
        μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := by
  classical
  let N := fun μ : {μ : 𝕜 // μ ≠ 0} => Module.End.eigenspace S.toLinearMap μ.val
  let X := ∀ μ, {Q : N μ →L[𝕜] N μ // IsStarProjection Q}
  let Y := {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S}
  have hzero (A : Y) (x : E) (hx : S x = 0) : A.val x = 0 := by
    apply norm_eq_zero.mp
    rw [← A.val.norm_modulus_apply, A.property.2, hx, norm_zero]
  have hatt (Q : X) : ∃ A : Y, ∀ μ (x : N μ), A.val x =
      μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := by
    let Qext (μ : 𝕜) : Module.End.eigenspace S.toLinearMap μ →L[𝕜]
        Module.End.eigenspace S.toLinearMap μ := if h : μ = 0 then 0 else (Q ⟨μ, h⟩).val
    have hQext (μ) : IsStarProjection (Qext μ) := by
      dsimp only [Qext]
      split_ifs with h
      · exact IsStarProjection.zero (Module.End.eigenspace S.toLinearMap μ →L[𝕜]
          Module.End.eigenspace S.toLinearMap μ)
      · exact (Q ⟨μ, h⟩).property
    obtain ⟨P, ⟨hP, hPS, hPx⟩, _⟩ := exists_unique_commuting_spectral_projection
      S hSc hS.isSelfAdjoint Qext hQext
    refine ⟨⟨((2 : 𝕜) • P - 1) * S,
      isSelfAdjoint_modulus_signed_projection S P hS hP hPS⟩, ?_⟩
    intro μ x
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change S (x : E) = μ.val • (x : E) at hx
    change ((2 : 𝕜) • P - 1) (S x) = _
    rw [hx, map_smul]
    have hPxx := hPx μ.val x
    simp only [Qext, dite_eq_right μ.property] at hPxx
    change μ.val • ((2 : 𝕜) • P x - (x : E)) = _
    rw [hPxx]
  let f : X → Y := fun Q => (hatt Q).choose
  have hf (Q : X) : ∀ μ (x : N μ), (f Q).val x =
      μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := (hatt Q).choose_spec
  have hinj : Function.Injective f := by
    intro Q Q' heq
    funext μ
    apply Subtype.ext
    ext x
    have h := (hf Q μ x).symm.trans
      ((congrArg (fun A : Y => A.val (x : E)) heq).trans (hf Q' μ x))
    have h₂ := congrArg (fun z : E => z + (x : E))
      (smul_right_injective E μ.property h)
    simp only [sub_add_cancel] at h₂
    exact smul_right_injective E (two_ne_zero : (2 : 𝕜) ≠ 0) h₂
  have hsurj : Function.Surjective f := by
    intro A
    obtain ⟨P, ⟨hP, hPS, _, hform⟩, _⟩ :=
      exists_unique_supported_sign_projection S A.val hS A.property.1 A.property.2
    have hinv (μ : {μ : 𝕜 // μ ≠ 0}) : ∀ x ∈ N μ, P x ∈ N μ := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change S x = μ.val • x at hx
      change S (P x) = μ.val • P x
      calc
        _ = P (S x) := (congrArg (fun B : E →L[𝕜] E => B x) hPS.eq).symm
        _ = _ := by rw [hx, map_smul]
    let Q : X := fun μ => ⟨P.restrict (hinv μ), hP.restrict_invariant (N μ) (hinv μ)⟩
    refine ⟨Q, Subtype.ext ?_⟩
    apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS.isSelfAdjoint
    intro μ x
    by_cases hμ : μ = 0
    · have hx : S (x : E) = 0 := by
        have hx := Module.End.mem_eigenspace_iff.mp x.property
        simpa only [hμ, zero_smul, ContinuousLinearMap.coe_coe] using hx
      rw [hzero (f Q) x hx, hzero A x hx]
    · rw [hf Q ⟨μ, hμ⟩ x, hform]
      have hx := Module.End.mem_eigenspace_iff.mp x.property
      change S (x : E) = μ • (x : E) at hx
      change μ • ((2 : 𝕜) • P x - (x : E)) = ((2 : 𝕜) • P - 1) (S x)
      rw [hx, map_smul]
      rfl
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- **Product topology is exactly the root norm topology.** The compact
fixed-modulus fiber is homeomorphic to the product of finite-dimensional
projection factors on all nonzero eigenspaces. The zero eigenspace is
fixed, even when it has arbitrary Hilbert dimension. -/
theorem exists_compact_modulus_spectral_homeomorph
    (S : E →L[𝕜] E) (hS : S.IsPositive) (hSc : IsCompactOperator S) :
    let N := fun μ : {μ : 𝕜 // μ ≠ 0} => Module.End.eigenspace S.toLinearMap μ.val
    ∃ e : (∀ μ, {Q : N μ →L[𝕜] N μ // IsStarProjection Q}) ≃ₜ
        {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S},
      ∀ Q μ (x : N μ), (e Q).val x =
        μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := by
  let N := fun μ : {μ : 𝕜 // μ ≠ 0} => Module.End.eigenspace S.toLinearMap μ.val
  let X := ∀ μ, {Q : N μ →L[𝕜] N μ // IsStarProjection Q}
  let Y := {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S}
  let (μ : {μ : 𝕜 // μ ≠ 0}) : FiniteDimensional 𝕜 (N μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hSc μ.val μ.property
  let : CompactSpace X := inferInstance
  let : CompactSpace Y := isCompact_iff_compactSpace.mp
    (isCompact_setOf_isSelfAdjoint_modulus_eq S hS hSc)
  obtain ⟨e, he⟩ := exists_compact_modulus_spectral_equiv S hS hSc
  have hrel (Q : X) (A : Y) : e Q = A ↔ ∀ μ (x : N μ), A.val x =
      μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := by
    constructor
    · rintro rfl
      exact he Q
    · intro h
      apply Subtype.ext
      apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS.isSelfAdjoint
      intro μ x
      by_cases hμ : μ = 0
      · have hz (B : Y) : B.val x = 0 := by
          apply norm_eq_zero.mp
          rw [← B.val.norm_modulus_apply, B.property.2]
          have hx := Module.End.mem_eigenspace_iff.mp x.property
          change S (x : E) = μ • (x : E) at hx
          simp only [hx, hμ, zero_smul, norm_zero]
        rw [hz (e Q), hz A]
      · exact (he Q ⟨μ, hμ⟩ x).trans (h ⟨μ, hμ⟩ x).symm
  have hgraph : IsClosed (Function.graph e) := by
    change IsClosed {z : X × Y | e z.1 = z.2}
    simp only [hrel, Set.ofPred_forall]
    apply isClosed_iInter
    intro μ
    apply isClosed_iInter
    intro x
    apply isClosed_eq
    · exact (continuous_subtype_val.comp continuous_snd).clm_apply continuous_const
    · have hc : Continuous (fun z : X × Y => (z.1 μ).val x) :=
        (continuous_subtype_val.comp ((continuous_apply μ).comp continuous_fst)).clm_apply
          continuous_const
      exact continuous_const.smul ((continuous_const.smul
        (continuous_subtype_val.comp hc)).sub continuous_const)
  have hf : Continuous e := continuous_of_isClosed_graph hgraph
  exact ⟨e.toHomeomorphOfContinuousClosed hf hf.isClosedMap, he⟩

end TauCeti
