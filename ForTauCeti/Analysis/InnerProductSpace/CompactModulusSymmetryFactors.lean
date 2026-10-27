/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactModulusFactors

/-!
# Local symmetry constraints on independent modulus factors

Commutation with G and anticommutation with J become independent
projection equations on each nonzero eigenspace of the compact modulus.
G and J must preserve that spectral decomposition. Neither is assumed
invertible, so zero-cosine defect blocks are retained.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The exact local equations for a signed modulus root. Commutation
with G becomes commutation of the sign projection; oddness for J
becomes exchange of the projection with its complement. -/
theorem compact_modulus_spectral_symmetries_iff
    (S : E →L[𝕜] E) (hS : S.IsPositive) (hSc : IsCompactOperator S)
    (G J : E →L[𝕜] E) (hGS : Commute G S) (hJS : Commute J S)
    (A : E →L[𝕜] E) (hmod : A.modulus = S)
    (P : ∀ μ : {μ : 𝕜 // μ ≠ 0}, Module.End.eigenspace S.toLinearMap μ.val →L[𝕜]
      Module.End.eigenspace S.toLinearMap μ.val)
    (hform : ∀ (μ : {μ : 𝕜 // μ ≠ 0})
      (x : Module.End.eigenspace S.toLinearMap μ.val),
      A x = μ.val • ((2 : 𝕜) • (P μ x : E) - (x : E))) :
    let g := fun μ : {μ : 𝕜 // μ ≠ 0} =>
      G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G hGS μ.val)
    let j := fun μ : {μ : 𝕜 // μ ≠ 0} =>
      J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J hJS μ.val)
    (Commute A G ∧ A * J + J * A = 0) ↔
      ∀ μ, Commute (P μ) (g μ) ∧ P μ * j μ + j μ * P μ = j μ := by
  let N := fun μ : {μ : 𝕜 // μ ≠ 0} => Module.End.eigenspace S.toLinearMap μ.val
  let g := fun μ : {μ : 𝕜 // μ ≠ 0} =>
    G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G hGS μ.val)
  let j := fun μ : {μ : 𝕜 // μ ≠ 0} =>
    J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J hJS μ.val)
  have hzero (x : E) (hx : S x = 0) : A x = 0 := by
    apply norm_eq_zero.mp
    rw [← A.norm_modulus_apply, hmod, hx, norm_zero]
  have hcommcalc (μ : {μ : 𝕜 // μ ≠ 0}) (x : N μ) :
      (A * G - G * A) x = (2 * μ.val) •
        (((P μ * g μ - g μ * P μ) x : N μ) : E) := by
    change A (g μ x : E) - G (A x) = _
    rw [hform μ (g μ x), hform μ x, map_smul, map_sub, map_smul]
    change μ.val • ((2 : 𝕜) • (P μ (g μ x) : E) - (g μ x : E)) -
      μ.val • ((2 : 𝕜) • (g μ (P μ x) : E) - (g μ x : E)) =
      (2 * μ.val) • ((P μ (g μ x) : E) - (g μ (P μ x) : E))
    module
  have hoddcalc (μ : {μ : 𝕜 // μ ≠ 0}) (x : N μ) :
      (A * J + J * A) x = (2 * μ.val) •
        (((P μ * j μ + j μ * P μ - j μ) x : N μ) : E) := by
    change A (j μ x : E) + J (A x) = _
    rw [hform μ (j μ x), hform μ x, map_smul, map_sub, map_smul]
    change μ.val • ((2 : 𝕜) • (P μ (j μ x) : E) - (j μ x : E)) +
      μ.val • ((2 : 𝕜) • (j μ (P μ x) : E) - (j μ x : E)) =
      (2 * μ.val) • ((P μ (j μ x) : E) + (j μ (P μ x) : E) - (j μ x : E))
    module
  constructor
  · rintro ⟨hc, ho⟩ μ
    constructor
    · ext x
      have hz : (A * G - G * A) x = 0 := by rw [hc.eq, sub_self]; rfl
      rw [hcommcalc] at hz
      have ht := (smul_eq_zero.mp hz).resolve_left (mul_ne_zero two_ne_zero μ.property)
      exact sub_eq_zero.mp ht
    · ext x
      have hz : (A * J + J * A) x = 0 := by rw [ho]; rfl
      rw [hoddcalc] at hz
      have ht := (smul_eq_zero.mp hz).resolve_left (mul_ne_zero two_ne_zero μ.property)
      exact sub_eq_zero.mp ht
  · intro h
    have hc : A * G - G * A = 0 := by
      apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS.isSelfAdjoint
      intro μ x
      by_cases hμ : μ = 0
      · have hx : S (x : E) = 0 := by
          have hx := Module.End.mem_eigenspace_iff.mp x.property
          simpa only [hμ, zero_smul, ContinuousLinearMap.coe_coe] using hx
        have hGx : S (G x) = 0 := by
          have h := congrArg (fun B : E →L[𝕜] E => B (x : E)) hGS.eq
          change G (S x) = S (G x) at h
          rw [hx, map_zero] at h
          exact h.symm
        change A (G x) - G (A x) = 0
        rw [hzero _ hGx, hzero _ hx, map_zero, sub_self]
      · rw [hcommcalc ⟨μ, hμ⟩ x, (h ⟨μ, hμ⟩).1.eq, sub_self]
        simp only [zero_apply, Submodule.coe_zero, smul_zero]
    refine ⟨sub_eq_zero.mp hc, ?_⟩
    apply eq_of_eq_on_compact_selfAdjoint_eigenspaces S hSc hS.isSelfAdjoint
    intro μ x
    by_cases hμ : μ = 0
    · have hx : S (x : E) = 0 := by
        have hx := Module.End.mem_eigenspace_iff.mp x.property
        simpa only [hμ, zero_smul, ContinuousLinearMap.coe_coe] using hx
      have hJx : S (J x) = 0 := by
        have h := congrArg (fun B : E →L[𝕜] E => B (x : E)) hJS.eq
        change J (S x) = S (J x) at h
        rw [hx, map_zero] at h
        exact h.symm
      change A (J x) + J (A x) = 0
      rw [hzero _ hJx, hzero _ hx, map_zero, add_zero]
    · rw [hoddcalc ⟨μ, hμ⟩ x, (h ⟨μ, hμ⟩).2, sub_self]
      simp only [zero_apply, Submodule.coe_zero, smul_zero]

/-- Independent projection choices on one nonzero modulus eigenspace,
commuting with G and exchanged with their complement by J. -/
@[expose] def spectralSignProjectionFactors
    (S G J : E →L[𝕜] E) (hGS : Commute G S) (hJS : Commute J S)
    (μ : {μ : 𝕜 // μ ≠ 0}) :
    Set (Module.End.eigenspace S.toLinearMap μ.val →L[𝕜]
      Module.End.eigenspace S.toLinearMap μ.val) :=
  let g := G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G hGS μ.val)
  let j := J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J hJS μ.val)
  {P | IsStarProjection P ∧ Commute P g ∧ P * j + j * P = j}

/-- **Complete independent spectral factors with symmetries.** All
self-adjoint roots of S commuting with G and odd for J form exactly the
product of the local compatible projection spaces. This includes the
zero operator G on any block and the full fixed kernel of S. -/
theorem exists_compact_modulus_symmetry_spectral_homeomorph
    (S : E →L[𝕜] E) (hS : S.IsPositive) (hSc : IsCompactOperator S)
    (G J : E →L[𝕜] E) (hGS : Commute G S) (hJS : Commute J S) :
    ∃ e : (∀ μ, spectralSignProjectionFactors S G J hGS hJS μ) ≃ₜ
        {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S ∧
          Commute A G ∧ A * J + J * A = 0},
      ∀ Q (μ : {μ : 𝕜 // μ ≠ 0})
        (x : Module.End.eigenspace S.toLinearMap μ.val), (e Q).val x =
        μ.val • ((2 : 𝕜) • ((Q μ).val x : E) - (x : E)) := by
  let N := fun μ : {μ : 𝕜 // μ ≠ 0} => Module.End.eigenspace S.toLinearMap μ.val
  let X := ∀ μ, {P : N μ →L[𝕜] N μ // IsStarProjection P}
  let X' := ∀ μ, spectralSignProjectionFactors S G J hGS hJS μ
  let Y := {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S}
  let Y' := {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S ∧
    Commute A G ∧ A * J + J * A = 0}
  obtain ⟨e, he⟩ := exists_compact_modulus_spectral_homeomorph S hS hSc
  let forget (Q : X') : X := fun μ => ⟨(Q μ).val, (Q μ).property.1⟩
  have hrel (Q : X) :
      (∀ μ, (Q μ).val ∈ spectralSignProjectionFactors S G J hGS hJS μ) ↔
        Commute (e Q).val G ∧ (e Q).val * J + J * (e Q).val = 0 := by
    have h := compact_modulus_spectral_symmetries_iff S hS hSc G J hGS hJS
      (e Q).val (e Q).property.2 (fun μ => (Q μ).val) (he Q)
    constructor
    · intro hQ
      exact h.mpr (fun μ => (hQ μ).2)
    · intro hQ μ
      exact ⟨(Q μ).property, h.mp hQ μ⟩
  let f (Q : X') : Y' :=
    ⟨(e (forget Q)).val, (e (forget Q)).property.1, (e (forget Q)).property.2,
      (hrel (forget Q)).mp (fun μ => (Q μ).property)⟩
  let base (A : Y') : Y := ⟨A.val, A.property.1, A.property.2.1⟩
  have hback (A : Y') (μ) : (e.symm (base A) μ).val ∈
      spectralSignProjectionFactors S G J hGS hJS μ := by
    apply (hrel (e.symm (base A))).mpr
    simpa only [e.apply_symm_apply] using A.property.2.2
  let b (A : Y') : X' := fun μ => ⟨(e.symm (base A) μ).val, hback A μ⟩
  let e' : X' ≃ Y' :=
    { toFun := f
      invFun := b
      left_inv := by
        intro Q
        funext μ
        apply Subtype.ext
        change (e.symm (e (forget Q)) μ).val = (Q μ).val
        rw [e.symm_apply_apply]
      right_inv := by
        intro A
        apply Subtype.ext
        change (e (e.symm (base A))).val = A.val
        rw [e.apply_symm_apply] }
  have hcforget : Continuous forget := by
    apply continuous_pi
    intro μ
    exact (continuous_subtype_val.comp (continuous_apply μ)).subtype_mk _
  have hcbase : Continuous base := continuous_subtype_val.subtype_mk _
  have hcf : Continuous f :=
    (continuous_subtype_val.comp (e.continuous.comp hcforget)).subtype_mk _
  have hcb : Continuous b := by
    apply continuous_pi
    intro μ
    exact (continuous_subtype_val.comp
      ((continuous_apply μ).comp (e.symm.continuous.comp hcbase))).subtype_mk _
  refine ⟨⟨e', hcf, hcb⟩, ?_⟩
  intro Q μ x
  exact he (forget Q) μ x

end TauCeti
