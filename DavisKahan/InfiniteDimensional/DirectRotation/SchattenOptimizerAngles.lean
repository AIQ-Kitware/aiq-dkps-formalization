/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenGradientKernel
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReflectionTransport

/-!
# Every Hilbert-space Schatten optimizer preserves principal sines

Classify the actual finite positive-gradient cutoffs and use reflection
commutation on the entire gradient kernel. Compact spectral completeness
then proves the ambient commutation identity. No prescribed spectral
block form or canonical-tail assumption is needed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every finite-cost local complex Schatten optimizer commutes with
the intrinsic sine-angle operator in arbitrary Hilbert dimension.
In particular unequal angle sectors cannot mix. -/
theorem commute_sinAngleOperator_of_schatten_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U) :
    Commute (U : E →L[ℂ] E) (K.sinAngleOperator L) := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let A := G.modulus
  let S := K.sinAngleOperator L
  have hGc : IsCompactOperator G := isCompactOperator_schattenUnitaryGradient p.toReal hp1 U
    (by
      apply OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
      rw [← neg_sub 1 (U : E →L[ℂ] E), OperatorIdealFamily.gauge_neg]
      exact hfinite)
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = G.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus G n)
    rw [hseq]
    exact hGc.tendsto_singularValue
  have hlocal_commutes (M : Submodule ℂ E) [M.HasOrthogonalProjection] [CompleteSpace M]
      [(K.comap M.subtype).HasOrthogonalProjection]
      [(L.comap M.subtype).HasOrthogonalProjection]
      (hK : M.IsReducing K.starProjection.toLinearMap)
      (hL : M.IsReducing L.starProjection.toLinearMap)
      (V : M ≃ₗᵢ[ℂ] M) (hV : ∀ x : M, (V x : E) = U x)
      (hVS : Commute (V : M →L[ℂ] M)
        ((K.comap M.subtype).sinAngleOperator (L.comap M.subtype))) :
      ∀ x ∈ M, U (S x) = S (U x) := by
    intro x hx
    let x₀ : M := ⟨x, hx⟩
    let S₀ := (K.comap M.subtype).sinAngleOperator (L.comap M.subtype)
    have hS₀ (y : M) : (S₀ y : E) = S (y : E) :=
      K.sinAngleOperator_comap_subtype_apply_of_invariant L M
        hK.mem_invtSubmodule hL.mem_invtSubmodule y
    calc
      _ = U (S₀ x₀ : E) := congrArg U (hS₀ x₀).symm
      _ = (V (S₀ x₀) : E) := (hV _).symm
      _ = (S₀ (V x₀) : E) :=
        congrArg Subtype.val (congrArg (fun B : M →L[ℂ] M => B x₀) hVS.eq)
      _ = S (V x₀ : E) := hS₀ _
      _ = _ := congrArg S (hV x₀)
  rw [commute_iff_eq]
  apply eq_of_eq_on_ker_and_positive_eigenSpans hAc G.isSelfAdjoint_modulus
    G.isPositive_modulus.re_inner_nonneg_left
  · rw [show A.ker = G.ker from G.ker_modulus]
    let Z := G.ker
    let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
    let := L.hasOrthogonalProjection_comap_subtype_of_complete Z
    obtain ⟨V, hV, _, hself⟩ :=
      exists_selfAdjoint_unitary_restriction_schatten_gradient_kernel p.toReal hp1 hp2 U
    have hK : Z.IsReducing K.starProjection.toLinearMap :=
      K.isReducing_ker_of_reflection_conjugate_eq_neg G
        (isSelfAdjoint_schattenUnitaryGradient _ _)
        (gradient_reflection_conjugate_eq_neg_of_schatten_isLocalMinOn_complex p hp hp1 K L U hmap hfinite hmin)
    have hL : Z.IsReducing L.starProjection.toLinearMap := by
      apply (L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule Z).mpr
      intro x hx
      change L.starProjection x ∈ Z
      have h := K.starProjection_map_mem_of_isometry_restriction Z U V hV
        hK.mem_invtSubmodule x hx
      simpa only [hmap] using h
    have hlocal := K.map_comap_subtype_of_isometry_restriction L Z U V hmap hV
    have hconj : (V : Z →L[ℂ] Z) * (K.comap Z.subtype).starProjection *
        star (V : Z →L[ℂ] Z) = (L.comap Z.subtype).starProjection := by
      rw [show star (V : Z →L[ℂ] Z) = (V.symm : Z →L[ℂ] Z) from V.adjoint_eq_symm]
      apply ContinuousLinearMap.ext
      intro x
      change V ((K.comap Z.subtype).starProjection (V.symm x)) =
        (L.comap Z.subtype).starProjection x
      have h := Submodule.starProjection_map_apply V (K.comap Z.subtype) x
      change ((K.comap Z.subtype).map V.toLinearMap).starProjection x = _ at h
      simpa only [hlocal] using h.symm
    have hVS := (K.comap Z.subtype).commute_sinAngleOperator_of_selfAdjoint_transport
      (L.comap Z.subtype) V hself hconj
    exact hlocal_commutes Z hK hL V hV hVS
  · intro ε hε
    obtain ⟨hM, hK, hL, _, _, V, hV, _, hlocal, hVmin⟩ :=
      exists_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex p hp hp1 hp2 K L U hmap hfinite hmin ε hε
    let M := eigenSpan A (Set.Ioi ε)
    let : FiniteDimensional ℂ M := hM
    let V' := Unitary.linearIsometryEquiv.symm V
    have hmin' : IsMinOn
        (fun W : M →L[ℂ] M => UnitarilyInvariantSeminorm.schatten ℂ M M p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (M →L[ℂ] M) ∧
          W * (K.comap M.subtype).starProjection * star W = (L.comap M.subtype).starProjection}
        (V : M →L[ℂ] M) := by
      intro W hW
      exact hVmin (Unitary.linearIsometryEquiv ⟨W, hW.1⟩)
        ((map_eq_iff_conjugate_starProjection_complex _ _ ⟨W, hW.1⟩).mpr hW.2)
    have hVS := commute_sinAngleOperator_of_isLocalMinOn_transports_complex p hp hp1 hp2
      (K.comap M.subtype) (L.comap M.subtype) V' hlocal hmin'.isLocalMinOn
    exact hlocal_commutes M hK hL V hV hVS

/-- Global optimality implies the stronger local angle rigidity. -/
theorem commute_sinAngleOperator_of_schatten_minimal
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E))) :
    Commute (U : E →L[ℂ] E) (K.sinAngleOperator L) := by
  exact commute_sinAngleOperator_of_schatten_isLocalMinOn_complex p hp hp1 hp2 K L U hmap hfinite
    (show IsMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U
      from fun T hT => hmin T hT).isLocalMinOn

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
