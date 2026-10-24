/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealStationarity
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientBlocks
import DavisKahan.FiniteDimensional.DirectRotation.RealTwoPhaseBlocks
import ForTauCeti.Analysis.InnerProductSpace.AnticommutingConjugation

/-!
# Small spectral blocks at real Schatten transport minima

On a positive gradient eigenspace, source reflection followed by ambient
conjugation is an isometric conjugation. The actual two-phase restriction
of a real stationary transporter consequently has complete small invariant
blocks for this conjugation, without supplied phase projections or bases.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.RealComplexification
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local notation "𝓔" => RealComplexification E

/-- At a real constrained local minimum, each positive submaximal gradient
level has a complete small invariant decomposition for the actual unitary
restriction and the source-induced conjugation. -/
theorem gradient_eigenspace_small_blocks_of_isLocalMinOn_real_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ 𝓔) [K.HasOrthogonalProjection]
    (hK : conjugateOperator K.starProjection = K.starProjection)
    (Q : 𝓔 →L[ℂ] 𝓔) (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * K.starProjection * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsLocalMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * K.starProjection * star W = Q ∧
        conjugateOperator W = W} (U : 𝓔 →L[ℂ] 𝓔))
    (g : ℝ) (hg : 0 < g)
    (hgm : g < p.toReal * phaseAmplitude p.toReal (criticalAngle p.toReal)) :
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).toLinearMap (g : ℂ)
    ∃ (V : L ≃ₗᵢ[ℂ] L) (J : L ≃ₗᵢ⋆[ℂ] L) (F : Finset (Submodule ℂ L)),
      (∀ x : L, (V x : 𝓔) = (U : 𝓔 →L[ℂ] 𝓔) x) ∧
      Function.Involutive J ∧
      (∀ x : L, (J x : 𝓔) = K.reflection (conjugation x)) ∧
      (∀ S ∈ F, S ≠ ⊥ ∧ Module.finrank ℂ S ≤ 2 ∧
        (∀ x ∈ S, V x ∈ S) ∧ (∀ x ∈ S, J x ∈ S)) ∧
      (F : Set (Submodule ℂ L)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ := by
  let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_real_transports
    p hp hp1 K.starProjection Q hP hK U hU htrans hmin
  have hR : (K.reflection : 𝓔 →L[ℂ] 𝓔) =
      (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hR] at hconj
  have hGR (x : 𝓔) : G (K.reflection x) = -K.reflection (G x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (K.reflection x)) hconj
    change K.reflection (G (K.reflection (K.reflection x))) = -G (K.reflection x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  have hRJ : conjugateOperator (K.reflection : 𝓔 →L[ℂ] 𝓔) = K.reflection := by
    rw [hR, conjugateOperator_sub, conjugateOperator_complex_smul,
      conjugateOperator_one, hK]
    change star (2 : ℂ) • K.starProjection - 1 = (2 : ℂ) • K.starProjection - 1
    rw [star_ofNat]
  have hRC (x : 𝓔) : K.reflection (conjugation x) = conjugation (K.reflection x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (conjugation x)) hRJ
    simpa only [conjugateOperator_apply, conjugation_involutive,
      LinearIsometryEquiv.coe_coe''] using h.symm
  have hUC (x : 𝓔) : (U : 𝓔 →L[ℂ] 𝓔) (conjugation x) =
      conjugation ((U : 𝓔 →L[ℂ] 𝓔) x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (conjugation x)) hU
    simpa only [conjugateOperator_apply, conjugation_involutive] using h.symm
  have hGC := schattenUnitaryGradient_apply_conjugation p.toReal
    (U : 𝓔 →L[ℂ] 𝓔) (canonicalConjugation (E := E)).toLinearEquiv.toLinearMap hUC
  obtain ⟨J, hJ, hJx⟩ := exists_eigenspace_conjugation_of_anticommuting_symmetries
    G.toLinearMap K.reflection K.reflection_involutive (canonicalConjugation (E := E))
    (fun x => conjugation_involutive x) hRC hGR hGC g
  obtain ⟨a, _, b, _, V, A, hA, hV, hrepr⟩ :=
    gradient_eigenspace_two_phase_representation p.toReal g hp1 hp2 hg hgm U
  obtain ⟨F, hF, hpair, hspan⟩ :=
    RealTransport.exists_orthogonal_blocks_of_two_phase_and_conjugation
      J.toLinearEquiv.toLinearMap J.isometry hJ A (V : _ →L[ℂ] _) hA
      (Complex.exp ((a : ℂ) * Complex.I))
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) hrepr
  refine ⟨V, J, F, hV, hJ, hJx, ?_, hpair, hspan⟩
  intro S hS
  obtain ⟨hS0, hdim, _, hVS, hJS⟩ := hF S hS
  refine ⟨hS0, hdim, ?_, ?_⟩
  · exact hVS
  · exact hJS

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
