/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealStationarity
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientBlocks
public import DavisKahan.FiniteDimensional.DirectRotation.RealTwoPhaseBlocks
public import DavisKahan.FiniteDimensional.DirectRotation.RealBlockRank
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingConjugation

/-!
# Small spectral blocks at real Schatten transport minima

On a positive gradient eigenspace, source reflection followed by ambient
conjugation is an isometric conjugation. The actual two-phase restriction
of a real stationary transporter consequently has complete small invariant
blocks for this conjugation, without supplied phase projections or bases.
Doubling by source reflection descends their complete orthogonal family to
the original real space, with real block dimensions at most four.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local notation "𝓔" => RealComplexification E

/-- At a real constrained local minimum, each positive gradient
level has a complete small invariant decomposition for the actual unitary
restriction and the source-induced conjugation. Doubling these blocks gives
a complete orthogonal real invariant decomposition of the level together
with its reflected negative level. -/
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
    (hgm : g ≤ p.toReal * phaseAmplitude p.toReal (criticalAngle p.toReal)) :
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).toLinearMap (g : ℂ)
    ∃ (V : L ≃ₗᵢ[ℂ] L) (J : L ≃ₗᵢ⋆[ℂ] L) (F : Finset (Submodule ℂ L)),
      (∀ x : L, (V x : 𝓔) = (U : 𝓔 →L[ℂ] 𝓔) x) ∧
      Function.Involutive J ∧
      (∀ x : L, (J x : 𝓔) = K.reflection (conjugation x)) ∧
      (∀ S ∈ F, S ≠ ⊥ ∧ Module.finrank ℂ S ≤ 2 ∧
        (∀ x ∈ S, V x ∈ S) ∧ (∀ x ∈ S, J x ∈ S)) ∧
      (F : Set (Submodule ℂ L)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ ∧
      (∃ H : Finset (Submodule ℝ E),
        (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
          (∀ x ∈ N, realify (U : 𝓔 →L[ℂ] 𝓔) x ∈ N) ∧
          (∀ x ∈ N, realify (K.reflection : 𝓔 →L[ℂ] 𝓔) x ∈ N) ∧
          ((Module.finrank ℝ N = 2 ∧
              Module.finrank ℝ ↥(N ⊓ RealTransport.realSubmodule K) = 1) ∨
            (Module.finrank ℝ N = 4 ∧
              Module.finrank ℝ ↥(N ⊓ RealTransport.realSubmodule K) = 2))) ∧
        (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧
        complexifySubmodule (H.sup id) = L ⊔ L.map K.reflection.toLinearMap) := by
  let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
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
  obtain ⟨a, b, V, A, hA, hV, hrepr⟩ :
      ∃ (a b : ℝ) (V : L ≃ₗᵢ[ℂ] L) (A : L →L[ℂ] L),
        IsStarProjection A ∧
        (∀ x : L, (V x : 𝓔) = (U : 𝓔 →L[ℂ] 𝓔) x) ∧
        (V : L →L[ℂ] L) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
          (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A := by
    rcases lt_or_eq_of_le hgm with hlt | heq
    · obtain ⟨a, _, b, _, V, A, hA, hV, hrepr⟩ :=
        gradient_eigenspace_two_phase_representation p.toReal g hp1 hp2 hg hlt U
      exact ⟨a, b, V, A, hA, hV, hrepr⟩
    · subst g
      have hcritical := signed_critical_gradient_eigenspace_representation
        p.toReal 1 hp1 hp2 (Or.inl rfl) U
      dsimp only at hcritical
      rw [one_mul] at hcritical
      obtain ⟨V, hV, hrepr⟩ := hcritical
      refine ⟨criticalAngle p.toReal, criticalAngle p.toReal, V, 0, ?_, hV, ?_⟩
      · exact IsStarProjection.zero (L →L[ℂ] L)
      · rw [sub_self, zero_smul ℂ (0 : L →L[ℂ] L), add_zero]
        simpa only [one_mul] using hrepr
  obtain ⟨F, hF, hpair, hspan⟩ :=
    RealTransport.exists_orthogonal_blocks_of_two_phase_and_conjugation
      J.toLinearEquiv.toLinearMap J.isometry hJ A (V : _ →L[ℂ] _) hA
      (Complex.exp ((a : ℂ) * Complex.I))
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) hrepr
  refine ⟨V, J, F, hV, hJ, hJx, ?_, hpair, hspan, ?_⟩
  · intro S hS
    obtain ⟨hS0, hdim, _, hVS, hJS⟩ := hF S hS
    exact ⟨hS0, hdim, hVS, hJS⟩
  · classical
    let f := fun S : Submodule ℂ L => S.map L.subtype
    let F' := F.image f
    have hF' : ∀ T ∈ F', T ≠ ⊥ ∧ Module.finrank ℂ T ≤ 2 ∧
        (∀ z ∈ T, K.reflection (conjugation z) ∈ T) ∧
        (∀ z ∈ T, (U : 𝓔 →L[ℂ] 𝓔) z ∈ T) := by
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨hS0, hdim, _, hVS, hJS⟩ := hF S hS
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hz
        apply hS0
        apply bot_unique
        intro x hx
        have hmem : (x : 𝓔) ∈ f S := ⟨x, hx, rfl⟩
        rw [hz, Submodule.mem_bot] at hmem
        exact Subtype.ext hmem
      · exact (Submodule.finrank_map_subtype_eq L S).le.trans hdim
      · rintro z ⟨x, hx, rfl⟩
        exact ⟨J x, hJS x hx, hJx x⟩
      · rintro z ⟨x, hx, rfl⟩
        exact ⟨V x, hVS x hx, hV x⟩
    have hpair' : (F' : Set (Submodule ℂ 𝓔)).Pairwise Submodule.IsOrtho := by
      intro S hS T hT hST
      obtain ⟨S', hS', rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
      exact (hpair hS' hT' (fun h => hST (congrArg f h))).map L.subtypeₗᵢ
    have hspan' : F'.sup id = L := by
      apply le_antisymm
      · apply Finset.sup_le
        intro S hS
        obtain ⟨S', _, rfl⟩ := Finset.mem_image.mp hS
        rintro z ⟨x, _, rfl⟩
        exact x.property
      · have hle : F.sup id ≤ (F'.sup id).comap L.subtype := by
          apply Finset.sup_le
          intro S hS x hx
          have hSf : f S ∈ F' := Finset.mem_image.mpr ⟨S, hS, rfl⟩
          exact (Finset.le_sup (f := id) hSf) ⟨x, hx, rfl⟩
        rw [hspan] at hle
        intro x hx
        exact hle (show (⟨x, hx⟩ : L) ∈ ⊤ from Submodule.mem_top)
    have hL : L.IsOrtho (L.map K.reflection.toLinearMap) := by
      rw [Submodule.isOrtho_iff_inner_eq]
      rintro x hx z ⟨y, hy, rfl⟩
      have hyneg : K.reflection y ∈ Module.End.eigenspace G.toLinearMap (-g : ℂ) := by
        have hy' : G y = (g : ℂ) • y := Module.End.mem_eigenspace_iff.mp hy
        rw [Module.End.mem_eigenspace_iff]
        change G (K.reflection y) = _
        rw [hGR, hy', map_smul]
        simp only [neg_smul]
      have hne : (g : ℂ) ≠ -g := by
        intro heq
        have hre := congrArg Complex.re heq
        simp only [Complex.ofReal_re, Complex.neg_re] at hre
        linarith
      exact ((isSelfAdjoint_schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).isSymmetric.orthogonalFamily_eigenspaces) hne ⟨x, hx⟩ ⟨K.reflection y, hyneg⟩
    exact RealTransport.exists_orthogonal_real_source_balanced_blocks K
      hRC (U : 𝓔 →L[ℂ] 𝓔) hUC L hL F' hF' hpair' hspan'

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
