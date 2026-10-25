/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealDecomposition
import DavisKahan.FiniteDimensional.DirectRotation.RealFourSchattenNorm
import DavisKahan.FiniteDimensional.DirectRotation.RealTwoSchattenNorm
import ForTauCeti.Analysis.InnerProductSpace.Complexification.UnitaryTransport
import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.FiniteBlocks
import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace
import ForTauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngleBlocks

/-!
# Every real spectral block of a global minimum is an unrestricted minimum

Descend the actual conjugation-fixed problem to the original real space,
preserving its accepted Schatten cost exactly. Restrict to the complete
small real blocks, identify the source projections with the actual
subspace intersections, and compare with every real unitary competitor
on each block. Thus the two- and four-dimensional optimizations apply to
genuine unrestricted restriction problems of an ambient global minimum.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local notation "𝓔" => RealComplexification E

omit [CompleteSpace E] in
/-- A conjugation-fixed source projection descends to the actual real
source subspace's orthogonal projection. -/
theorem realify_starProjection_realSubmodule
    (K : Submodule ℂ 𝓔) (hK : conjugateOperator K.starProjection = K.starProjection) :
    realify K.starProjection = (realSubmodule K).starProjection := by
  have hKC : ∀ z ∈ K, conjugation z ∈ K := by
    intro z hz
    apply K.starProjection_eq_self_iff.mp
    have h := congrArg (fun A : 𝓔 →L[ℂ] 𝓔 => A (conjugation z)) hK
    simp only [conjugateOperator_apply, conjugation_involutive,
      K.starProjection_eq_self_iff.mpr hz] at h
    exact h.symm
  have hreal : complexifySubmodule (realSubmodule K) = K := complexify_realSubmodule K hKC
  apply complexify_injective
  have hP : complexify (realify K.starProjection) = K.starProjection :=
    complexify_realPartOperator hK
  rw [hP, ← starProjection_complexifySubmodule]
  simp only [hreal]

/-- Every ambient real global Schatten minimum has a complete orthogonal
small-block decomposition whose actual restrictions are globally minimal
among all real unitary transports of the source intersection. Balanced
blocks have actual restricted source ranks one or two. The zero-gradient
exceptions remain tagged without a balance assumption. -/
theorem exists_complete_globally_minimizing_real_blocks
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ 𝓔) [K.HasOrthogonalProjection]
    (hK : conjugateOperator K.starProjection = K.starProjection)
    (Q : 𝓔 →L[ℂ] 𝓔) (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * K.starProjection * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * K.starProjection * star W = Q ∧
        conjugateOperator W = W} (U : 𝓔 →L[ℂ] 𝓔)) :
    let K₀ := realSubmodule K
    let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
    ∃ H : Finset (Submodule ℝ E),
      (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
        (∀ x ∈ N, K₀.starProjection x ∈ N) ∧
        ∃ V : N ≃ₗᵢ[ℝ] N,
          (∀ x : N, (V x : E) = realify (U : 𝓔 →L[ℂ] 𝓔) x) ∧
          IsMinOn
            (fun W : N →L[ℝ] N => UnitarilyInvariantSeminorm.schatten ℝ N N p
              (LinearMap.id - W.toLinearMap) ^ p.toReal)
            {W | W ∈ unitary (N →L[ℝ] N) ∧
              W * (K₀.comap N.subtype).starProjection * star W =
                (V : N →L[ℝ] N) * (K₀.comap N.subtype).starProjection * star (V : N →L[ℝ] N)}
            (V : N →L[ℝ] N) ∧
          (((Module.finrank ℝ N = 2 ∧ Module.finrank ℝ (K₀.comap N.subtype) = 1) ∨
            (Module.finrank ℝ N = 4 ∧ Module.finrank ℝ (K₀.comap N.subtype) = 2)) ∨
            (Module.finrank ℝ N ≤ 2 ∧ complexifySubmodule N ≤ G.toLinearMap.ker))) ∧
      (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ H.sup id = ⊤ := by
  let K₀ := realSubmodule K
  have hPreal := realify_starProjection_realSubmodule K hK
  have hUc : complexify (realify (U : 𝓔 →L[ℂ] 𝓔)) = (U : 𝓔 →L[ℂ] 𝓔) :=
    complexify_realPartOperator hU
  have hTU : realify (U : 𝓔 →L[ℂ] 𝓔) ∈ unitary (E →L[ℝ] E) := by
    apply (mem_unitary_complexify_iff _).mp
    rw [hUc]
    exact U.property
  let T := Unitary.linearIsometryEquiv ⟨realify (U : 𝓔 →L[ℂ] 𝓔), hTU⟩
  have hT : (T : E →L[ℝ] E) = realify (U : 𝓔 →L[ℂ] 𝓔) :=
    Unitary.coe_linearIsometryEquiv_apply _
  have hrealmin := isMinOn_realify_transport p hp K.starProjection
    (U : 𝓔 →L[ℂ] 𝓔) hK hU (by simpa only [htrans] using hmin)
  rw [hPreal] at hrealmin
  obtain ⟨H, hH, horth, hspan⟩ :=
    exists_complete_real_blocks_of_isLocalMinOn_real_transports
      p hp hp1 hp2 K hK Q U hU htrans hmin.isLocalMinOn
  refine ⟨H, ?_, horth, hspan⟩
  intro N hN
  obtain ⟨hN0, hNdim, hPN, hUN, hclass⟩ := hH N hN
  have hPN' : ∀ x ∈ N, K₀.starProjection x ∈ N := by
    simpa only [hPreal] using hPN
  have hTN : ∀ x ∈ N, T x ∈ N := by
    intro x hx
    change (T : E →L[ℝ] E) x ∈ N
    rw [hT]
    exact hUN x hx
  obtain ⟨V, hV, hVmin⟩ := exists_isMinOn_restriction_of_invariant
    p hp T K₀.starProjection (isSelfAdjoint_starProjection K₀) N hTN hPN'
    (by simpa only [hT] using hrealmin)
  have hP₀ : (K₀.starProjection.toLinearMap.restrict hPN').toContinuousLinearMap =
      (K₀.comap N.subtype).starProjection := by
    ext x
    change K₀.starProjection (x : E) =
      (((K₀.comap N.subtype).starProjection x : N) : E)
    exact (K₀.starProjection_comap_subtype_apply_of_invariant N hPN' x).symm
  rw [hP₀] at hVmin
  have hrank : Module.finrank ℝ (K₀.comap N.subtype) =
      Module.finrank ℝ ↥(N ⊓ K₀) := by
    rw [← Submodule.finrank_map_subtype_eq N (K₀.comap N.subtype),
      Submodule.map_comap_subtype]
  refine ⟨hN0, hNdim, hPN', V, ?_, hVmin, ?_⟩
  · intro x
    rw [hV]
    exact congrArg (fun A : E →L[ℝ] E => A x) hT
  · rw [hrank]
    exact hclass

/-- Every global real orthogonal transport minimum, stated on the original
real Hilbert space, decomposes completely into fixed blocks of dimension at
most two, balanced two-dimensional rank-one problems, and four-dimensional
rank-two problems. The restriction comparison includes all orthogonal competitors;
no real-minimum hypothesis is replaced by complex unrestricted minimality.
The cost splits over the same actual blocks, and their accepted angle
multisets assemble to the original pair's angles with exact multiplicities,
including every zero and right angle. -/
theorem exists_complete_globally_minimizing_blocks_real
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W =
        (T : E →L[ℝ] E) * K.starProjection * star (T : E →L[ℝ] E)} (T : E →L[ℝ] E)) :
    ∃ H : Finset (Submodule ℝ E),
      (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
        (∀ x ∈ N, K.starProjection x ∈ N) ∧
        ∃ V : N ≃ₗᵢ[ℝ] N,
          (∀ x : N, (V x : E) = T x) ∧
          IsMinOn
            (fun W : N →L[ℝ] N => UnitarilyInvariantSeminorm.schatten ℝ N N p
              (LinearMap.id - W.toLinearMap) ^ p.toReal)
            {W | W ∈ unitary (N →L[ℝ] N) ∧
              W * (K.comap N.subtype).starProjection * star W =
                (V : N →L[ℝ] N) * (K.comap N.subtype).starProjection * star (V : N →L[ℝ] N)}
            (V : N →L[ℝ] N) ∧
          ((Module.finrank ℝ N ≤ 2 ∧ (V : N →L[ℝ] N) = 1) ∨
            (Module.finrank ℝ N = 2 ∧ Module.finrank ℝ (K.comap N.subtype) = 1) ∨
            (Module.finrank ℝ N = 4 ∧ Module.finrank ℝ (K.comap N.subtype) = 2)) ∧
          (Module.finrank ℝ N = 4 →
            let A := K.comap N.subtype
            let B := A.map V.toLinearMap
            let h := (A.principalAngles B 0 + A.principalAngles B 1)/2
            let d := (A.principalAngles B 0 - A.principalAngles B 1)/2
            UnitarilyInvariantSeminorm.schatten ℝ N N p
              (LinearMap.id - V.toLinearMap) ^ p.toReal =
              min (2*phasePower p.toReal h (max d (optimalPhase p.toReal h)))
                ((2 : ℝ)^p.toReal + 2*phaseChord (A.principalAngles B 1)^p.toReal)) ∧
          (Module.finrank ℝ N = 2 → Module.finrank ℝ (K.comap N.subtype) = 1 →
            UnitarilyInvariantSeminorm.schatten ℝ N N p
              (LinearMap.id - V.toLinearMap) ^ p.toReal =
              min (2 * phaseChord ((K.comap N.subtype).principalAngles
                ((K.comap N.subtype).map V.toLinearMap) 0)^p.toReal) ((2 : ℝ)^p.toReal))) ∧
      (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ H.sup id = ⊤ ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal =
        ∑ N : {N : Submodule ℝ E // N ∈ H},
          UnitarilyInvariantSeminorm.schatten ℝ N.val N.val p
            (LinearMap.id - (N.val.orthogonalProjectionOnto.toLinearMap ∘ₗ
              T.toLinearMap ∘ₗ N.val.subtype)) ^ p.toReal ∧
      K.principalAngleMultiset (K.map T.toLinearMap) =
        ∑ N : {N : Submodule ℝ E // N ∈ H},
          (K.comap N.val.subtype).principalAngleMultiset
            ((K.map T.toLinearMap).comap N.val.subtype) := by
  have hTU : (T : E →L[ℝ] E) ∈ unitary (E →L[ℝ] E) := by
    simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using
      (Unitary.linearIsometryEquiv.symm T).property
  let U : unitary (𝓔 →L[ℂ] 𝓔) :=
    ⟨complexify (T : E →L[ℝ] E), (mem_unitary_complexify_iff _).mpr hTU⟩
  let Kc := complexifySubmodule K
  have hP : Kc.starProjection = complexify K.starProjection := starProjection_complexifySubmodule K
  have hKc : conjugateOperator Kc.starProjection = Kc.starProjection := by
    rw [hP, conjugateOperator_complexify]
  have hUc : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U :=
    conjugateOperator_complexify (T : E →L[ℝ] E)
  have hminc := isMinOn_complexify_transport_of_real p hp K.starProjection
    (T : E →L[ℝ] E) hmin
  obtain ⟨H, hH, horth, hspan⟩ := exists_complete_globally_minimizing_real_blocks
    p hp hp1 hp2 Kc hKc
    ((U : 𝓔 →L[ℂ] 𝓔) * Kc.starProjection * star (U : 𝓔 →L[ℂ] 𝓔))
    U hUc rfl (by simpa only [hP] using hminc)
  have hrealT : realify (U : 𝓔 →L[ℂ] 𝓔) = (T : E →L[ℝ] E) := by
    ext x
    simp only [U, realify_apply, re_complexify, re_ofReal]
  have hsource : realSubmodule Kc = K := realSubmodule_complexifySubmodule K
  simp only [hsource, hrealT] at hH
  refine ⟨H, ?_, horth, hspan, ?_⟩
  · intro N hN
    obtain ⟨hN0, hNdim, hPN, V, hV, hVmin, hclass⟩ := hH N hN
    refine ⟨hN0, hNdim, hPN, V, ?_, hVmin, ?_, ?_, ?_⟩
    · intro x
      exact hV x
    · rcases hclass with (h2 | h4) | hzero
      · change Module.finrank ℝ N = 2 ∧
          Module.finrank ℝ ((realSubmodule Kc).comap N.subtype) = 1 at h2
        rw [hsource] at h2
        exact Or.inr (Or.inl h2)
      · change Module.finrank ℝ N = 4 ∧
          Module.finrank ℝ ((realSubmodule Kc).comap N.subtype) = 2 at h4
        rw [hsource] at h4
        exact Or.inr (Or.inr h4)
      · let S := K.comap N.subtype
        by_cases htrivial : S = ⊥ ∨ S = ⊤
        · have hprojection : S.starProjection = 0 ∨ S.starProjection = 1 := by
            rcases htrivial with hz | ht
            · left
              simp only [hz, Submodule.starProjection_bot]
            · right
              simp only [ht, Submodule.starProjection_top]
              rfl
          have hidentity := eq_one_of_isMinOn_transport_zero_or_one p hp S.starProjection
            hprojection (Unitary.linearIsometryEquiv.symm V)
            (by simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using hVmin)
          exact Or.inl ⟨hzero.1, by
            simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using hidentity⟩
        · have hpos : 1 ≤ Module.finrank ℝ S :=
            Submodule.one_le_finrank_iff.mpr (fun hz => htrivial (Or.inl hz))
          have hstrict : Module.finrank ℝ S < Module.finrank ℝ N :=
            lt_of_le_of_ne S.finrank_le (fun heq =>
              htrivial (Or.inr (Submodule.eq_top_of_finrank_eq heq)))
          have hbalanced : Module.finrank ℝ N = 2 ∧ Module.finrank ℝ S = 1 := by omega
          exact Or.inr (Or.inl hbalanced)
    · intro hNfour
      have hKtwo : Module.finrank ℝ (K.comap N.subtype) = 2 := by
        rcases hclass with (h2 | h4) | hzero
        · omega
        · change Module.finrank ℝ N = 4 ∧
            Module.finrank ℝ ((realSubmodule Kc).comap N.subtype) = 2 at h4
          rw [hsource] at h4
          exact h4.2
        · omega
      exact real_four_schatten_cost_eq_of_isMinOn_image
        p hp hp1 hp2 (K.comap N.subtype) hNfour hKtwo V hVmin
    · intro hNtwo hKone
      exact real_two_schatten_cost_eq_of_isMinOn_image
        p hp (K.comap N.subtype) hNtwo hKone V hVmin

  · classical
    let I := {N : Submodule ℝ E // N ∈ H}
    let W (i : I) := i.val
    have horthI : OrthogonalFamily ℝ (fun i => W i) (fun i => (W i).subtypeₗᵢ) := by
      intro i j hij x y
      exact (horth i.property j.property (fun heq => hij (Subtype.ext heq))).inner_eq
        x.property y.property
    have hspanI : (⨆ i : I, W i) = ⊤ := by
      apply top_unique
      rw [← hspan]
      apply Finset.sup_le
      intro N hN
      exact le_iSup (fun i : I => W i) ⟨N, hN⟩
    have hTN : ∀ i : I, ∀ x ∈ W i, (T : E →L[ℝ] E) x ∈ W i := by
      intro i x hx
      obtain ⟨_, _, _, V, hV, _, _⟩ := hH i.val i.property
      have heq : T x = (V ⟨x, hx⟩ : E) := (hV ⟨x, hx⟩).symm
      change T x ∈ W i
      rw [heq]
      exact (V ⟨x, hx⟩).property
    constructor
    · exact schatten_displacement_rpow_of_orthogonal_blocks W horthI hspanI
        (T : E →L[ℝ] E) hTN p hp
    · have hKI : ∀ i : I, ∀ x ∈ W i, K.starProjection x ∈ W i := by
        intro i
        exact (hH i.val i.property).2.2.1
      have hLI : ∀ i : I, ∀ x ∈ W i,
          (K.map T.toLinearMap).starProjection x ∈ W i := by
        intro i
        obtain ⟨_, _, hPN, V, hV, _, _⟩ := hH i.val i.property
        exact K.starProjection_map_mem_of_isometry_restriction i.val T V hV hPN
      exact K.principalAngleMultiset_of_orthogonal_blocks
        (K.map T.toLinearMap) W horthI hspanI hKI hLI

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
