/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealStationarity
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientBlocks
import DavisKahan.FiniteDimensional.DirectRotation.RealBlockDescent
import ForTauCeti.Analysis.InnerProductSpace.AnticommutingConjugation
import ForTauCeti.Analysis.InnerProductSpace.Projection.ConjugationBlocks

/-!
# Real blocks on the zero Schatten gradient level

The zero-gradient unitary restriction is a reflection. Source projection and
its negative-phase projection preserve the actual restricted conjugation.
Their common real lines and planes give the zero-level blocks needed for
the finite real transport matching theorem.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local notation "𝓔" => RealComplexification E

/-- The zero-gradient restriction of a real local minimum supplies two actual
orthogonal projections preserving its coordinate conjugation: the source
projection and the negative-phase projection of the restricted transporter. -/
theorem gradient_kernel_projection_data_of_isLocalMinOn_real_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K : Submodule ℂ 𝓔) [K.HasOrthogonalProjection]
    (hK : conjugateOperator K.starProjection = K.starProjection)
    (Q : 𝓔 →L[ℂ] 𝓔) (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * K.starProjection * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsLocalMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * K.starProjection * star W = Q ∧
        conjugateOperator W = W} (U : 𝓔 →L[ℂ] 𝓔)) :
    let L := (schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).toLinearMap.ker
    ∃ (J : L ≃ₗᵢ⋆[ℂ] L) (A S : L →L[ℂ] L) (V : L ≃ₗᵢ[ℂ] L),
      IsStarProjection A ∧ IsStarProjection S ∧ Function.Involutive J ∧
      (∀ x : L, (J x : 𝓔) = conjugation x) ∧
      (∀ x : L, (A x : 𝓔) = K.starProjection x) ∧
      (∀ x : L, (V x : 𝓔) = (U : 𝓔 →L[ℂ] 𝓔) x) ∧
      (V : L →L[ℂ] L) = 1 - (2 : ℂ) • S ∧
      (∀ x, J (A x) = A (J x)) ∧ (∀ x, J (S x) = S (J x)) := by
  let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
  let L := G.toLinearMap.ker
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_real_transports
    p hp hp1 K.starProjection Q hP hK U hU htrans hmin
  have hR : (K.reflection : 𝓔 →L[ℂ] 𝓔) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hR] at hconj
  have hGR (x : 𝓔) : G (K.reflection x) = -K.reflection (G x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (K.reflection x)) hconj
    change K.reflection (G (K.reflection (K.reflection x))) = -G (K.reflection x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  have hRL : ∀ x ∈ L, K.reflection x ∈ L := by
    intro x hx
    have hx' : G x = 0 := LinearMap.mem_ker.mp hx
    rw [LinearMap.mem_ker]
    change G (K.reflection x) = 0
    rw [hGR, hx', map_zero, neg_zero]
  have hPL : ∀ x ∈ L, K.starProjection x ∈ L := by
    intro x hx
    have hPx : K.starProjection x = (1 / 2 : ℂ) • (K.reflection x + x) := by
      have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T x) hR
      change K.reflection x = (2 : ℂ) • K.starProjection x - x at h
      rw [h]
      module
    rw [hPx]
    exact L.smul_mem _ (L.add_mem (hRL x hx) hx)
  have hPC (x : 𝓔) : K.starProjection (conjugation x) = conjugation (K.starProjection x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (conjugation x)) hK
    simpa only [conjugateOperator_apply, conjugation_involutive] using h.symm
  have hUC (x : 𝓔) : (U : 𝓔 →L[ℂ] 𝓔) (conjugation x) =
      conjugation ((U : 𝓔 →L[ℂ] 𝓔) x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (conjugation x)) hU
    simpa only [conjugateOperator_apply, conjugation_involutive] using h.symm
  have hGC := schattenUnitaryGradient_apply_conjugation p.toReal
    (U : 𝓔 →L[ℂ] 𝓔) (canonicalConjugation (E := E)).toLinearEquiv.toLinearMap hUC
  obtain ⟨J, hJ, hJx⟩ := exists_kernel_conjugation_of_anticommute G.toLinearMap
    (canonicalConjugation (E := E)) (fun x => conjugation_involutive x) hGC
  have hJx' (x : L) : (J x : 𝓔) = conjugation x := hJx x
  let A : L →L[ℂ] L := K.starProjection.restrict hPL
  have hAx (x : L) : (A x : 𝓔) = K.starProjection x := rfl
  have hA : IsStarProjection A := by
    refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_⟩
    · change A * A = A
      apply ContinuousLinearMap.ext
      intro x
      apply Subtype.ext
      change K.starProjection (K.starProjection (x : 𝓔)) = K.starProjection (x : 𝓔)
      exact congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T x) hP.isIdempotentElem.eq
    · intro x y
      exact hP.isSelfAdjoint.isSymmetric (x : 𝓔) (y : 𝓔)
  obtain ⟨V, S, hS, hV, hrepr⟩ := gradient_kernel_reflection_representation
    p.toReal (by linarith : 0 < p.toReal) U
  have hVC (x : L) : J (V x) = V (J x) := by
    apply Subtype.ext
    rw [hJx', hV, hV, hJx']
    exact (hUC x).symm
  have hSJ (x : L) : J (S x) = S (J x) := by
    have hSform : S = (1 / 2 : ℂ) • (1 - (V : L →L[ℂ] L)) := by
      rw [hrepr]
      module
    have hSx (y : L) : S y = (1 / 2 : ℂ) • (y - V y) :=
      congrArg (fun T : L →L[ℂ] L => T y) hSform
    rw [hSx, map_smulₛₗ, map_sub, hVC, hSx]
    congr 1
    simp only [one_div, map_inv₀, map_ofNat]
  refine ⟨J, A, S, V, hA, hS, hJ, hJx', hAx, hV, hrepr, ?_, hSJ⟩
  intro x
  apply Subtype.ext
  rw [hJx', hAx, hAx, hJx']
  exact (hPC x).symm

set_option maxHeartbeats 800000 in
/-- The entire zero-gradient space of an actual real constrained local
minimum decomposes into orthogonal real blocks of dimension at most two,
preserved by the source projection and the actual real transporter. -/
theorem gradient_kernel_real_blocks_of_isLocalMinOn_real_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K : Submodule ℂ 𝓔) [K.HasOrthogonalProjection]
    (hK : conjugateOperator K.starProjection = K.starProjection)
    (Q : 𝓔 →L[ℂ] 𝓔) (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * K.starProjection * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsLocalMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * K.starProjection * star W = Q ∧
        conjugateOperator W = W} (U : 𝓔 →L[ℂ] 𝓔)) :
    let L := (schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).toLinearMap.ker
    ∃ H : Finset (Submodule ℝ E),
      (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 2 ∧
        (∀ x ∈ N, realify K.starProjection x ∈ N) ∧
        (∀ x ∈ N, realify (U : 𝓔 →L[ℂ] 𝓔) x ∈ N)) ∧
      (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧
      complexifySubmodule (H.sup id) = L := by
  classical
  let L := (schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).toLinearMap.ker
  let : InnerProductSpace ℝ L := InnerProductSpace.rclikeToReal ℂ L
  obtain ⟨J, A, S, V, hA, hS, hJ, hJx, hAx, hV, hrepr, hAJ, hSJ⟩ :=
    gradient_kernel_projection_data_of_isLocalMinOn_real_transports
      p hp hp1 K hK Q U hU htrans hmin
  obtain ⟨F, hF, hpair, hspan⟩ := exists_orthogonal_realPoints_blocks_of_two_projections
    J.toLinearEquiv.toLinearMap A S hA hS hAJ hSJ
  let N := RealTransport.realSubmodule L
  let e := RealTransport.realPointsDescentEquiv L J hJx
  let j : realPoints J.toLinearEquiv.toLinearMap →ₗᵢ[ℝ] E :=
    N.subtypeₗᵢ.comp e.toLinearIsometry
  let B := realPointsOperator J.toLinearEquiv.toLinearMap S hSJ
  let D := realPointsOperator J.toLinearEquiv.toLinearMap A hAJ
  have hj (z : realPoints J.toLinearEquiv.toLinearMap) :
      j z = re ((z : L) : 𝓔) := RealTransport.realPointsDescentEquiv_apply L J hJx z
  have hjreal (z : realPoints J.toLinearEquiv.toLinearMap) :
      ofReal (j z) = (z : L) := by
    rw [hj]
    apply RealTransport.ofReal_re_of_conjugation_fixed
    have h := congrArg (fun w : L => (w : 𝓔)) (mem_realPoints.mp z.property)
    exact (hJx z).symm.trans h
  have hDj (z : realPoints J.toLinearEquiv.toLinearMap) :
      realify K.starProjection (j z) = j (D z) := by
    rw [realify_apply, hjreal, hj]
    have hDz : ((D z : L) : 𝓔) = K.starProjection (z : L) := by
      rw [show (D z : L) = A (z : L) from realPointsOperator_apply _ _ _ z, hAx]
    rw [hDz]
  have hUj (z : realPoints J.toLinearEquiv.toLinearMap) :
      realify (U : 𝓔 →L[ℂ] 𝓔) (j z) = j (z - (2 : ℝ) • B z) := by
    rw [realify_apply, hjreal, ← hV]
    have hphase : V (z : L) = (z : L) - (2 : ℂ) • S (z : L) :=
      congrArg (fun T : L →L[ℂ] L => T z) hrepr
    rw [hphase, map_sub, map_smul, hj, hj]
    have hBz : ((B z : L) : 𝓔) = (S (z : L) : 𝓔) :=
      congrArg (fun w : L => (w : 𝓔)) (realPointsOperator_apply _ _ _ z)
    rw [hBz]
    simp [re_complex_smul]
  let f := fun T : Submodule ℝ (realPoints J.toLinearEquiv.toLinearMap) =>
    (T.map e.toLinearMap).map N.subtype
  let H := F.image f
  have hf (T) (hT : T ∈ F) : f T ∈ H := Finset.mem_image.mpr ⟨T, hT, rfl⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hT0, hdim, hDT, hBT⟩ := hF T' hT'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      apply hT0
      apply bot_unique
      intro z hz
      have hm : j z ∈ f T' := ⟨e z, ⟨z, hz, rfl⟩, rfl⟩
      rw [hzero, Submodule.mem_bot] at hm
      exact j.injective (by simpa using hm)
    · calc
        Module.finrank ℝ (f T') = Module.finrank ℝ (T'.map e.toLinearMap) :=
          Submodule.finrank_map_subtype_eq N _
        _ = Module.finrank ℝ T' := e.toLinearEquiv.finrank_map_eq T'
        _ ≤ 2 := hdim
    · rintro x ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      change realify K.starProjection (j z) ∈ f T'
      rw [hDj]
      exact ⟨e (D z), ⟨D z, hDT z hz, rfl⟩, rfl⟩
    · rintro x ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      change realify (U : 𝓔 →L[ℂ] 𝓔) (j z) ∈ f T'
      rw [hUj]
      exact ⟨e (z - (2 : ℝ) • B z),
        ⟨z - (2 : ℝ) • B z, T'.sub_mem hz (T'.smul_mem _ (hBT z hz)), rfl⟩, rfl⟩
  · intro T hT W hW hTW
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hW
    exact ((hpair hT' hW' (fun h => hTW (congrArg f h))).map e.toLinearIsometry).map
      N.subtypeₗᵢ
  · have hspanR : H.sup id = N := by
      apply le_antisymm
      · apply Finset.sup_le
        intro T hT
        obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp hT
        rintro x ⟨z, _, rfl⟩
        exact z.property
      · have hle : F.sup id ≤ (H.sup id).comap j.toLinearMap := by
          apply Finset.sup_le
          intro T hT z hz
          exact (Finset.le_sup (f := id) (hf T hT)) ⟨e z, ⟨z, hz, rfl⟩, rfl⟩
        rw [hspan] at hle
        intro x hx
        obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
        have hmem := hle (show z ∈ ⊤ from Submodule.mem_top)
        change j z ∈ H.sup id at hmem
        have hjz : j z = x := congrArg (fun w : N => (w : E)) hz
        rwa [hjz] at hmem
    rw [hspanR]
    apply RealTransport.complexify_realSubmodule
    intro z hz
    have h := (J ⟨z, hz⟩).property
    rwa [hJx] at h

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
