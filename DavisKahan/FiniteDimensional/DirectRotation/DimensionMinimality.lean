/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearOptimality
public import DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Spectrum
public import DavisKahan.FiniteDimensional.DirectRotation.SmallAngleCounterexample

/-!
# Least real dimension for the short-angle trace-norm counterexample

Each positive principal angle of an acute pair supplies an orthogonal
principal plane. In ambient dimension at most three there can therefore be
at most one positive angle. The unrestricted real nuclear optimality
criterion then gives direct-rotation minimality when all angles are at most
`pi / 3`. Together with the four-dimensional small-angle family, this makes
four the least real ambient dimension for this trace-norm failure.

The dimension argument uses the existing principal-plane construction;
the optimization argument specializes `RealNuclearOptimality`.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional

open Module (finrank)
open scoped BigOperators

section PrincipalPlanes

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Positive principal angles are exactly the indices counted by the
rank of the directed sine map. -/
theorem principalAngles_pos_iff_lt_nontrivialAngleCount (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (i : ℕ) :
    0 < U.principalAngles V i ↔ i < nontrivialAngleCount U V := by
  rw [U.principalAngles_apply V, Real.arcsin_pos, U.principalSines_def V]
  have hmap : (U.sinThetaMap V).toLinearMap = sinThetaMap U V := by
    rw [U.sinThetaMap_def V]
    rfl
  rw [hmap]
  exact (sinThetaMap U V).singularValues_pos_iff_lt_finrank_range

/-- An acute pair in dimension at most three has at most one positive
principal-angle label, including multiplicities. -/
theorem positive_principalAngle_unique_of_finrank_le_three (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (hdim : finrank 𝕜 E ≤ 3)
    {i j : ℕ} (hi : 0 < U.principalAngles V i) (hj : 0 < U.principalAngles V j) :
    i = j := by
  have hn := twice_nontrivialAngleCount_le_finrank_of_acute U V hacute
  have hi' := (principalAngles_pos_iff_lt_nontrivialAngleCount U V i).mp hi
  have hj' := (principalAngles_pos_iff_lt_nontrivialAngleCount U V j).mp hj
  omega

/-- The trace norm of an acute direct rotation is the sum of its
principal-plane chord costs, with the accepted angle multiplicities. -/
theorem nuclear_directRotation_displacement_eq_sum_principalAngles
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    UnitarilyInvariantSeminorm.nuclear 𝕜 E E
        (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      ∑ i : Fin (finrank 𝕜 U), 4 * Real.sin (U.principalAngles V i / 2) := by
  classical
  let A := LinearMap.id - (directRotation U V hacute).toLinearMap
  let n := nontrivialAngleCount U V
  have hnU : n ≤ finrank 𝕜 U := by
    by_contra h
    have hp := (principalAngles_pos_iff_lt_nontrivialAngleCount U V (finrank 𝕜 U)).mpr
      (Nat.lt_of_not_ge h)
    rw [U.principalAngles_of_finrank_le V le_rfl] at hp
    exact (lt_irrefl 0) hp
  have hzero (i : ℕ) (hi : n ≤ i) : U.principalAngles V i = 0 := by
    apply le_antisymm _ (U.principalAngles_nonneg V i)
    exact le_of_not_gt (fun hp => (Nat.not_lt_of_ge hi)
      ((principalAngles_pos_iff_lt_nontrivialAngleCount U V i).mp hp))
  have hcost : UnitarilyInvariantSeminorm.nuclear 𝕜 E E A =
      ∑ i : Fin n, 2 * principalPlaneChord U V i := by
    have htail : A.singularValues (2 * n) = 0 := by
      rw [singularValues_directRotation_displacement U V hacute]
      simp [n]
    have hrank := A.singularValues_eq_zero_iff_le_finrank_range.mp htail
    rw [← A.kyFanSum_eq_nuclear hrank, ← kyFanSum_eq_linearMap_kyFanSum,
      kyFanSum_directRotation_displacement_eq_principalChords]
    simp only [Nat.mul_mod_right, Nat.zero_ne_one, false_and, dite_false, add_zero]
    have hsize : min (2 * n / 2) n = n := by omega
    exact Fintype.sum_equiv (finCongr hsize) _ _ (fun _ => rfl)
  calc
    UnitarilyInvariantSeminorm.nuclear 𝕜 E E A =
        ∑ i : Fin n, 2 * principalPlaneChord U V i := hcost
    _ = ∑ i : Fin n, 4 * Real.sin (U.principalAngles V i / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      have hcos : Real.cos (U.principalAngles V i) = principalPlaneCosine U V i := by
        rw [U.principalAngles_apply V, Real.cos_arcsin, principalPlaneCosine,
          principalPlaneSine_eq_singularValue, U.principalSines_def V, U.sinThetaMap_def V]
        rfl
      rw [principalPlaneChord_eq_two_mul_sin_half U V i
        (U.principalAngles_nonneg V i)
        ((U.principalAngles_le_pi_div_two V i).trans (by linarith [Real.pi_pos])) hcos]
      ring
    _ = ∑ i : Fin (finrank 𝕜 U), 4 * Real.sin (U.principalAngles V i / 2) := by
      let f : ℕ → ℝ := fun i => 4 * Real.sin (U.principalAngles V i / 2)
      change (∑ i : Fin n, f i) = ∑ i : Fin (finrank 𝕜 U), f i
      calc
        (∑ i : Fin n, f i) = ∑ i ∈ Finset.range n, f i :=
          Fin.sum_univ_eq_sum_range f n
        _ = ∑ i ∈ Finset.range (finrank 𝕜 U), f i := by
          apply Finset.sum_subset (Finset.range_mono hnU)
          intro i _ hi
          simp only [Finset.mem_range, not_lt] at hi
          simp [f, hzero i hi]
        _ = ∑ i : Fin (finrank 𝕜 U), f i :=
          (Fin.sum_univ_eq_sum_range f (finrank 𝕜 U)).symm

end PrincipalPlanes

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- In real ambient dimension at most three, the printed `pi / 3`
hypothesis does give full trace-norm minimality of the direct rotation.
The competitor is any ambient orthogonal transporter. -/
theorem nuclear_directRotation_le_of_finrank_le_three
    (U V : Submodule ℝ E) (hacute : IsAcute U V)
    (hdim : finrank ℝ E ≤ 3) (hshort : U.principalAngles V 0 ≤ Real.pi / 3)
    (W : E ≃ₗᵢ[ℝ] E) (hmap : U.map W.toLinearMap = V) :
    UnitarilyInvariantSeminorm.nuclear ℝ E E
        (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      UnitarilyInvariantSeminorm.nuclear ℝ E E (LinearMap.id - W.toLinearMap) := by
  have hKL : finrank ℝ U = finrank ℝ V := by
    have h := W.toLinearEquiv.finrank_map_eq U
    change finrank ℝ (U.map W.toLinearMap) = finrank ℝ U at h
    rw [hmap] at h
    exact h.symm
  have hcanonical := (RealTransport.realTransportPowerMinimum_one_eq_canonical_iff U V hKL).mpr
    ⟨fun i => (U.principalAngles_antitone V (Nat.zero_le i.val)).trans hshort,
      fun i j hi hj => Fin.ext
        (positive_principalAngle_unique_of_finrank_le_three U V hacute hdim hi hj)⟩
  rw [RealTransport.realTransportPowerMinimum_one_eq_nuclearMatching U V hKL] at hcanonical
  obtain ⟨T, _, hcost, hmin⟩ :=
    RealTransport.exists_minimizing_real_nuclear_transport_matching U V hKL
  rw [UnitarilyInvariantSeminorm.schatten_one] at hcost hmin
  calc
    UnitarilyInvariantSeminorm.nuclear ℝ E E
        (LinearMap.id - (directRotation U V hacute).toLinearMap) =
        ∑ i : Fin (finrank ℝ U), 4 * Real.sin (U.principalAngles V i / 2) :=
      nuclear_directRotation_displacement_eq_sum_principalAngles U V hacute
    _ = UnitarilyInvariantSeminorm.nuclear ℝ E E (LinearMap.id - T.toLinearMap) :=
      hcanonical.symm.trans hcost.symm
    _ ≤ UnitarilyInvariantSeminorm.nuclear ℝ E E (LinearMap.id - W.toLinearMap) :=
      hmin W hmap

/-- A real trace-norm counterexample within the printed short-angle
range requires ambient dimension at least four. -/
theorem four_le_finrank_of_shortAngle_nuclear_counterexample
    (U V : Submodule ℝ E) (hacute : IsAcute U V)
    (hshort : U.principalAngles V 0 ≤ Real.pi / 3)
    (W : E ≃ₗᵢ[ℝ] E) (hmap : U.map W.toLinearMap = V)
    (hstrict : UnitarilyInvariantSeminorm.nuclear ℝ E E (LinearMap.id - W.toLinearMap) <
      UnitarilyInvariantSeminorm.nuclear ℝ E E
        (LinearMap.id - (directRotation U V hacute).toLinearMap)) :
    4 ≤ finrank ℝ E := by
  by_contra h
  have hdim : finrank ℝ E ≤ 3 := by omega
  exact (not_lt_of_ge (nuclear_directRotation_le_of_finrank_le_three
    U V hacute hdim hshort W hmap)) hstrict

/-- Four-dimensional real trace-norm counterexamples occur at arbitrarily
small positive angles even under the printed `pi / 3` bound. -/
theorem exists_four_dimensional_shortAngle_nuclear_counterexample
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
      (hacute : IsAcute U V)
      (W : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      U.map W.toLinearMap = V ∧
      0 < U.principalAngles V 0 ∧ U.principalAngles V 0 < epsilon ∧
      U.principalAngles V 0 ≤ Real.pi / 3 ∧
      UnitarilyInvariantSeminorm.nuclear ℝ _ _ (LinearMap.id - W.toLinearMap) <
        UnitarilyInvariantSeminorm.nuclear ℝ _ _
          (LinearMap.id - (directRotation U V hacute).toLinearMap) := by
  obtain ⟨U, V, hacute, W, hmap, hpos, hsmall, hshort, hstrict⟩ :=
    arbitrarilySmall_fullDisplacement_refuted epsilon hepsilon
  have hangle : principalAngles U V 0 = U.principalAngles V 0 := by
    rw [principalAngles, Finsupp.mapRange_apply, U.principalAngles_apply V,
      principalSines, U.principalSines_def V, U.sinThetaMap_def V]
    rfl
  have hnorm (A : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4)) :
      kyFanSum 4 A = UnitarilyInvariantSeminorm.nuclear ℝ _ _ A := by
    rw [kyFanSum_eq_linearMap_kyFanSum]
    exact A.kyFanSum_eq_nuclear
      ((LinearMap.finrank_range_le A).trans_eq finrank_euclideanSpace_fin)
  rw [hangle] at hpos hsmall hshort
  rw [hnorm, hnorm] at hstrict
  exact ⟨U, V, hacute, W, hmap, hpos, hsmall, hshort, hstrict⟩

/-- Four is the least real ambient dimension admitting an acute-pair
trace-norm counterexample within the printed short-angle range. -/
theorem isLeast_real_shortAngle_nuclear_counterexample_dimension :
    IsLeast {n : ℕ |
      ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
        (hacute : IsAcute U V)
        (W : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
        U.map W.toLinearMap = V ∧ U.principalAngles V 0 ≤ Real.pi / 3 ∧
        UnitarilyInvariantSeminorm.nuclear ℝ _ _ (LinearMap.id - W.toLinearMap) <
          UnitarilyInvariantSeminorm.nuclear ℝ _ _
            (LinearMap.id - (directRotation U V hacute).toLinearMap)} 4 := by
  constructor
  · obtain ⟨U, V, hacute, W, hmap, _, _, hshort, hstrict⟩ :=
      exists_four_dimensional_shortAngle_nuclear_counterexample 1 zero_lt_one
    exact ⟨U, V, hacute, W, hmap, hshort, hstrict⟩
  · rintro n ⟨U, V, hacute, W, hmap, hshort, hstrict⟩
    have h := four_le_finrank_of_shortAngle_nuclear_counterexample U V hacute hshort W hmap hstrict
    simpa only [finrank_euclideanSpace_fin] using h

end Real

end TauCeti.DavisKahan.FiniteDimensional
