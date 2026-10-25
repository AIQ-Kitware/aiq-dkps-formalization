/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealRestrictions

/-!
# Exact angle costs on the actual blocks of every real global minimum

The complete orthogonal family supplied by real spectral-gradient descent
has actual restricted source ranks at most two. Its accepted angle
multisets partition the original pair's angles, including all zero slots.
Every block cost is explicit: the clipped two-angle formula in dimension
four, the one-angle minimum on balanced planes, and zero on fixed blocks.

This supplies an exact angle-cost certificate for every ambient real
global minimum. A minimum over arbitrary combinatorial matchings still
requires constructing a transporter for each allowed matching and removing
the zero slots without changing the matching value.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The unrestricted one-angle real Schatten power minimum. -/
def realSingleSchattenCost (p theta : ℝ) : ℝ :=
  min (2 * phaseChord theta^p) ((2 : ℝ)^p)

/-- The unrestricted ordered two-angle real Schatten power minimum.
Its use below is on the accepted decreasing principal angles. -/
def realPairSchattenCost (p theta psi : ℝ) : ℝ :=
  let h := (theta + psi)/2
  let d := (theta - psi)/2
  min (2 * phasePower p h (max d (optimalPhase p h)))
    ((2 : ℝ)^p + 2 * phaseChord psi^p)

/-- A fixed source direction has zero one-angle cost. -/
@[simp] theorem realSingleSchattenCost_zero (p : ℝ) (hp : 0 < p) :
    realSingleSchattenCost p 0 = 0 := by
  simp [realSingleSchattenCost, phaseChord, Real.zero_rpow hp.ne', Real.rpow_nonneg]

/-- Pairing a nonnegative angle with a zero angle gives exactly its
one-angle cost. Thus common fixed directions cannot improve the matching
value by serving as extra partners. The scalar phase is clipped to the
single-point interval at half the nonzero angle. -/
theorem realPairSchattenCost_zero (p theta : ℝ) (hp : 1 ≤ p) (htheta : 0 ≤ theta) :
    realPairSchattenCost p theta 0 = realSingleSchattenCost p theta := by
  have hphase := (optimalPhase_spec p (theta/2) hp (by linarith)).1.2
  have hsum : theta/2 + theta/2 = theta := by ring
  simp only [realPairSchattenCost, add_zero, sub_zero, max_eq_left hphase, phasePower,
    hsum, sub_self]
  simp [realSingleSchattenCost, phaseChord, Real.zero_rpow (show p ≠ 0 by linarith)]

/-- Exact cost assigned to an actual small block. Fixed blocks of dimension
at most two contribute the sum of their zero-angle one-angle costs. -/
def realSchattenAngleBlockCost (p : ℝ) (K L : Submodule ℝ E) : ℝ :=
  if Module.finrank ℝ E = 4 then
    realPairSchattenCost p (K.principalAngles L 0) (K.principalAngles L 1)
  else ∑ j : Fin (Module.finrank ℝ K), realSingleSchattenCost p (K.principalAngles L j)

/-- Every real global minimum has a complete actual reducing family with
at most two source-angle entries per member. Its explicit angle costs sum
to the ambient minimum, and its complete accepted angle multiset is exactly
the original pair's multiset. This holds in every finite ambient dimension
and source rank, with no endpoint, multiplicity or determinant exclusions. -/
theorem exists_real_schatten_angle_cost_decomposition [CompleteSpace E]
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
        Module.finrank ℝ (K.comap N.subtype) ≤ 2 ∧
        (Module.finrank ℝ N = 4 → Module.finrank ℝ (K.comap N.subtype) = 2) ∧
        (∀ x ∈ N, K.starProjection x ∈ N) ∧
        (∀ x ∈ N, (K.map T.toLinearMap).starProjection x ∈ N) ∧
        (∀ x ∈ N, T x ∈ N)) ∧
      (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ H.sup id = ⊤ ∧
      K.principalAngleMultiset (K.map T.toLinearMap) =
        ∑ N : {N : Submodule ℝ E // N ∈ H},
          (K.comap N.val.subtype).principalAngleMultiset
            ((K.map T.toLinearMap).comap N.val.subtype) ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal =
        ∑ N : {N : Submodule ℝ E // N ∈ H},
          realSchattenAngleBlockCost p.toReal (K.comap N.val.subtype)
            ((K.map T.toLinearMap).comap N.val.subtype) := by
  classical
  obtain ⟨H, hH, horth, hspan, hsum, hangles⟩ :=
    exists_complete_globally_minimizing_blocks_real p hp hp1 hp2 K T hmin
  refine ⟨H, ?_, horth, hspan, hangles, ?_⟩
  · intro N hN
    obtain ⟨hN0, hNdim, hPN, V, hV, _, hclass, _, _⟩ := hH N hN
    refine ⟨hN0, hNdim, ?_, ?_, hPN,
      K.starProjection_map_mem_of_isometry_restriction N T V hV hPN, ?_⟩
    · rcases hclass with hfixed | htwo | hfour
      · exact (K.comap N.subtype).finrank_le.trans hfixed.1
      · omega
      · omega
    · intro hfour
      rcases hclass with hfixed | htwo | hfourRank
      · omega
      · omega
      · exact hfourRank.2
    · intro x hx
      rw [← hV ⟨x, hx⟩]
      exact (V ⟨x, hx⟩).property
  · rw [hsum]
    apply Finset.sum_congr rfl
    intro N _
    obtain ⟨_, _, _, V, hV, _, hclass, hfour, htwo⟩ := hH N.val N.property
    have htarget := K.map_comap_subtype_of_isometry_restriction
      (K.map T.toLinearMap) N.val T V rfl hV
    have hcompression :
        N.val.orthogonalProjectionOnto.toLinearMap ∘ₗ T.toLinearMap ∘ₗ N.val.subtype =
          V.toLinearMap := by
      apply LinearMap.ext
      intro x
      change N.val.orthogonalProjectionOnto (T x) = V x
      rw [← hV]
      exact N.val.orthogonalProjectionOnto_mem_subspace_eq_self (V x)
    rw [hcompression]
    unfold realSchattenAngleBlockCost
    by_cases hNfour : Module.finrank ℝ N.val = 4
    · rw [ite_eq_left hNfour, ← htarget]
      exact hfour hNfour
    · rw [ite_eq_right hNfour]
      rcases hclass with hfixed | htwoRank | hfourRank
      · have hVL : V.toLinearMap = LinearMap.id :=
          congrArg ContinuousLinearMap.toLinearMap hfixed.2
        have htargetSelf : (K.map T.toLinearMap).comap N.val.subtype =
            K.comap N.val.subtype := by
          rw [← htarget, hVL, Submodule.map_id]
        simp [hVL, htargetSelf, realSingleSchattenCost, Submodule.principalAngles_self,
          phaseChord, Real.zero_rpow (show p.toReal ≠ 0 by linarith), Real.rpow_nonneg]
      · rw [htwoRank.2, Fin.sum_univ_one, ← htarget]
        exact htwo htwoRank.1 htwoRank.2
      · exact (hNfour hfourRank.1).elim

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
