/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealAngleCosts
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenTransportExistence

/-!
# Labelled matchings extracted from unrestricted real transport minima

A matching is an involutive permutation: fixed vertices are unmatched,
and each two-cycle is an edge. The pair weight is the full two-class
four-dimensional minimum, symmetrized in its two angles. Each edge is
counted with half its weight at each endpoint.

The exact accepted angle-index equivalence transfers the actual small
blocks of a real global minimum to the original principal-angle labels.
Thus repeated and zero angles retain their distinct indices. This is the
lower-bound direction of a matching formula; constructing an ambient
transporter for every matching is a separate converse.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open scoped ENNReal

/-- Symmetric pair weight, including both determinant classes of the
unrestricted four-dimensional problem. -/
@[expose]
def realSchattenPairWeight (p theta psi : ℝ) : ℝ :=
  realPairSchattenCost p (max theta psi) (min theta psi)

theorem realSchattenPairWeight_comm (p theta psi : ℝ) :
    realSchattenPairWeight p theta psi = realSchattenPairWeight p psi theta := by
  simp only [realSchattenPairWeight, max_comm, min_comm]

/-- Cost of a labelled matching. For an involutive permutation, every
nonfixed edge is counted twice with half its full two-angle weight. -/
@[expose]
def realSchattenMatchingCost {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) : ℝ := by
  classical
  exact ∑ i, if s i = i then realSingleSchattenCost p (theta i)
    else realSchattenPairWeight p (theta i) (theta (s i)) / 2

/-- Relabelling the vertices preserves the matching cost. -/
theorem realSchattenMatchingCost_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ) (theta : κ → ℝ) (s : Equiv.Perm κ) (e : ι ≃ κ) :
    realSchattenMatchingCost p (theta ∘ e) ((e.trans s).trans e.symm) =
      realSchattenMatchingCost p theta s := by
  classical
  unfold realSchattenMatchingCost
  rw [← e.sum_comp (fun i => if s i = i then realSingleSchattenCost p (theta i)
    else realSchattenPairWeight p (theta i) (theta (s i)) / 2)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply,
    Equiv.symm_apply_eq]

/-- Disjoint unions of labelled matchings have additive costs. -/
theorem realSchattenMatchingCost_sigma {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ℝ) (theta : (i : ι) → κ i → ℝ) (s : ∀ i, Equiv.Perm (κ i)) :
    realSchattenMatchingCost p (fun x : Sigma κ => theta x.1 x.2)
        (Equiv.sigmaCongrRight s) =
      ∑ i, realSchattenMatchingCost p (theta i) (s i) := by
  classical
  simp only [realSchattenMatchingCost, Fintype.sum_sigma, Equiv.sigmaCongrRight_apply,
    Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rfl

/-- An unmatched vertex has exactly its one-angle weight. -/
theorem realSchattenMatchingCost_refl {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) :
    realSchattenMatchingCost p theta (Equiv.refl ι) =
      ∑ i, realSingleSchattenCost p (theta i) := by
  simp [realSchattenMatchingCost]

/-- A two-cycle on decreasing angles has exactly the proved ordered
two-angle weight, without assuming either angle is positive or distinct. -/
theorem realSchattenMatchingCost_rev_two (p : ℝ) (theta : Fin 2 → ℝ)
    (horder : theta 1 ≤ theta 0) :
    realSchattenMatchingCost p theta Fin.revPerm = realPairSchattenCost p (theta 0) (theta 1) := by
  simp [realSchattenMatchingCost, Fin.sum_univ_two, Fin.revPerm, Fin.rev,
    realSchattenPairWeight, max_eq_left horder, min_eq_right horder,
    max_eq_right horder, min_eq_left horder]

/-- All labelled matchings on a finite vertex set, represented by their
involutive permutations. The identity is the empty-edge matching. -/
def realSchattenMatchings (ι : Type*) [Fintype ι] : Finset (Equiv.Perm ι) := by
  classical
  exact Finset.univ.filter (fun s => Function.Involutive s)

@[simp] theorem mem_realSchattenMatchings {ι : Type*} [Fintype ι] (s : Equiv.Perm ι) :
    s ∈ realSchattenMatchings ι ↔ Function.Involutive s := by
  classical
  simp [realSchattenMatchings]

theorem realSchattenMatchings_nonempty (ι : Type*) [Fintype ι] :
    (realSchattenMatchings ι).Nonempty := by
  exact ⟨Equiv.refl ι, mem_realSchattenMatchings _ |>.mpr (fun _ => rfl)⟩

/-- The finite combinatorial matching minimum, including an empty vertex
set and zero or repeated vertex angles. -/
def realSchattenMatchingMinimum {ι : Type*} [Fintype ι] (p : ℝ) (theta : ι → ℝ) : ℝ :=
  (realSchattenMatchings ι).inf' (realSchattenMatchings_nonempty ι)
    (realSchattenMatchingCost p theta)

/-- The combinatorial minimum is below every matching's cost. -/
theorem realSchattenMatchingMinimum_le {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) (hs : Function.Involutive s) :
    realSchattenMatchingMinimum p theta ≤ realSchattenMatchingCost p theta s := by
  exact Finset.inf'_le _ ((mem_realSchattenMatchings s).mpr hs)

/-- The finite matching minimum is attained by an actual involution.
This is combinatorial attainment; it does not construct an ambient
orthogonal transporter for that involution. -/
theorem exists_attains_realSchattenMatchingMinimum {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) :
    ∃ s : Equiv.Perm ι, Function.Involutive s ∧
      realSchattenMatchingCost p theta s = realSchattenMatchingMinimum p theta := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
    (realSchattenMatchings_nonempty ι) (realSchattenMatchingCost p theta)
  exact ⟨s, (mem_realSchattenMatchings s).mp hs, heq.symm⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Every ambient real global Schatten minimum has exactly the cost of a
matching on the original accepted principal-angle indices. The edge cost
is the full two-class four-dimensional minimum. Zero and repeated angles
remain distinct labels, and no principal-plane preservation is imposed
on the original minimizer. -/
theorem exists_matching_cost_eq_of_isMinOn_real_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W =
        (T : E →L[ℝ] E) * K.starProjection * star (T : E →L[ℝ] E)} (T : E →L[ℝ] E)) :
    ∃ s : Equiv.Perm (Fin (Module.finrank ℝ K)), Function.Involutive s ∧
      realSchattenMatchingCost p.toReal
        (fun j : Fin (Module.finrank ℝ K) => K.principalAngles (K.map T.toLinearMap) j) s =
        UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  classical
  obtain ⟨H, hH, horth, hspan, _, hcost⟩ :=
    exists_real_schatten_angle_cost_decomposition p hp hp1 hp2 K T hmin
  let I := {N : Submodule ℝ E // N ∈ H}
  let W (i : I) := i.val
  let A (i : I) := K.comap (W i).subtype
  let B (i : I) := (K.map T.toLinearMap).comap (W i).subtype
  let theta (i : I) (j : Fin (Module.finrank ℝ (A i))) := (A i).principalAngles (B i) j
  have horthI : OrthogonalFamily ℝ (fun i => W i) (fun i => (W i).subtypeₗᵢ) := by
    intro i j hij x y
    exact (horth i.property j.property (fun h => hij (Subtype.ext h))).inner_eq x.property y.property
  have hspanI : (⨆ i : I, W i) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Finset.sup_le
    intro N hN
    exact le_iSup W ⟨N, hN⟩
  have hKI : ∀ i : I, ∀ x ∈ W i, K.starProjection x ∈ W i :=
    fun i => (hH i.val i.property).2.2.2.2.1
  have hLI : ∀ i : I, ∀ x ∈ W i, (K.map T.toLinearMap).starProjection x ∈ W i :=
    fun i => (hH i.val i.property).2.2.2.2.2.1
  obtain ⟨e, he⟩ := K.exists_equiv_principalAngleIndices_of_orthogonal_blocks
    (K.map T.toLinearMap) W horthI hspanI hKI hLI
  let s (i : I) : Equiv.Perm (Fin (Module.finrank ℝ (A i))) :=
    if Module.finrank ℝ (W i) = 4 then Fin.revPerm else Equiv.refl _
  have hs (i : I) : Function.Involutive (s i) := by
    intro j
    dsimp [s]
    split_ifs <;> simp [Fin.revPerm, Fin.rev_rev]
  let S := Equiv.sigmaCongrRight s
  have hS : Function.Involutive S := by
    rintro ⟨i, j⟩
    change (⟨i, s i (s i j)⟩ : Σ i, Fin (Module.finrank ℝ (A i))) = ⟨i, j⟩
    rw [hs i]
  refine ⟨(e.trans S).trans e.symm, ?_, ?_⟩
  · intro j
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (congrArg e.symm (hS (e j))).trans (e.symm_apply_apply j)
  · have htheta : (fun j : Fin (Module.finrank ℝ K) =>
        K.principalAngles (K.map T.toLinearMap) j) = (fun x => theta x.1 x.2) ∘ e := by
      funext j
      exact (he j).symm
    rw [htheta, realSchattenMatchingCost_reindex, realSchattenMatchingCost_sigma, hcost]
    apply Finset.sum_congr rfl
    intro i _
    unfold realSchattenAngleBlockCost
    dsimp [s]
    by_cases hfour : Module.finrank ℝ (W i) = 4
    · rw [ite_eq_left hfour, ite_eq_left hfour]
      have hrank : Module.finrank ℝ (A i) = 2 := (hH i.val i.property).2.2.2.1 hfour
      change realSchattenMatchingCost p.toReal
        (fun j : Fin (Module.finrank ℝ (A i)) => (A i).principalAngles (B i) j) Fin.revPerm = _
      rw [hrank]
      exact realSchattenMatchingCost_rev_two _ _ ((A i).principalAngles_antitone (B i) zero_le_one)
    · rw [ite_eq_right hfour, ite_eq_right hfour, realSchattenMatchingCost_refl]

private theorem starProjection_map_real (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) :
    (K.map T.toLinearMap).starProjection =
      (T : E →L[ℝ] E) * K.starProjection * star (T : E →L[ℝ] E) := by
  ext x
  rw [Submodule.starProjection_map_apply]
  change T (K.starProjection (T.symm x)) = T (K.starProjection (star (T : E →L[ℝ] E) x))
  rw [show star (T : E →L[ℝ] E) = (T.symm : E →L[ℝ] E) from T.adjoint_eq_symm]
  rfl

/-- Every ambient real orthogonal transporter dominates the cost of some
matching on the original accepted angle indices. Compact attainment is
used only to pass to an actual global minimizer before extracting its
matching. Thus the comparison imposes no stationarity or block-preservation
hypothesis on the given competitor. -/
theorem exists_matching_cost_le_real_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) :
    ∃ s : Equiv.Perm (Fin (Module.finrank ℝ K)), Function.Involutive s ∧
      realSchattenMatchingCost p.toReal
        (fun j : Fin (Module.finrank ℝ K) => K.principalAngles (K.map T.toLinearMap) j) s ≤
        UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  let U₀ := Unitary.linearIsometryEquiv.symm T
  obtain ⟨U, htrans, hmin⟩ := exists_schatten_transport_minimizer p hp K.starProjection
    ((U₀ : E →L[ℝ] E) * K.starProjection * star (U₀ : E →L[ℝ] E)) U₀ rfl
  let R := Unitary.linearIsometryEquiv U
  have hR : (R : E →L[ℝ] E) = (U : E →L[ℝ] E) :=
    Unitary.coe_linearIsometryEquiv_apply U
  have hminR : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W =
        (R : E →L[ℝ] E) * K.starProjection * star (R : E →L[ℝ] E)} (R : E →L[ℝ] E) := by
    simpa only [hR, htrans] using hmin
  obtain ⟨s, hs, hcost⟩ := exists_matching_cost_eq_of_isMinOn_real_transport
    p hp hp1 hp2 K R hminR
  have htarget : K.map R.toLinearMap = K.map T.toLinearMap := by
    have hproj : (K.map R.toLinearMap).starProjection = (K.map T.toLinearMap).starProjection := by
      rw [starProjection_map_real, starProjection_map_real, hR, htrans]
      simp only [U₀, Unitary.coe_symm_linearIsometryEquiv_apply]
    rw [← Submodule.range_starProjection (K.map R.toLinearMap),
      ← Submodule.range_starProjection (K.map T.toLinearMap), hproj]
  refine ⟨s, hs, ?_⟩
  simp only [htarget] at hcost
  rw [hcost]
  have hbound := hmin ⟨U₀.property, rfl⟩
  change UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - (U : E →L[ℝ] E).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - (U₀ : E →L[ℝ] E).toLinearMap) ^ p.toReal at hbound
  have hlin (V : E ≃ₗᵢ[ℝ] E) : (V : E →L[ℝ] E).toLinearMap = V.toLinearMap := by
    ext x
    rfl
  have hU₀ : (U₀ : E →L[ℝ] E) = (T : E →L[ℝ] E) :=
    Unitary.coe_symm_linearIsometryEquiv_apply T
  rw [← hR, hU₀, hlin, hlin] at hbound
  exact hbound

/-- The finite matching minimum is a global lower bound over every
ambient real orthogonal competitor, in arbitrary finite dimension and
source rank. The reverse inequality requires ambient matching attainment. -/
theorem realSchattenMatchingMinimum_le_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) :
    realSchattenMatchingMinimum p.toReal
        (fun j : Fin (Module.finrank ℝ K) => K.principalAngles (K.map T.toLinearMap) j) ≤
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  obtain ⟨s, hs, hcost⟩ := exists_matching_cost_le_real_transport p hp hp1 hp2 K T
  exact (realSchattenMatchingMinimum_le _ _ s hs).trans hcost

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
