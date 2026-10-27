/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6.1 Sol
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealMatchingExponent

/-!
# Unrestricted real nuclear transport matching

Continue the proved unrestricted real Schatten matching theorem to
exponent one. Both sides are minima of jointly continuous functions on
fixed compact sets; on the matching side the set is finite and each
positive pair is itself a compact scalar minimum. This passage includes
zero singular values, right angles and every multiplicity. Compact
attainment supplies an actual ambient nuclear minimizer.

The ambient minimal-distortion problem itself is classical:
Bolotnikov--Li--Rodman (2001), Problem 1.1. The exact unrestricted real
matching formula and its endpoint continuation are candidate extensions;
no equivalent formula was located in the sources examined, and priority
is unresolved. See `dev/spectral-transport-unification.md`, row T7, for
the theorem-level comparison, rather than attributing this entire family
to the classical problem formulation.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual displacement operators of the entire real orthogonal
transport fiber. This includes all determinant classes and all mixing. -/
def realTransportDisplacements (K L : Submodule ℝ E) : Set (E →L[ℝ] E) :=
  (fun W : E →L[ℝ] E => 1-W) ''
    {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W = L.starProjection}

/-- The literal spectral-power minimum over actual ambient transports. -/
def realTransportPowerMinimum (p : ℝ) (K L : Submodule ℝ E) : ℝ :=
  singularValuePowerMinimum p (realTransportDisplacements K L)

/-- The full set of actual real transport displacements is compact. -/
theorem isCompact_realTransportDisplacements (K L : Submodule ℝ E) :
    IsCompact (realTransportDisplacements K L) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (isCompact_unitary_transport_fiber K.starProjection L.starProjection).image
    (continuous_const.sub continuous_id)

/-- The unrestricted finite real transport value is continuous at every
positive exponent; empty fibers are allowed for this continuity statement. -/
theorem continuousOn_realTransportPowerMinimum (K L : Submodule ℝ E) :
    ContinuousOn (fun p => realTransportPowerMinimum p K L) (Ioi 0) :=
  continuousOn_singularValuePowerMinimum (isCompact_realTransportDisplacements K L)

private theorem conjugate_of_map_eq (K L : Submodule ℝ E) (V : E ≃ₗᵢ[ℝ] E)
    (hmap : K.map V.toLinearMap = L) :
    (V : E →L[ℝ] E) * K.starProjection * star (V : E →L[ℝ] E) = L.starProjection := by
  ext x
  change V (K.starProjection (star (V : E →L[ℝ] E) x)) = L.starProjection x
  rw [show star (V : E →L[ℝ] E) = (V.symm : E →L[ℝ] E) from V.adjoint_eq_symm]
  change V (K.starProjection (V.symm x)) = L.starProjection x
  have h := Submodule.starProjection_map_apply V K x
  simpa only [hmap] using h.symm

private theorem displacement_mem_of_map_eq (K L : Submodule ℝ E) (V : E ≃ₗᵢ[ℝ] E)
    (hmap : K.map V.toLinearMap = L) :
    1-(V : E →L[ℝ] E) ∈ realTransportDisplacements K L := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact mem_image_of_mem _ ⟨(Unitary.linearIsometryEquiv.symm V).property,
    conjugate_of_map_eq K L V hmap⟩

omit [FiniteDimensional ℝ E] in
private theorem displacement_toLinearMap (V : E ≃ₗᵢ[ℝ] E) :
    (1-(V : E →L[ℝ] E)).toLinearMap = LinearMap.id - V.toLinearMap := by
  ext x
  rfl

/-- On `1<p<2`, the continuous unrestricted value agrees with the already
proved positive-edge matching minimum on the original positive labels. -/
theorem realTransportPowerMinimum_eq_matching
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    realTransportPowerMinimum p K L = realPositiveSchattenMatchingMinimum p
      (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
        K.principalAngles L j.val) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let q := ENNReal.ofReal p
  have hq : q.toReal = p := ENNReal.toReal_ofReal (by linarith)
  have : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.mpr hp1.le⟩
  have hfinite : q ≠ ∞ := ENNReal.ofReal_ne_top
  obtain ⟨V, hmap, hcost, hmin⟩ := exists_minimizing_real_schatten_transport_matching
    q hfinite (by simpa only [hq] using hp1) (by simpa only [hq] using hp2) K L hKL
  have hminS : IsMinOn (singularValuePowerSum p) (realTransportDisplacements K L)
      (1-(V : E →L[ℝ] E)) := by
    rintro B ⟨W, ⟨hW, htrans⟩, rfl⟩
    let U : unitary (E →L[ℝ] E) := ⟨W, hW⟩
    let T := Unitary.linearIsometryEquiv U
    have hmapT := map_eq_of_unitary_conjugate K L U htrans
    have hbound := hmin T hmapT
    change singularValuePowerSum p (1-(V : E →L[ℝ] E)) ≤
      singularValuePowerSum p (1-(T : E →L[ℝ] E))
    rw [← hq, singularValuePowerSum_eq_schatten_rpow q hfinite,
      singularValuePowerSum_eq_schatten_rpow q hfinite,
      displacement_toLinearMap, displacement_toLinearMap]
    exact hbound
  have hvalue := singularValuePowerMinimum_eq_of_isMinOn p
    (displacement_mem_of_map_eq K L V hmap) hminS
  change realTransportPowerMinimum p K L = _ at hvalue
  rw [hvalue, ← hq, singularValuePowerSum_eq_schatten_rpow q hfinite,
    displacement_toLinearMap, hcost, hq]

/-- The unrestricted real nuclear value equals the closed nuclear matching
minimum. The passage from `1<p<2` uses continuity of both variational
minima, so no nuclear first-variation or smoothness assumption is made. -/
theorem realTransportPowerMinimum_one_eq_nuclearMatching
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    realTransportPowerMinimum 1 K L = realNuclearMatchingMinimum
      (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
        K.principalAngles L j.val) := by
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let theta : J → ℝ := fun j => K.principalAngles L j.val
  have htheta (j : J) : theta j ∈ Icc 0 (Real.pi/2) :=
    ⟨K.principalAngles_nonneg L j.val, K.principalAngles_le_pi_div_two L j.val⟩
  have hf : ContinuousAt (fun p => realTransportPowerMinimum p K L) 1 :=
    ((continuousOn_realTransportPowerMinimum K L) 1 (by norm_num)).continuousAt
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hg : ContinuousAt (fun p => realVariationalMatchingMinimum p theta) 1 :=
    ((continuousOn_realVariationalMatchingMinimum theta) 1 (by norm_num)).continuousAt
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hevent : (fun p => realTransportPowerMinimum p K L) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun p => realVariationalMatchingMinimum p theta) := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with p hp
    exact (realTransportPowerMinimum_eq_matching p hp.1 hp.2 K L hKL).trans
      (realVariationalMatchingMinimum_eq_positive p hp.1 hp.2 theta htheta).symm
  have heq : realTransportPowerMinimum 1 K L = realVariationalMatchingMinimum 1 theta :=
    tendsto_nhds_unique
      ((hf.tendsto.mono_left nhdsWithin_le_nhds).congr' hevent)
      (hg.tendsto.mono_left nhdsWithin_le_nhds)
  exact heq.trans (realVariationalMatchingMinimum_one theta htheta)

private theorem nuclear_displacement (V : E ≃ₗᵢ[ℝ] E) :
    singularValuePowerSum 1 (1-(V : E →L[ℝ] E)) =
      UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - V.toLinearMap) := by
  have h := singularValuePowerSum_eq_schatten_rpow (1 : ℝ≥0∞) (by simp)
    (1-(V : E →L[ℝ] E))
  simpa only [ENNReal.toReal_one, Real.rpow_one, displacement_toLinearMap] using h

/-- The unrestricted real nuclear transport minimum is the closed finite
matching value. An actual ambient orthogonal transporter attains it, and
its accepted nuclear norm bounds every ambient orthogonal competitor.
All zero, repeated and right angles and common ambient directions are
included, with no determinant or prescribed-plane restriction. -/
theorem exists_minimizing_real_nuclear_transport_matching
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    ∃ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - T.toLinearMap) =
        realNuclearMatchingMinimum
          (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
            K.principalAngles L j.val) ∧
      ∀ V : E ≃ₗᵢ[ℝ] E, K.map V.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - T.toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - V.toLinearMap) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let q := ENNReal.ofReal (3/2 : ℝ)
  have hq : q.toReal = (3/2 : ℝ) := ENNReal.toReal_ofReal (by norm_num)
  have : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.mpr (by norm_num)⟩
  obtain ⟨V₀, hV₀, _, _⟩ := exists_minimizing_real_schatten_transport_matching
    q ENNReal.ofReal_ne_top (by rw [hq]; norm_num) (by rw [hq]; norm_num) K L hKL
  have hne : (realTransportDisplacements K L).Nonempty :=
    ⟨_, displacement_mem_of_map_eq K L V₀ hV₀⟩
  obtain ⟨B, hB, hvalue, hmin⟩ := exists_attains_singularValuePowerMinimum
    1 zero_lt_one (isCompact_realTransportDisplacements K L) hne
  rcases hB with ⟨W, ⟨hW, htrans⟩, rfl⟩
  let U : unitary (E →L[ℝ] E) := ⟨W, hW⟩
  let T := Unitary.linearIsometryEquiv U
  have hmap := map_eq_of_unitary_conjugate K L U htrans
  have hvalueT : realTransportPowerMinimum 1 K L =
      singularValuePowerSum 1 (1-(T : E →L[ℝ] E)) := hvalue
  rw [realTransportPowerMinimum_one_eq_nuclearMatching K L hKL,
    nuclear_displacement] at hvalueT
  refine ⟨T, hmap, hvalueT.symm, fun V hV => ?_⟩
  have hbound := hmin (displacement_mem_of_map_eq K L V hV)
  change singularValuePowerSum 1 (1-(T : E →L[ℝ] E)) ≤
    singularValuePowerSum 1 (1-(V : E →L[ℝ] E)) at hbound
  rw [nuclear_displacement, nuclear_displacement] at hbound
  exact hbound

/-- The exact unrestricted real matching theorem on the closed exponent
range `1 ≤ p < 2`. The nuclear endpoint is proved by compact continuation;
the strict range uses the spectral-gradient block classification. -/
theorem exists_minimizing_real_schatten_transport_matching_of_one_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    ∃ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal =
        realPositiveSchattenMatchingMinimum p.toReal
          (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
            K.principalAngles L j.val) ∧
      ∀ V : E ≃ₗᵢ[ℝ] E, K.map V.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - V.toLinearMap) ^ p.toReal := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono hp (show (1 : ℝ≥0∞) ≤ p from Fact.out)
  rcases hp1.eq_or_lt with h1 | hp1
  · have hpEq : p = 1 := (ENNReal.toReal_eq_one_iff p).mp h1.symm
    subst p
    obtain ⟨T, hmap, hcost, hmin⟩ := exists_minimizing_real_nuclear_transport_matching K L hKL
    let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
    let theta : J → ℝ := fun j => K.principalAngles L j.val
    have htheta (j : J) : theta j ∈ Icc 0 (Real.pi/2) :=
      ⟨K.principalAngles_nonneg L j.val, K.principalAngles_le_pi_div_two L j.val⟩
    have hm := realPositiveSchattenMatchingMinimum_one theta htheta
    have hc : UnitarilyInvariantSeminorm.schatten ℝ E E 1
        (LinearMap.id - T.toLinearMap) = realPositiveSchattenMatchingMinimum 1 theta :=
      hcost.trans hm.symm
    refine ⟨T, hmap, ?_, fun V hV => ?_⟩
    · simpa only [ENNReal.toReal_one, Real.rpow_one] using hc
    · simpa only [ENNReal.toReal_one, Real.rpow_one] using hmin V hV
  · exact exists_minimizing_real_schatten_transport_matching p hp hp1 hp2 K L hKL

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
