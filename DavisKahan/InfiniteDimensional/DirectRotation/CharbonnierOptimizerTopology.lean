/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerClassification
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedParameterTopology
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryTailHomeomorph

/-!
# Operator-norm topology of every Hilbert Charbonnier optimizer

The complete ambient optimizer set is homeomorphic to the finite
optimizer set on any positive subcritical principal-sine cutoff.
The extension preserves operator-norm differences exactly. Thus the
infinite-dimensional optimizer set is compact and its finite
multiplicity coordinates retain their actual topology.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- All globally minimizing ambient unitary transporters in the native
extended Charbonnier trace. No finite-cost or prescribed-block assumption
is built into the set. -/
def charbonnierHilbertTransportMinimizers
    (tau : ℝ) (K L : Submodule ℂ E) : Set (E ≃ₗᵢ[ℂ] E) :=
  {U | K.map U.toLinearMap = L ∧
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau}

omit [CompleteSpace E] in
@[simp]
theorem mem_charbonnierHilbertTransportMinimizers_complex
    (tau : ℝ) (K L : Submodule ℂ E) (U : E ≃ₗᵢ[ℂ] E) :
    U ∈ charbonnierHilbertTransportMinimizers tau K L ↔
      K.map U.toLinearMap = L ∧
        ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
          (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
            (1 - (T : E →L[ℂ] E)).charbonnierCost tau := Iff.rfl

/-- The full infinite-dimensional optimizer family is homeomorphic to
its actual finite cutoff optimizer family. Every ambient optimizer is
included, and the extension preserves operator-norm differences exactly. -/
theorem exists_charbonnier_finite_cutoff_optimizer_homeomorph_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (smoothedCriticalAngle tau)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
        (K.starProjection - L.starProjection) hD) c hc).1
    Module.finrank ℂ (K.comap M.subtype) = Module.finrank ℂ (L.comap M.subtype) ∧
    ∃ e : smoothedTransportMinimizers tau (K.comap M.subtype) (L.comap M.subtype) ≃ₜ
        charbonnierHilbertTransportMinimizers tau K L,
      (∀ V (x : M), (e V).val x = (V.val x : E)) ∧
      (∀ V, ∀ x ∈ Mᗮ, (e V).val x = nonacuteDirectRotation K L J x) ∧
      ∀ V W, ‖((e V).val : E →L[ℂ] E) - ((e W).val : E →L[ℂ] E)‖ =
        ‖(V.val : M →L[ℂ] M) - (W.val : M →L[ℂ] M)‖ := by
  classical
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L J
  have hRred : M.IsReducing R.toLinearMap :=
    sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hcompact c hc
  obtain ⟨Vref, hVref, _, _⟩ :=
    R.exists_restriction_of_finite_invariant M hRred.mem_invtSubmodule
  have hVrefmap := K.map_comap_subtype_of_isometry_restriction L M R Vref hRmap hVref
  have hdim : Module.finrank ℂ (K.comap M.subtype) = Module.finrank ℂ (L.comap M.subtype) := by
    have h := Vref.toLinearEquiv.finrank_map_eq (K.comap M.subtype)
    rw [hVrefmap] at h
    exact h.symm
  obtain ⟨e₀, hhead, hnorm⟩ := LinearIsometryEquiv.exists_reference_tail_homeomorph M R hRred
  let Tail := {U : E ≃ₗᵢ[ℂ] E | ∀ x ∈ Mᗮ, U x = R x}
  have hinvhead (U : Tail) (x : M) : (e₀.symm U x : E) = U.val x := by
    have h := hhead (e₀.symm U) x
    rw [e₀.apply_symm_apply] at h
    exact h.symm
  have hminiff (V : M ≃ₗᵢ[ℂ] M) (hmap : K.map (e₀ V).val.toLinearMap = L) :
      (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - ((e₀ V).val : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau) ↔
      (∀ W : M ≃ₗᵢ[ℂ] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        smoothedDisplacementCost tau V.toLinearMap ≤
          smoothedDisplacementCost tau W.toLinearMap) := by
    have h := charbonnier_minimal_iff_canonical_tail_finite_minimal_complex
      tau hτ K L J hD c hc hc1 hcrit (e₀ V).val hmap
    dsimp only at h
    constructor
    · intro hmin
      obtain ⟨_, W, hW, _, hWmin⟩ := h.mp hmin
      have heq : W = V := by
        ext x
        exact (hW x).trans (hhead V x)
      subst W
      exact hWmin
    · intro hmin
      exact h.mpr ⟨(e₀ V).property, V, fun x => (hhead V x).symm,
        K.map_comap_subtype_of_isometry_restriction L M (e₀ V).val V hmap
          (fun x => (hhead V x).symm), hmin⟩
  have hiff (V : M ≃ₗᵢ[ℂ] M) :
      V ∈ smoothedTransportMinimizers tau (K.comap M.subtype) (L.comap M.subtype) ↔
        (e₀ V).val ∈ charbonnierHilbertTransportMinimizers tau K L := by
    constructor
    · intro hV
      rw [mem_smoothedTransportMinimizers_complex] at hV
      obtain ⟨T, hTmap, hTM, hTtail, _⟩ := K.exists_transport_replacing_finite_block L M
        hK R hRmap hRred.mem_invtSubmodule V hV.1
      let T' : Tail := ⟨T, hTtail⟩
      have hpre : e₀.symm T' = V := by
        ext x
        exact (hinvhead T' x).trans (hTM x)
      have heq : T' = e₀ V := e₀.symm_apply_eq.mp hpre
      have hmap : K.map (e₀ V).val.toLinearMap = L := by
        exact (congrArg (fun U : Tail => K.map U.val.toLinearMap) heq).symm.trans hTmap
      exact ⟨hmap, (hminiff V hmap).mpr hV.2⟩
    · intro hU
      rw [mem_smoothedTransportMinimizers_complex]
      exact ⟨K.map_comap_subtype_of_isometry_restriction L M (e₀ V).val V hU.1
        (fun x => (hhead V x).symm), (hminiff V hU.1).mp hU.2⟩
  have htail (U : charbonnierHilbertTransportMinimizers tau K L) :
      ∀ x ∈ Mᗮ, U.val x = R x :=
    ((charbonnier_minimal_iff_canonical_tail_finite_minimal_complex
      tau hτ K L J hD c hc hc1 hcrit U.val U.property.1).mp U.property.2).1
  let flatten : {U : Tail | U.val ∈ charbonnierHilbertTransportMinimizers tau K L} ≃ₜ
      charbonnierHilbertTransportMinimizers tau K L :=
    { toFun := fun U => ⟨U.val.val, U.property⟩
      invFun := fun U => ⟨⟨U.val, htail U⟩, U.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let e := (e₀.subtype hiff).trans flatten
  exact ⟨hdim, e, fun V x => hhead V.val x, fun V => (e₀ V.val).property,
    fun V W => hnorm V.val W.val⟩

/-- The full ambient complex Charbonnier optimizer set is compact in
operator norm even in infinite Hilbert dimension. The compact family
includes all angle multiplicities, right defects and fixed directions. -/
theorem isCompact_charbonnierHilbertTransportMinimizers_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    IsCompact (charbonnierHilbertTransportMinimizers tau K L) := by
  let c := Real.sin (smoothedCriticalAngle tau) / 2
  have hcangle := smoothedCriticalAngle_mem tau hτ
  have hsin : 0 < Real.sin (smoothedCriticalAngle tau) :=
    Real.sin_pos_of_pos_of_lt_pi hcangle.1 (by linarith [hcangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (smoothedCriticalAngle tau)]
  have hcrit : c ≤ Real.sin (smoothedCriticalAngle tau) := by dsimp only [c]; linarith
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
      (K.starProjection - L.starProjection) hD) c hc).1
  obtain ⟨hdim, e, _, _, _⟩ := exists_charbonnier_finite_cutoff_optimizer_homeomorph_complex
    tau hτ K L J hD c hc hc1 hcrit
  let : CompactSpace (smoothedTransportMinimizers tau (K.comap M.subtype) (L.comap M.subtype)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_smoothedTransportMinimizers tau hτ
        (K.comap M.subtype) (L.comap M.subtype) hdim)
  exact isCompact_iff_compactSpace.mpr e.compactSpace

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
