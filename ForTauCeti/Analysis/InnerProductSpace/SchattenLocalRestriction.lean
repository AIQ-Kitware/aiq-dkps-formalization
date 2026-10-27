/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenMinimizerRestriction
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryTailHomeomorph
public import Mathlib.Topology.Order.LocalExtr

/-!
# Actual reducing restrictions of local Schatten minima

Local optimality in operator norm descends to every actual reducing
sector. Both the retained sector and its unchanged complement may be
infinite-dimensional. Native finite cost justifies cancelling the tail.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology TauCeti.LinearIsometryEquivOperatorNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A finite-cost native local minimum restricts to a finite-cost native
local minimum on every source-reducing sector that reduces the unitary.
The topology on both unitary groups is operator norm. -/
theorem exists_schatten_locally_minimizing_reducing_restriction
    (p : ℝ) (hp : 1 ≤ p)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] [CompleteSpace M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E)))
      {T | K.map T.toLinearMap = L} U)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : M.IsReducing U.toLinearMap) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : M →L[𝕜] M)) ≠ ∞ ∧
      IsLocalMinOn
        (fun W : M ≃ₗᵢ[𝕜] M => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M)))
        {W | (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype} V := by
  let Φ := OperatorIdealFamily.schatten 𝕜 p hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let := K.hasOrthogonalProjection_comap_subtype_of_complete M
  let := L.hasOrthogonalProjection_comap_subtype_of_complete M
  obtain ⟨e, hhead, _⟩ := U.exists_reference_tail_homeomorph M hUM
  let Tail := {T : E ≃ₗᵢ[𝕜] E | ∀ x ∈ Mᗮ, T x = U x}
  let u : Tail := ⟨U, fun _ _ => rfl⟩
  let V := e.symm u
  let f (W : M ≃ₗᵢ[𝕜] M) := (e W).val
  have hfV : f V = U := congrArg Subtype.val (e.apply_symm_apply u)
  have hV (x : M) : (V x : E) = U x := (hhead V x).symm.trans
    (congrArg (fun T : E ≃ₗᵢ[𝕜] E => T x) hfV)
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M U V hmap hV
  have hinvhead (T : Tail) (x : M) : (e.symm T x : E) = T.val x := by
    have h := hhead (e.symm T) x
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hfeasible (W : M ≃ₗᵢ[𝕜] M)
      (hW : (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype) :
      K.map (f W).toLinearMap = L := by
    obtain ⟨T, hTmap, hTM, hTtail⟩ :=
      K.exists_transport_replacing_reducing_block L M hK U hmap hUM W hW
    let t : Tail := ⟨T, hTtail⟩
    have hpre : e.symm t = W := by
      ext x
      exact (hinvhead t x).trans (hTM x)
    have heq : t = e W := e.symm_apply_eq.mp hpre
    exact (congrArg (fun T : Tail => K.map T.val.toLinearMap) heq).symm.trans hTmap
  let tail := Φ.gauge (Mᗮ.orthogonalProjectionOnto ∘L
    (1 - (U : E →L[𝕜] E)) ∘L Mᗮ.subtypeL) ^ p
  have hsplit (W : M ≃ₗᵢ[𝕜] M) :
      Φ.gauge (1 - (f W : E →L[𝕜] E)) ^ p =
        Φ.gauge (1 - (W : M →L[𝕜] M)) ^ p + tail :=
    ContinuousLinearMap.gauge_schatten_unitary_displacement_rpow_eq_block_add_tail p hp M
      (f W) U W (hhead W) (e W).property
  have hfinite' := ENNReal.rpow_ne_top_of_nonneg hp0.le hfinite
  rw [← hfV, hsplit] at hfinite'
  obtain ⟨_, htail⟩ := ENNReal.add_ne_top.mp hfinite'
  have hVle : Φ.gauge (1 - (V : M →L[𝕜] M)) ≤ Φ.gauge (1 - (U : E →L[𝕜] E)) := by
    apply (ENNReal.rpow_le_rpow_iff hp0).mp
    rw [← hfV, hsplit]
    exact le_self_add
  have hVfinite := ne_top_of_le_ne_top hfinite hVle
  refine ⟨V, hV, hlocal, hVfinite, ?_⟩
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hloc : IsLocalMinOn
      (fun T : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E)))
      {T | K.map T.toLinearMap = L} (f V) := by rwa [hfV]
  have hcomp := hloc.comp_continuousOn
    (s := {W : M ≃ₗᵢ[𝕜] M |
      (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype})
    (fun W hW => hfeasible W hW) hf.continuousOn hlocal
  change ∀ᶠ (W : M ≃ₗᵢ[𝕜] M) in
      𝓝[{W | (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype}] V,
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : M →L[𝕜] M)) ≤
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M))
  filter_upwards [hcomp] with W hW
  change Φ.gauge (1 - (f V : E →L[𝕜] E)) ≤
    Φ.gauge (1 - (f W : E →L[𝕜] E)) at hW
  have hpow := ENNReal.rpow_le_rpow hW hp0.le
  rw [hsplit, hsplit] at hpow
  exact (ENNReal.rpow_le_rpow_iff hp0).mp
    ((ENNReal.add_le_add_iff_right htail).mp hpow)

/-- The finite-sector specialization needs only forward invariance of
the actual ambient unitary. Its complementary action is unchanged. -/
theorem exists_schatten_locally_minimizing_finite_restriction
    (p : ℝ) (hp : 1 ≤ p)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E)))
      {T | K.map T.toLinearMap = L} U)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : ∀ x ∈ M, U x ∈ M) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : M →L[𝕜] M)) ≠ ∞ ∧
      IsLocalMinOn
        (fun W : M ≃ₗᵢ[𝕜] M => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M)))
        {W | (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype} V := by
  obtain ⟨_, _, _, hred⟩ := U.exists_restriction_of_finite_invariant M hUM
  exact exists_schatten_locally_minimizing_reducing_restriction p hp K L M U hmap
    hfinite hmin hK hred

end TauCeti
