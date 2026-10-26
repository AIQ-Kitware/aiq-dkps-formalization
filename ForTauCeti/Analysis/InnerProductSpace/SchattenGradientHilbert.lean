/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenPhaseSymbol
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import ForTauCeti.Analysis.InnerProductSpace.FiniteTransportSupport
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension

/-!
# The Schatten unitary gradient on arbitrary complex Hilbert space

For exponents greater than one, the phase-gradient symbol is continuous
even at identity. Its normal functional calculus is continuous on the
whole unitary group and respects every actual unitary restriction.
No finite-dimensional differentiation or trace formula is asserted here.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The phase-gradient functional calculus is continuous in operator
norm on the entire unitary group, including at zero displacement. -/
theorem continuous_schattenUnitaryGradient_unitary (p : ℝ) (hp : 1 < p) :
    Continuous (fun U : unitary (E →L[ℂ] E) => schattenUnitaryGradient p (U : E →L[ℂ] E)) := by
  simp only [schattenUnitaryGradient_def]
  exact continuous_subtype_val.cfc' (isCompact_sphere (0 : ℂ) 1)
    (fun z => (schattenPhaseDerivative p z : ℂ))
    (fun U => spectrum.subset_circle_of_unitary U.property)
    (Complex.continuous_ofReal.comp (continuous_schattenPhaseDerivative p hp)).continuousOn
    (fun U => isStarNormal_of_mem_unitary U.property)

/-- Actual unitary restriction commutes with the continuous phase
gradient calculus. Both the carrier and ambient space may be infinite. -/
theorem schattenUnitaryGradient_apply_of_unitary_restriction
    (p : ℝ) (hp : 1 < p) (M : Submodule ℂ E) [CompleteSpace M]
    (U : E ≃ₗᵢ[ℂ] E) (V : M ≃ₗᵢ[ℂ] M)
    (hV : ∀ x : M, (V x : E) = U x) (x : M) :
    (schattenUnitaryGradient p (V : M →L[ℂ] M) x : E) =
      schattenUnitaryGradient p (U : E →L[ℂ] E) (x : E) := by
  have hUunit := (Unitary.linearIsometryEquiv.symm U).property
  have hVunit := (Unitary.linearIsometryEquiv.symm V).property
  have hinter : M.subtypeL ∘L (V : M →L[ℂ] M) = (U : E →L[ℂ] E) ∘L M.subtypeL := by
    ext y
    exact hV y
  have hinterStar := ContinuousLinearMap.comp_star_eq_star_comp_of_mem_unitary M.subtypeL
    hVunit hUunit hinter
  have h := ContinuousLinearMap.comp_cfc_eq_cfc_comp M.subtypeL hinter hinterStar
    (fun z => (schattenPhaseDerivative p z : ℂ))
    (Complex.continuous_ofReal.comp (continuous_schattenPhaseDerivative p hp)).continuousOn
    (Complex.continuous_ofReal.comp (continuous_schattenPhaseDerivative p hp)).continuousOn
    (isStarNormal_of_mem_unitary hVunit) (isStarNormal_of_mem_unitary hUunit)
  simp only [schattenUnitaryGradient_def]
  exact congrArg (fun T : M →L[ℂ] E => T x) h

/-- The identity contributes no phase gradient, in any Hilbert dimension. -/
@[simp] theorem schattenUnitaryGradient_one (p : ℝ) :
    schattenUnitaryGradient p (1 : E →L[ℂ] E) = 0 := by
  rw [schattenUnitaryGradient_def,
    show (1 : E →L[ℂ] E) = algebraMap ℂ (E →L[ℂ] E) 1 by simp,
    cfc_algebraMap]
  simp [schattenPhaseDerivative_eq]

/-- A finite-rank unitary displacement has compact phase gradient.
The gradient vanishes on the entire fixed complement, even if it is
infinite-dimensional or nonseparable. -/
theorem isCompactOperator_schattenUnitaryGradient_of_finite_rank
    (p : ℝ) (hp : 1 < p) (U : E ≃ₗᵢ[ℂ] E)
    (n : ℕ) (hU : (1 - (U : E →L[ℂ] E)).rank ≤ n) :
    IsCompactOperator (schattenUnitaryGradient p (U : E →L[ℂ] E)) := by
  obtain ⟨M, hM, _, _, hUM, _, hfix⟩ :=
    exists_finite_transport_support (⊥ : Submodule ℂ E) ⊥ U n hU
  let : FiniteDimensional ℂ M := hM
  obtain ⟨V, hV, _, _⟩ := U.exists_restriction_of_finite_invariant M hUM.mem_invtSubmodule
  have hext : schattenUnitaryGradient p (U : E →L[ℂ] E) = M.subtypeL ∘L
      schattenUnitaryGradient p (V : M →L[ℂ] M) ∘L M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      exact (schattenUnitaryGradient_apply_of_unitary_restriction p hp M U V hV x).symm
    · intro x hx
      have h := schattenUnitaryGradient_apply_of_unitary_restriction p hp Mᗮ U
        (LinearIsometryEquiv.refl ℂ Mᗮ) (fun y => (hfix y y.property).symm) ⟨x, hx⟩
      change (schattenUnitaryGradient p (1 : Mᗮ →L[ℂ] Mᗮ) ⟨x, hx⟩ : E) = _ at h
      rw [schattenUnitaryGradient_one, zero_apply] at h
      exact h.symm
  rw [hext]
  have hGcompact : IsCompactOperator (schattenUnitaryGradient p (V : M →L[ℂ] M)) :=
    (isCompactOperator_id : IsCompactOperator (_root_.id : M → M)).clm_comp _
  exact (hGcompact.comp_clm M.orthogonalProjectionOnto).clm_comp M.subtypeL

/-- A compact perturbation of the identity in the unitary group has
compact phase gradient for `p>1`. In particular every nonzero gradient
eigenspace is finite-dimensional, without a separability assumption. -/
theorem isCompactOperator_schattenUnitaryGradient
    (p : ℝ) (hp : 1 < p) (U : E ≃ₗᵢ[ℂ] E)
    (hU : IsCompactOperator (((U : E →L[ℂ] E) - 1) : E →L[ℂ] E)) :
    IsCompactOperator (schattenUnitaryGradient p (U : E →L[ℂ] E)) := by
  obtain ⟨V, N, hN, hlim, _, _, _, _⟩ := exists_finite_unitary_approximation_sequence U hU
  have hlimunit : Tendsto (fun n => Unitary.linearIsometryEquiv.symm (V n)) atTop
      (𝓝 (Unitary.linearIsometryEquiv.symm U)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using hlim
  have hgrad := ((continuous_schattenUnitaryGradient_unitary p hp).tendsto
    (Unitary.linearIsometryEquiv.symm U)).comp hlimunit
  simp only [Unitary.coe_symm_linearIsometryEquiv_apply] at hgrad
  exact isCompactOperator_of_tendsto hgrad (Eventually.of_forall fun n =>
    isCompactOperator_schattenUnitaryGradient_of_finite_rank p hp (V n) (N n) (hN n))

end TauCeti
