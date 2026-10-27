/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierSpectralTrace
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralVariation
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import ForTauCeti.Analysis.InnerProductSpace.FiniteTransportSupport
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension

/-!
# The Charbonnier phase gradient on arbitrary Hilbert spaces

The existing finite phase symbol and gradient live here without a finite-
dimensional assumption. Their normal functional calculus is continuous
on the unitary group and respects actual reducing restrictions.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ComplexConjugate Topology

/-- The scalar phase derivative in an argument-free form. -/
@[expose] def smoothedPhaseDerivative (tau : ℝ) (z : ℂ) : ℝ :=
  (conj (charbonnierDisplacementGradient tau z) * (Complex.I * z)).re

/-- The phase derivative is the imaginary coordinate divided by the
positive smoothed displacement radius. -/
theorem smoothedPhaseDerivative_eq (tau : ℝ) (z : ℂ) :
    smoothedPhaseDerivative tau z = z.im / Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) := by
  simp only [smoothedPhaseDerivative, charbonnierDisplacementGradient,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, div_eq_mul_inv]
  ring

/-- Zero phase gradient on the unit circle means eigenvalue `1` or `-1`. -/
theorem smoothedPhaseDerivative_eq_zero_iff_of_norm_eq_one
    (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    smoothedPhaseDerivative tau z = 0 ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hzero
    rw [smoothedPhaseDerivative_eq] at hzero
    have him : z.im = 0 := (div_eq_zero_iff.mp hzero).resolve_right
      (charbonnier_radius_pos tau htau z).ne'
    have hsquare : z.re ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq z
      rw [hz, one_pow, Complex.normSq_apply, him] at h
      nlinarith
    rcases sq_eq_one_iff.mp hsquare with hre | hre
    · exact Or.inl (Complex.ext hre him)
    · exact Or.inr (Complex.ext (by simpa using hre) (by simpa using him))
  · rintro (rfl | rfl) <;> simp [smoothedPhaseDerivative_eq]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The actual Charbonnier unitary phase gradient. -/
@[expose] def smoothedUnitaryGradient (tau : ℝ) (U : E →L[ℂ] E) : E →L[ℂ] E :=
  unitaryPhaseGradient (charbonnierDisplacementGradient tau) U

/-- The phase gradient is self-adjoint. -/
theorem isSelfAdjoint_smoothedUnitaryGradient (tau : ℝ) (U : E →L[ℂ] E) :
    IsSelfAdjoint (smoothedUnitaryGradient tau U) :=
  isSelfAdjoint_unitaryPhaseGradient _ _

/-- The phase gradient commutes with the underlying normal operator. -/
theorem commute_smoothedUnitaryGradient
    (tau : ℝ) (U : E →L[ℂ] E) [IsStarNormal U] :
    Commute (smoothedUnitaryGradient tau U) U :=
  commute_unitaryPhaseGradient _ _

/-- Eigenvectors of the transporter have the scalar phase gradient. -/
theorem smoothedUnitaryGradient_apply_of_apply_eq_smul [FiniteDimensional ℂ E]
    (tau : ℝ) (U : E →L[ℂ] E) [IsStarNormal U] (x : E) (mu : ℂ)
    (hx : U x = mu • x) :
    smoothedUnitaryGradient tau U x = (smoothedPhaseDerivative tau mu : ℂ) • x :=
  ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ hx


/-- Positive smoothing makes the scalar phase symbol continuous on
all complex inputs, including zero displacement. -/
theorem continuous_smoothedPhaseDerivative (tau : ℝ) (hτ : 0 < tau) :
    Continuous (smoothedPhaseDerivative tau) := by
  have hr : Continuous (fun z : ℂ => Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2)) := by fun_prop
  exact (Complex.continuous_im.div hr (fun z => (charbonnier_radius_pos tau hτ z).ne')).congr
    (fun z => (smoothedPhaseDerivative_eq tau z).symm)

/-- The smoothed phase gradient is operator-norm continuous on the
whole unitary group in arbitrary Hilbert dimension. -/
theorem continuous_smoothedUnitaryGradient_unitary (tau : ℝ) (hτ : 0 < tau) :
    Continuous (fun U : unitary (E →L[ℂ] E) => smoothedUnitaryGradient tau (U : E →L[ℂ] E)) := by
  change Continuous (fun U : unitary (E →L[ℂ] E) =>
    cfc (fun z => (smoothedPhaseDerivative tau z : ℂ)) (U : E →L[ℂ] E))
  exact continuous_subtype_val.cfc' (isCompact_sphere (0 : ℂ) 1)
    (fun z => (smoothedPhaseDerivative tau z : ℂ))
    (fun U => spectrum.subset_circle_of_unitary U.property)
    (Complex.continuous_ofReal.comp (continuous_smoothedPhaseDerivative tau hτ)).continuousOn
    (fun U => isStarNormal_of_mem_unitary U.property)

/-- Actual unitary restriction commutes with the continuous phase
gradient calculus. Both the carrier and ambient space may be infinite. -/
theorem smoothedUnitaryGradient_apply_of_unitary_restriction
    (tau : ℝ) (hτ : 0 < tau) (M : Submodule ℂ E) [CompleteSpace M]
    (U : E ≃ₗᵢ[ℂ] E) (V : M ≃ₗᵢ[ℂ] M)
    (hV : ∀ x : M, (V x : E) = U x) (x : M) :
    (smoothedUnitaryGradient tau (V : M →L[ℂ] M) x : E) =
      smoothedUnitaryGradient tau (U : E →L[ℂ] E) (x : E) := by
  have hUunit := (Unitary.linearIsometryEquiv.symm U).property
  have hVunit := (Unitary.linearIsometryEquiv.symm V).property
  have hinter : M.subtypeL ∘L (V : M →L[ℂ] M) = (U : E →L[ℂ] E) ∘L M.subtypeL := by
    ext y
    exact hV y
  have hinterStar := ContinuousLinearMap.comp_star_eq_star_comp_of_mem_unitary M.subtypeL
    hVunit hUunit hinter
  have h := ContinuousLinearMap.comp_cfc_eq_cfc_comp M.subtypeL hinter hinterStar
    (fun z => (smoothedPhaseDerivative tau z : ℂ))
    (Complex.continuous_ofReal.comp (continuous_smoothedPhaseDerivative tau hτ)).continuousOn
    (Complex.continuous_ofReal.comp (continuous_smoothedPhaseDerivative tau hτ)).continuousOn
    (isStarNormal_of_mem_unitary hVunit) (isStarNormal_of_mem_unitary hUunit)
  exact congrArg (fun T : M →L[ℂ] E => T x) h

/-- The identity contributes no phase gradient, in any Hilbert dimension. -/
@[simp] theorem smoothedUnitaryGradient_one (tau : ℝ) :
    smoothedUnitaryGradient tau (1 : E →L[ℂ] E) = 0 := by
  rw [smoothedUnitaryGradient, unitaryPhaseGradient,
    show (1 : E →L[ℂ] E) = algebraMap ℂ (E →L[ℂ] E) 1 by simp,
    cfc_algebraMap]
  simp [charbonnierDisplacementGradient]

/-- A finite-rank unitary displacement has compact phase gradient.
The gradient vanishes on the entire fixed complement, even if it is
infinite-dimensional or nonseparable. -/
theorem isCompactOperator_smoothedUnitaryGradient_of_finite_rank
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E)
    (n : ℕ) (hU : (1 - (U : E →L[ℂ] E)).rank ≤ n) :
    IsCompactOperator (smoothedUnitaryGradient tau (U : E →L[ℂ] E)) := by
  obtain ⟨M, hM, _, _, hUM, _, hfix⟩ :=
    exists_finite_transport_support (⊥ : Submodule ℂ E) ⊥ U n hU
  let : FiniteDimensional ℂ M := hM
  obtain ⟨V, hV, _, _⟩ := U.exists_restriction_of_finite_invariant M hUM.mem_invtSubmodule
  have hext : smoothedUnitaryGradient tau (U : E →L[ℂ] E) = M.subtypeL ∘L
      smoothedUnitaryGradient tau (V : M →L[ℂ] M) ∘L M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      exact (smoothedUnitaryGradient_apply_of_unitary_restriction tau hτ M U V hV x).symm
    · intro x hx
      have h := smoothedUnitaryGradient_apply_of_unitary_restriction tau hτ Mᗮ U
        (LinearIsometryEquiv.refl ℂ Mᗮ) (fun y => (hfix y y.property).symm) ⟨x, hx⟩
      change (smoothedUnitaryGradient tau (1 : Mᗮ →L[ℂ] Mᗮ) ⟨x, hx⟩ : E) = _ at h
      rw [smoothedUnitaryGradient_one, zero_apply] at h
      exact h.symm
  rw [hext]
  have hGcompact : IsCompactOperator (smoothedUnitaryGradient tau (V : M →L[ℂ] M)) :=
    (isCompactOperator_id : IsCompactOperator (_root_.id : M → M)).clm_comp _
  exact (hGcompact.comp_clm M.orthogonalProjectionOnto).clm_comp M.subtypeL

/-- A compact perturbation of the identity in the unitary group has
compact phase gradient at every positive smoothing scale. Every nonzero gradient
eigenspace is finite-dimensional, without a separability assumption. -/
theorem isCompactOperator_smoothedUnitaryGradient
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E)
    (hU : IsCompactOperator (((U : E →L[ℂ] E) - 1) : E →L[ℂ] E)) :
    IsCompactOperator (smoothedUnitaryGradient tau (U : E →L[ℂ] E)) := by
  obtain ⟨V, N, hN, hlim, _, _, _, _⟩ := exists_finite_unitary_approximation_sequence U hU
  have hlimunit : Tendsto (fun n => Unitary.linearIsometryEquiv.symm (V n)) atTop
      (𝓝 (Unitary.linearIsometryEquiv.symm U)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using hlim
  have hgrad := ((continuous_smoothedUnitaryGradient_unitary tau hτ).tendsto
    (Unitary.linearIsometryEquiv.symm U)).comp hlimunit
  simp only [Unitary.coe_symm_linearIsometryEquiv_apply] at hgrad
  exact isCompactOperator_of_tendsto hgrad (Eventually.of_forall fun n =>
    isCompactOperator_smoothedUnitaryGradient_of_finite_rank tau hτ (V n) (N n) (hN n))

end TauCeti
