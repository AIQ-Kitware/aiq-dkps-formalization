/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenFrameAttainment
import DavisKahan.FiniteDimensional.DirectRotation.SchattenFunctionalPhase

/-!
# Attainment of every compatible Schatten phase projection

An arbitrary orthogonal projection commuting with canonical rotation and
source reflection admits a compatible paired frame. The positive and
negative attaining scalar phases on its two sectors construct a global
ambient minimum. The relative phase has a formula in terms of the actual
cosine operator and the prescribed projection, independent of that frame.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every compatible orthogonal phase projection occurs in a globally
optimal ambient transporter. Repeated, zero and right angles are included;
competitors are not assumed to preserve any chosen paired frame. -/
theorem exists_schatten_transport_from_projection_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let F := schattenPhaseFactor p.toReal (Proposition35.section3CosAngleOperator K L)
    ∃ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
      (T.trans R.symm : E →L[ℂ] E) = F * P + star F * (1 - P) ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal =
          ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) ∧
      IsMinOn
        (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal)
        {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
        (T : E →L[ℂ] E) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  have hC : IsSelfAdjoint C :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  let F := schattenPhaseFactor p.toReal C
  let F' : unitary (E →L[ℂ] E) := ⟨F, schattenPhaseFactor_mem_unitary _ C inferInstance⟩
  obtain ⟨hPC, n, m, e, theta, eps, sign, hθ, hC0, hC1, hCf,
      hR0, hR1, hRf, hJ0, hJf, hPe⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_projection_basis_complex
      K L hKL P hP hPR hPJ
  change ∀ i, R (e (.inl (0, i))) =
    Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)) at hR0
  change ∀ i, R (e (.inl (1, i))) =
    Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i)) at hR1
  change ∀ j, R (e (.inr j)) = e (.inr j) at hRf
  let delta := fun i => if sign i then optimalPhase p.toReal (theta i)
    else -optimalPhase p.toReal (theta i)
  have hδ (i) : delta i ∈ Icc (-theta i) (theta i) := by
    have hm := (optimalPhase_spec p.toReal (theta i) hp1.le (hθ i).1.le).1
    dsimp only [delta]
    split <;> constructor <;> linarith [hm.1, hm.2, (hθ i).1]
  have hscalar (i) : phasePower p.toReal (theta i) (delta i) =
      phaseMinimum p.toReal (theta i) := by
    have hm := (optimalPhase_spec p.toReal (theta i) hp1.le (hθ i).1.le).2.1
    cases hs : sign i
    · simp only [delta, hs, Bool.false_eq_true, ite_false]
      rw [phasePower,
        show theta i + -optimalPhase p.toReal (theta i) =
          theta i - optimalPhase p.toReal (theta i) by ring,
        show theta i - -optimalPhase p.toReal (theta i) =
          theta i + optimalPhase p.toReal (theta i) by ring, add_comm]
      exact hm
    · simpa only [delta, hs, ite_true] using hm
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L D
  obtain ⟨T, hT, _, _, _, hZp, hZf, hatt, hmin⟩ :=
    exists_schatten_transport_attaining_phases_in_frame_complex p hp hp1 hp2 K L R hRmap
      e theta eps hθ hC0 hC1 hCf hR0 hR1 hRf hJ0 hJf delta hδ hscalar
  have hCp (r : Fin 2) (i : Fin n) : C (e (.inl (r, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (r, i)) := by
    fin_cases r
    · exact hC0 i
    · exact hC1 i
  have hFe (r i) : F (e (.inl (r, i))) =
      Complex.exp ((optimalPhase p.toReal (theta i) : ℂ) * Complex.I) • e (.inl (r, i)) :=
    schattenPhaseFactor_apply_cos p.toReal (theta i) C _
      ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩ (hCp r i)
  have hFse (r i) : star F (e (.inl (r, i))) =
      Complex.exp (((-optimalPhase p.toReal (theta i) : ℝ) : ℂ) * Complex.I) • e (.inl (r, i)) :=
    schattenPhaseFactor_star_apply_cos p.toReal (theta i) C _
      ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩ (hCp r i)
  have hFfix (x : E) (hx : C x = x) : F x = x :=
    schattenPhaseFactor_apply_one p.toReal hp1.le C x hx
  have hFsfix (x : E) (hx : C x = x) : star F x = x := by
    have h := unitary_star_apply_of_apply_eq_smul F' (1 : ℂ) (by simp) x
      (by simpa only [one_smul] using hFfix x hx)
    simpa only [star_one, one_smul] using h
  refine ⟨T, hT, ?_, hatt, hmin⟩
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro j
  change (T.trans R.symm) (e j) = F (P (e j)) + star F (e j - P (e j))
  rcases j with ⟨r, i⟩ | j
  · rw [hZp]
    have he := hPe r i
    cases hs : sign i
    · have hp0 : P (e (.inl (r, i))) = 0 := by simpa [hs] using he
      rw [hp0, map_zero, sub_zero, zero_add, hFse]
      simp only [delta, hs, Bool.false_eq_true, ite_false]
    · have hp1 : P (e (.inl (r, i))) = e (.inl (r, i)) := by simpa [hs] using he
      rw [hp1, sub_self, map_zero, add_zero, hFe]
      simp only [delta, hs, ite_true]
  · have hCP : C (P (e (.inr j))) = P (e (.inr j)) := by
      have h := congrArg (fun A : E →L[ℂ] E => A (e (.inr j))) hPC.eq
      change P (C (e (.inr j))) = C (P (e (.inr j))) at h
      rw [hCf] at h
      exact h.symm
    have hCsub : C (e (.inr j) - P (e (.inr j))) = e (.inr j) - P (e (.inr j)) := by
      rw [map_sub, show C (e (.inr j)) = _ from hCf j, hCP]
    rw [hZf, hFfix _ hCP, hFsfix _ hCsub]
    module

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
