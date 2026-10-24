/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientSpectrum
import ForTauCeti.Analysis.CStarAlgebra.TwoPointSpectrum

/-!
# Two-phase restrictions on positive Schatten-gradient levels

Each gradient eigenspace is invariant under the unitary. On a positive
submaximal level, the restricted unitary is affine in an orthogonal
projection, with the two scalar phases furnished by the amplitude theorem.
This constructs the operator blocks rather than only constraining individual
eigenvectors. The relation between the projections on opposite levels is a
separate optimization step.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
private theorem two_phase_representation_on_invariant_subspace
    (p g a b : ℝ) (U : unitary (E →L[ℂ] E)) (K : Submodule ℂ E)
    (hinv : ∀ x ∈ K, (U : E →L[ℂ] E) x ∈ K)
    (hG : ∀ x ∈ K, schattenUnitaryGradient p (U : E →L[ℂ] E) x = (g : ℂ) • x)
    (hlevel : ∀ t : ℝ, |t| ≤ Real.pi →
      schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g →
        Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) ∨
          Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I)) :
    ∃ (V : K ≃ₗᵢ[ℂ] K) (P : K →L[ℂ] K),
      IsStarProjection P ∧
      (∀ x : K, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : K →L[ℂ] K) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
        (Complex.exp ((b : ℂ) * Complex.I) -
          Complex.exp ((a : ℂ) * Complex.I)) • P := by
  let v : K →ₗᵢ[ℂ] K :=
    { (U : E →L[ℂ] E).toLinearMap.restrict hinv with
      norm_map' := fun x => _root_.ContinuousLinearMap.norm_map_of_mem_unitary U.2 x }
  let V : K ≃ₗᵢ[ℂ] K := v.toLinearIsometryEquiv rfl
  let : IsStarNormal (V : K →L[ℂ] K) := by
    constructor
    change ContinuousLinearMap.adjoint (V : K →L[ℂ] K) * (V : K →L[ℂ] K) =
      (V : K →L[ℂ] K) * ContinuousLinearMap.adjoint (V : K →L[ℂ] K)
    rw [V.adjoint_eq_symm]
    ext x
    simp
  have hV (x : K) : (V x : E) = (U : E →L[ℂ] E) x := rfl
  have hs : spectrum ℂ (V : K →L[ℂ] K) ⊆
      {Complex.exp ((a : ℂ) * Complex.I), Complex.exp ((b : ℂ) * Complex.I)} := by
    intro mu hmu
    rw [_root_.ContinuousLinearMap.spectrum_eq] at hmu
    obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.2 hmu).exists_hasEigenvector
    have hx0 : (x : E) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hxU : (U : E →L[ℂ] E) (x : E) = mu • (x : E) := by
      have h := congrArg (fun y : K => (y : E)) hx.apply_eq_smul
      exact (hV x).symm.trans h
    have hnorm : ‖mu‖ = 1 := by
      have h := _root_.ContinuousLinearMap.norm_map_of_mem_unitary U.2 (x : E)
      rw [hxU, norm_smul] at h
      exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx0) (by simpa using h)
    have hphase : Complex.exp (((mu.arg : ℝ) : ℂ) * Complex.I) = mu := by
      simpa only [hnorm, Complex.ofReal_one, one_mul] using
        Complex.norm_mul_exp_arg_mul_I mu
    have hxG : schattenUnitaryGradient p (U : E →L[ℂ] E) (x : E) =
        (g : ℂ) • (x : E) :=
      hG x x.2
    have hsymbol := schattenUnitaryGradient_apply_of_apply_eq_smul p
      (U : E →L[ℂ] E) (x : E) mu hxU
    rw [hxG] at hsymbol
    have hreal : schattenPhaseDerivative p mu = g := by
      exact_mod_cast (smul_left_injective ℂ hx0 hsymbol).symm
    have hroot := hlevel mu.arg (Complex.abs_arg_le_pi mu) (by rwa [hphase])
    simpa only [hphase, Set.mem_insert_iff, Set.mem_singleton_iff] using hroot
  obtain ⟨P, hP, hrepr⟩ := exists_isStarProjection_eq_affine_of_spectrum_subset_pair
    (V : K →L[ℂ] K) (Complex.exp ((a : ℂ) * Complex.I))
      (Complex.exp ((b : ℂ) * Complex.I)) hs
  exact ⟨V, P, hP, hV, hrepr⟩

/-- A positive submaximal gradient eigenspace carries a unitary restriction
with exactly two allowed phases, represented by a star projection. -/
theorem gradient_eigenspace_two_phase_representation
    (p g : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p))
    (U : unitary (E →L[ℂ] E)) :
    let K := Module.End.eigenspace
      (schattenUnitaryGradient p (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      ∃ (V : K ≃ₗᵢ[ℂ] K) (P : K →L[ℂ] K),
        IsStarProjection P ∧
        (∀ x : K, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (V : K →L[ℂ] K) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
          (Complex.exp ((b : ℂ) * Complex.I) -
            Complex.exp ((a : ℂ) * Complex.I)) • P := by
  let G := schattenUnitaryGradient p (U : E →L[ℂ] E)
  let K := Module.End.eigenspace G.toLinearMap (g : ℂ)
  have hinv : ∀ x ∈ K, (U : E →L[ℂ] E) x ∈ K := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change G x = (g : ℂ) • x at hx
    change G ((U : E →L[ℂ] E) x) = (g : ℂ) • (U : E →L[ℂ] E) x
    have hcomm := congrArg (fun A : E →L[ℂ] E => A x)
      (commute_schattenUnitaryGradient p (U : E →L[ℂ] E)).eq
    change G ((U : E →L[ℂ] E) x) = (U : E →L[ℂ] E) (G x) at hcomm
    rw [hcomm, hx, map_smul]
  obtain ⟨a, ha, b, hb, hlevel⟩ := schattenPhaseDerivative_level_set p g hp1 hp2 hg0 hgm
  obtain ⟨V, P, hP, hV, hrepr⟩ := two_phase_representation_on_invariant_subspace
    p g a b U K hinv (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hlevel t ht).1 hg with rfl | rfl <;> simp)
  exact ⟨a, ha, b, hb, V, P, hP, hV, hrepr⟩

/-- Opposite positive and negative gradient levels use a common pair of
phase roots, with opposite signs in their two projection representations. -/
theorem opposite_gradient_eigenspaces_two_phase_representation
    (p g : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p))
    (U : unitary (E →L[ℂ] E)) :
    let G := schattenUnitaryGradient p (U : E →L[ℂ] E)
    let Kplus := Module.End.eigenspace G.toLinearMap (g : ℂ)
    let Kminus := Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ)
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      phaseAmplitude p a = phaseAmplitude p b ∧
      (∃ (V : Kplus ≃ₗᵢ[ℂ] Kplus) (A : Kplus →L[ℂ] Kplus),
        IsStarProjection A ∧
        (∀ x : Kplus, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (V : Kplus →L[ℂ] Kplus) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
          (Complex.exp ((b : ℂ) * Complex.I) -
            Complex.exp ((a : ℂ) * Complex.I)) • A) ∧
      (∃ (V : Kminus ≃ₗᵢ[ℂ] Kminus) (B : Kminus →L[ℂ] Kminus),
        IsStarProjection B ∧
        (∀ x : Kminus, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (V : Kminus →L[ℂ] Kminus) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
          (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B) := by
  let G := schattenUnitaryGradient p (U : E →L[ℂ] E)
  have hinv (c : ℝ) : ∀ x ∈ Module.End.eigenspace G.toLinearMap (c : ℂ),
      (U : E →L[ℂ] E) x ∈ Module.End.eigenspace G.toLinearMap (c : ℂ) := by
    have hcomm : Commute G.toLinearMap (U : E →L[ℂ] E).toLinearMap :=
      congrArg _root_.ContinuousLinearMap.toLinearMap
        (commute_schattenUnitaryGradient p (U : E →L[ℂ] E)).eq
    exact Module.End.mapsTo_genEigenspace_of_comm hcomm (c : ℂ) 1
  obtain ⟨a, ha, b, hb, hpos, hneg⟩ :=
    schattenPhaseDerivative_signed_level_sets p g hp1 hp2 hg0 hgm
  refine ⟨a, ha, b, hb, ?_, ?_, ?_⟩
  · have hc := criticalAngle_mem p hp1 hp2
    have hap : a ∈ Ioo 0 Real.pi := ⟨ha.1, by linarith [ha.2, hc.2, Real.pi_pos]⟩
    have hbp : b ∈ Ioo 0 Real.pi := ⟨by linarith [hb.1, hc.1], hb.2⟩
    apply mul_left_cancel₀ (by linarith : p ≠ 0)
    rw [← schattenPhaseDerivative_exp_eq_amplitude p a hap,
      ← schattenPhaseDerivative_exp_eq_amplitude p b hbp]
    exact ((hpos a (by rw [abs_of_pos hap.1]; exact hap.2.le)).2 (Or.inl rfl)).trans
      ((hpos b (by rw [abs_of_pos hbp.1]; exact hbp.2.le)).2 (Or.inr rfl)).symm
  · exact two_phase_representation_on_invariant_subspace p g a b U
      (Module.End.eigenspace G.toLinearMap (g : ℂ)) (hinv g)
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hpos t ht).1 hg with rfl | rfl <;> simp)
  · exact two_phase_representation_on_invariant_subspace p (-g) (-a) (-b) U
      (Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ)) (hinv (-g))
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hneg t ht).1 hg with rfl | rfl <;> simp)

/-- The unitary restriction to the zero-gradient space is an actual
orthogonal reflection, represented by its negative-phase projection. -/
theorem gradient_kernel_reflection_representation
    (p : ℝ) (hp : 0 < p) (U : unitary (E →L[ℂ] E)) :
    let L := (schattenUnitaryGradient p (U : E →L[ℂ] E)).toLinearMap.ker
    ∃ (V : L ≃ₗᵢ[ℂ] L) (S : L →L[ℂ] L),
      IsStarProjection S ∧
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : L →L[ℂ] L) = 1 - (2 : ℂ) • S := by
  let G := schattenUnitaryGradient p (U : E →L[ℂ] E)
  let L := G.toLinearMap.ker
  have hinv : ∀ x ∈ L, (U : E →L[ℂ] E) x ∈ L := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change G x = 0 at hx
    have hcomm := congrArg (fun A : E →L[ℂ] E => A x)
      (commute_schattenUnitaryGradient p (U : E →L[ℂ] E)).eq
    change G ((U : E →L[ℂ] E) x) = (U : E →L[ℂ] E) (G x) at hcomm
    change G ((U : E →L[ℂ] E) x) = 0
    rw [hcomm, hx, map_zero]
  obtain ⟨V, S, hS, hV, hrepr⟩ := two_phase_representation_on_invariant_subspace
    p 0 0 Real.pi U L hinv
      (fun x hx => by
        have hx' := LinearMap.mem_ker.1 hx
        change G x = 0 at hx'
        simpa only [Complex.ofReal_zero, zero_smul] using hx')
      (fun t _ hg => by
        have hnorm : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
          simp [Complex.norm_exp]
        have hzero := (schattenPhaseDerivative_eq_zero_iff_of_norm_eq_one p hp _ hnorm).1 hg
        simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.exp_pi_mul_I]
          using hzero)
  refine ⟨V, S, hS, hV, ?_⟩
  calc
    (V : L →L[ℂ] L) = 1 + ((-1 : ℂ) - 1) • S := by
      simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.exp_pi_mul_I,
        one_smul] using hrepr
    _ = 1 - (2 : ℂ) • S := by module

/-- At either signed maximal gradient level, the restricted unitary is
the scalar critical phase. The two submaximal branches have coalesced. -/
theorem signed_critical_gradient_eigenspace_representation
    (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hs : s = 1 ∨ s = -1)
    (U : unitary (E →L[ℂ] E)) :
    let g := s * (p * phaseAmplitude p (criticalAngle p))
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ V : L ≃ₗᵢ[ℂ] L,
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : L →L[ℂ] L) = Complex.exp (((s * criticalAngle p : ℝ) : ℂ) * Complex.I) • 1 := by
  let G := schattenUnitaryGradient p (U : E →L[ℂ] E)
  let g := s * (p * phaseAmplitude p (criticalAngle p))
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
  have hinv : ∀ x ∈ L, (U : E →L[ℂ] E) x ∈ L := by
    have hcomm : Commute G.toLinearMap (U : E →L[ℂ] E).toLinearMap :=
      congrArg _root_.ContinuousLinearMap.toLinearMap
        (commute_schattenUnitaryGradient p (U : E →L[ℂ] E)).eq
    exact Module.End.mapsTo_genEigenspace_of_comm hcomm (g : ℂ) 1
  have hlevel (t : ℝ) (ht : |t| ≤ Real.pi)
      (hg : schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g) :
      t = s * criticalAngle p := by
    rcases hs with rfl | rfl
    · simpa only [one_mul] using
        (schattenPhaseDerivative_max_level_set p t hp1 hp2 ht).1 (by simpa [g] using hg)
    · have hneg : schattenPhaseDerivative p (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) =
          p * phaseAmplitude p (criticalAngle p) := by
        rw [schattenPhaseDerivative_exp_neg, hg]
        simp [g]
      have ht' := (schattenPhaseDerivative_max_level_set p (-t) hp1 hp2
        (by simpa only [abs_neg] using ht)).1 hneg
      simpa only [neg_one_mul] using (neg_eq_iff_eq_neg.1 ht')
  obtain ⟨V, A, _, hV, hrepr⟩ := two_phase_representation_on_invariant_subspace
    p g (s * criticalAngle p) (s * criticalAngle p) U L hinv
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => Or.inl (congrArg (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I))
        (hlevel t ht hg)))
  refine ⟨V, hV, ?_⟩
  rw [hrepr, sub_self]
  change Complex.exp (((s * criticalAngle p : ℝ) : ℂ) * Complex.I) •
    (1 : L →L[ℂ] L) + (0 : ℂ) • A = _
  rw [zero_smul ℂ A, add_zero]

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
