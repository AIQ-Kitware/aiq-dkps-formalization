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
      schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g → t = a ∨ t = b) :
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
    have harg : mu.arg = a ∨ mu.arg = b :=
      hlevel mu.arg (Complex.abs_arg_le_pi mu) (by rwa [hphase])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases harg with heq | heq
    · exact Or.inl (by rw [← hphase, heq])
    · exact Or.inr (by rw [← hphase, heq])
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
      (fun t ht hg => (hlevel t ht).1 hg)
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
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · exact two_phase_representation_on_invariant_subspace p g a b U
      (Module.End.eigenspace G.toLinearMap (g : ℂ)) (hinv g)
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx) (fun t ht hg => (hpos t ht).1 hg)
  · exact two_phase_representation_on_invariant_subspace p (-g) (-a) (-b) U
      (Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ)) (hinv (-g))
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx) (fun t ht hg => (hneg t ht).1 hg)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
