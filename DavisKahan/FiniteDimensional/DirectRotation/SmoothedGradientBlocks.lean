/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientBranches
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import ForTauCeti.Analysis.CStarAlgebra.TwoPointSpectrum
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralRestriction

/-!
# Actual angular Charbonnier-gradient restrictions

The two scalar branches determine the actual unitary restrictions on
opposite gradient eigenspaces. At the maximal signed level the restriction
is a scalar critical phase, including arbitrary multiplicities and empty spaces.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
private theorem two_phase_representation_on_invariant_subspace
    (tau g a b : ℝ) (U : unitary (E →L[ℂ] E)) (K : Submodule ℂ E)
    (hinv : ∀ x ∈ K, (U : E →L[ℂ] E) x ∈ K)
    (hG : ∀ x ∈ K, smoothedUnitaryGradient tau (U : E →L[ℂ] E) x = (g : ℂ) • x)
    (hlevel : ∀ t : ℝ, |t| ≤ Real.pi →
      smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)) = g →
        Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) ∨
          Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I)) :
    ∃ (V : K ≃ₗᵢ[ℂ] K) (P : K →L[ℂ] K),
      IsStarProjection P ∧
      (∀ x : K, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : K →L[ℂ] K) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
        (Complex.exp ((b : ℂ) * Complex.I) -
          Complex.exp ((a : ℂ) * Complex.I)) • P := by
  apply exists_two_phase_restriction_of_cfc_level
    (fun z => (smoothedPhaseDerivative tau z : ℂ)) (g : ℂ)
    (Complex.exp ((a : ℂ) * Complex.I)) (Complex.exp ((b : ℂ) * Complex.I)) U K hinv hG
  intro z hz hg
  have hphase : Complex.exp (((z.arg : ℝ) : ℂ) * Complex.I) = z := by
    simpa only [hz, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
  have hreal : smoothedPhaseDerivative tau z = g := by exact_mod_cast hg
  simpa only [hphase] using hlevel z.arg (Complex.abs_arg_le_pi z) (by rwa [hphase])

/-- Opposite positive and negative gradient levels use a common pair of
phase roots, with opposite signs in their two projection representations. -/
theorem opposite_gradient_eigenspaces_two_phase_representation_complex
    (tau g : ℝ) (htau : 0 < tau) (hg0 : 0 < g)
    (hgm : g < (smoothingRadius tau)⁻¹)
    (U : unitary (E →L[ℂ] E)) :
    let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
    let Kplus := Module.End.eigenspace G.toLinearMap (g : ℂ)
    let Kminus := Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ)
    ∃ a ∈ Ioo 0 (smoothedCriticalAngle tau), ∃ b ∈ Ioo (smoothedCriticalAngle tau) Real.pi,
      smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) = g ∧
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I)) = g ∧
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
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  have hinv (c : ℝ) : ∀ x ∈ Module.End.eigenspace G.toLinearMap (c : ℂ),
      (U : E →L[ℂ] E) x ∈ Module.End.eigenspace G.toLinearMap (c : ℂ) := by
    have hcomm : Commute G.toLinearMap (U : E →L[ℂ] E).toLinearMap :=
      congrArg _root_.ContinuousLinearMap.toLinearMap
        (commute_smoothedUnitaryGradient tau (U : E →L[ℂ] E)).eq
    exact Module.End.mapsTo_genEigenspace_of_comm hcomm (c : ℂ) 1
  obtain ⟨a, ha, b, hb, hpos, hneg⟩ :=
    smoothedPhaseDerivative_signed_level_sets tau g htau hg0 hgm
  refine ⟨a, ha, b, hb, ?_, ?_, ?_, ?_⟩
  · exact (hpos a (by rw [abs_of_pos ha.1]; linarith [ha.2,
      (smoothedCriticalAngle_mem tau htau).2, Real.pi_pos])).2 (Or.inl rfl)
  · exact (hpos b (by rw [abs_of_pos (lt_trans
      (smoothedCriticalAngle_mem tau htau).1 hb.1)]; exact hb.2.le)).2 (Or.inr rfl)
  · exact two_phase_representation_on_invariant_subspace tau g a b U
      (Module.End.eigenspace G.toLinearMap (g : ℂ)) (hinv g)
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hpos t ht).1 hg with rfl | rfl <;> simp)
  · exact two_phase_representation_on_invariant_subspace tau (-g) (-a) (-b) U
      (Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ)) (hinv (-g))
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hneg t ht).1 hg with rfl | rfl <;> simp)

/-- At either signed maximal gradient level, the restricted unitary is
the scalar critical phase. The two submaximal branches have coalesced. -/
theorem signed_critical_gradient_eigenspace_representation_complex
    (tau s : ℝ) (htau : 0 < tau) (hs : s = 1 ∨ s = -1)
    (U : unitary (E →L[ℂ] E)) :
    let g := s * ((smoothingRadius tau)⁻¹)
    let L := Module.End.eigenspace
      (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ V : L ≃ₗᵢ[ℂ] L,
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : L →L[ℂ] L) =
        Complex.exp (((s * smoothedCriticalAngle tau : ℝ) : ℂ) * Complex.I) • 1 := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let g := s * ((smoothingRadius tau)⁻¹)
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
  have hinv : ∀ x ∈ L, (U : E →L[ℂ] E) x ∈ L := by
    have hcomm : Commute G.toLinearMap (U : E →L[ℂ] E).toLinearMap :=
      congrArg _root_.ContinuousLinearMap.toLinearMap
        (commute_smoothedUnitaryGradient tau (U : E →L[ℂ] E)).eq
    exact Module.End.mapsTo_genEigenspace_of_comm hcomm (g : ℂ) 1
  have hlevel (t : ℝ) (ht : |t| ≤ Real.pi)
      (hg : smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)) = g) :
      t = s * smoothedCriticalAngle tau := by
    rcases hs with rfl | rfl
    · simpa only [one_mul] using
        (smoothedPhaseDerivative_max_level_set tau t htau ht).1 (by simpa [g] using hg)
    · have hneg : smoothedPhaseDerivative tau (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) =
          (smoothingRadius tau)⁻¹ := by
        rw [smoothedPhaseDerivative_exp_neg, hg]
        simp [g]
      have ht' := (smoothedPhaseDerivative_max_level_set tau (-t) htau
        (by simpa only [abs_neg] using ht)).1 hneg
      simpa only [neg_one_mul] using (neg_eq_iff_eq_neg.1 ht')
  obtain ⟨V, A, _, hV, hrepr⟩ := two_phase_representation_on_invariant_subspace
    tau g (s * smoothedCriticalAngle tau) (s * smoothedCriticalAngle tau) U L hinv
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => Or.inl (congrArg (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I))
        (hlevel t ht hg)))
  refine ⟨V, hV, ?_⟩
  rw [hrepr, sub_self]
  change Complex.exp (((s * smoothedCriticalAngle tau : ℝ) : ℂ) * Complex.I) •
    (1 : L →L[ℂ] L) + (0 : ℂ) • A = _
  rw [zero_smul ℂ A, add_zero]


end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
