/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerGradientBranches
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralRestriction
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Actual smoothed-power gradient blocks

The common angular level sets determine the unitary restrictions on actual
gradient eigenspaces. Source reflection pairs opposite levels at an ambient
constrained local minimum. The zero-gradient restriction is self-adjoint;
maximal levels have a single critical phase. Multiplicities and empty
subspaces are retained throughout.

The spectral-restriction and reflection-pairing ingredients are classical.
The proof extends the earlier `SmoothedGradientBlocks`/`SmoothedGradientPairing`
argument using the common family phase law, not the Charbonnier optimum.
Historical priority of the transport consequences remains unresolved.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
private theorem gradient_mapsTo_eigenspace (p tau : ℝ)
    (U : unitary (E →L[ℂ] E)) (c : ℂ) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    ∀ x ∈ Module.End.eigenspace G.toLinearMap c,
      (U : E →L[ℂ] E) x ∈ Module.End.eigenspace G.toLinearMap c := by
  let := isStarNormal_of_mem_unitary U.property
  have hcomm : Commute
      (unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)).toLinearMap
      (U : E →L[ℂ] E).toLinearMap :=
    congrArg _root_.ContinuousLinearMap.toLinearMap
      (commute_unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)).eq
  exact Module.End.mapsTo_genEigenspace_of_comm hcomm c 1

private theorem two_phase_representation_on_invariant_subspace
    (p tau g a b : ℝ) (U : unitary (E →L[ℂ] E)) (N : Submodule ℂ E)
    (hinv : ∀ x ∈ N, (U : E →L[ℂ] E) x ∈ N)
    (hG : ∀ x ∈ N,
      unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E) x =
        (g : ℂ) • x)
    (hlevel : ∀ t : ℝ, |t| ≤ Real.pi → smoothedPowerPhaseSlope p tau t = g →
      Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) ∨
        Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I)) :
    ∃ (V : N ≃ₗᵢ[ℂ] N) (P : N →L[ℂ] N),
      IsStarProjection P ∧ (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : N →L[ℂ] N) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
        (Complex.exp ((b : ℂ) * Complex.I) -
          Complex.exp ((a : ℂ) * Complex.I)) • P := by
  apply exists_two_phase_restriction_of_cfc_level
    (fun z => (smoothedPowerPhaseDerivative p tau z : ℂ)) (g : ℂ)
    (Complex.exp ((a : ℂ) * Complex.I)) (Complex.exp ((b : ℂ) * Complex.I)) U N hinv hG
  intro z hz hg
  have hphase : Complex.exp (((z.arg : ℝ) : ℂ) * Complex.I) = z := by
    simpa only [hz, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
  have hreal : smoothedPowerPhaseSlope p tau z.arg = g := by
    rw [← smoothedPowerPhaseDerivative_exp, hphase]
    exact_mod_cast hg
  simpa only [hphase] using hlevel z.arg (Complex.abs_arg_le_pi z) hreal

/-- Opposite submaximal gradient eigenspaces carry an actual common phase
pair, represented by orthogonal spectral projections on their respective
carriers. No optimality assumption is needed. -/
theorem opposite_gradient_eigenspaces_two_phase_representation
    (p tau g : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hg0 : 0 < g) (hgm : g < peakSlope p tau) (U : unitary (E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    let Nplus := Module.End.eigenspace G.toLinearMap (g : ℂ)
    let Nminus := Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ)
    ∃ a ∈ Ioo 0 (criticalAngle p tau), ∃ b ∈ Ioo (criticalAngle p tau) Real.pi,
      smoothedPowerPhaseSlope p tau a = g ∧ smoothedPowerPhaseSlope p tau b = g ∧
      (∃ (V : Nplus ≃ₗᵢ[ℂ] Nplus) (A : Nplus →L[ℂ] Nplus),
        IsStarProjection A ∧ (∀ x : Nplus, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (V : Nplus →L[ℂ] Nplus) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
          (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A) ∧
      (∃ (V : Nminus ≃ₗᵢ[ℂ] Nminus) (B : Nminus →L[ℂ] Nminus),
        IsStarProjection B ∧ (∀ x : Nminus, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (V : Nminus →L[ℂ] Nminus) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
          (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B) := by
  obtain ⟨a, ha, b, hb, hpos, hneg⟩ := phaseSlope_signed_level_sets p tau g hp hp2 htau hg0 hgm
  have hc := criticalAngle_mem p tau hp hp2 htau
  refine ⟨a, ha, b, hb, ?_, ?_, ?_, ?_⟩
  · exact (hpos a (by rw [abs_of_pos ha.1]; linarith [ha.2, hc.2])).2 (Or.inl rfl)
  · exact (hpos b (by rw [abs_of_pos (lt_trans hc.1 hb.1)]; exact hb.2.le)).2 (Or.inr rfl)
  · exact two_phase_representation_on_invariant_subspace p tau g a b U _
      (gradient_mapsTo_eigenspace p tau U (g : ℂ))
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hpos t ht).1 hg with rfl | rfl <;> simp)
  · exact two_phase_representation_on_invariant_subspace p tau (-g) (-a) (-b) U _
      (gradient_mapsTo_eigenspace p tau U ((-g : ℝ) : ℂ))
      (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
      (fun t ht hg => by rcases (hneg t ht).1 hg with rfl | rfl <;> simp)

/-- Source reflection pairs opposite gradient eigenspaces at every local
minimum on the full complex transport fiber. -/
theorem gradient_eigenspace_pairing_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) (g : ℂ) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    ∃ e : Module.End.eigenspace G.toLinearMap g ≃ₗᵢ[ℂ]
        Module.End.eigenspace G.toLinearMap (-g),
      ∀ x, (e x : E) = K.reflection x := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    p tau hp htau K.starProjection Q hP U htrans hmin
  have hJ : (K.reflection : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hJ] at hconj
  have hanti (x : E) : G (K.reflection x) = -K.reflection (G x) := by
    have h := congrArg (fun A : E →L[ℂ] E => A (K.reflection x)) hconj
    change K.reflection (G (K.reflection (K.reflection x))) = -G (K.reflection x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  exact ⟨eigenspaceNegEquivOfInvolution K.reflection K.reflection_involutive
    G.toLinearMap hanti g, fun x => eigenspaceNegEquivOfInvolution_apply _ _ _ _ _ x⟩

/-- At a signed maximal gradient level, the actual unitary restriction is
the scalar critical phase. No local minimality is needed. -/
theorem signed_critical_gradient_eigenspace_representation
    (p tau s : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hs : s = 1 ∨ s = -1) (U : unitary (E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    let g := s * peakSlope p tau
    let N := Module.End.eigenspace G.toLinearMap (g : ℂ)
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : N →L[ℂ] N) = Complex.exp (((s * criticalAngle p tau : ℝ) : ℂ) * Complex.I) • 1 := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let g := s * peakSlope p tau
  let N := Module.End.eigenspace G.toLinearMap (g : ℂ)
  have hlevel (t : ℝ) (ht : |t| ≤ Real.pi) (hg : smoothedPowerPhaseSlope p tau t = g) :
      t = s * criticalAngle p tau := by
    rcases hs with rfl | rfl
    · simpa only [one_mul] using
        (phaseSlope_max_level_set p tau t hp hp2 htau ht).1 (by simpa [g] using hg)
    · have hneg : smoothedPowerPhaseSlope p tau (-t) = peakSlope p tau := by
        rw [phaseSlope_odd, hg]
        simp [g]
      have ht' := (phaseSlope_max_level_set p tau (-t) hp hp2 htau
        (by simpa only [abs_neg] using ht)).1 hneg
      simpa only [neg_one_mul] using (neg_eq_iff_eq_neg.1 ht')
  obtain ⟨V, A, _, hV, hrepr⟩ := two_phase_representation_on_invariant_subspace
    p tau g (s * criticalAngle p tau) (s * criticalAngle p tau) U N
    (gradient_mapsTo_eigenspace p tau U (g : ℂ))
    (fun x hx => Module.End.mem_eigenspace_iff.1 hx)
    (fun t ht hg => Or.inl (congrArg (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I))
      (hlevel t ht hg)))
  refine ⟨V, hV, ?_⟩
  rw [hrepr, sub_self, zero_smul ℂ A, add_zero]

/-- The full zero-gradient restriction is a self-adjoint unitary. This
exceptional sector is retained in the ambient reduction, rather than being
silently dropped from the positive-level decomposition. -/
theorem gradient_kernel_isSelfAdjoint_restriction
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 < tau) (U : unitary (E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    let N := G.toLinearMap.ker
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      IsSelfAdjoint (V : N →L[ℂ] N) := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let N := G.toLinearMap.ker
  have hinv : ∀ x ∈ N, (U : E →L[ℂ] E) x ∈ N := by
    simpa only [Module.End.eigenspace_zero] using gradient_mapsTo_eigenspace p tau U 0
  have hG : ∀ x ∈ N, cfc (fun z => (smoothedPowerPhaseDerivative p tau z : ℂ))
      (U : E →L[ℂ] E) x = (0 : ℂ) • x := by
    intro x hx
    rw [zero_smul]
    exact LinearMap.mem_ker.1 hx
  have hroots (z : ℂ) (hz : ‖z‖ = 1)
      (hg : (smoothedPowerPhaseDerivative p tau z : ℂ) = 0) : z = 1 ∨ z = -1 := by
    have hreal : smoothedPowerPhaseDerivative p tau z = 0 := by exact_mod_cast hg
    rw [smoothedPowerPhaseDerivative_eq] at hreal
    have hcoeff : p * (tau ^ 2 + ‖z - 1‖ ^ 2) ^ ((p - 2) / 2) ≠ 0 :=
      (mul_pos (by linarith) (Real.rpow_pos_of_pos (smoothedPower_radicand_pos tau htau z) _)).ne'
    have him : z.im = 0 := (mul_eq_zero.mp hreal).resolve_left hcoeff
    have hnorm := Complex.normSq_eq_norm_sq z
    rw [hz, one_pow, Complex.normSq_apply, him] at hnorm
    have hre : z.re = 1 ∨ z.re = -1 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).1
      nlinarith
    rcases hre with hre | hre
    · exact Or.inl (Complex.ext hre him)
    · exact Or.inr (Complex.ext (by simpa using hre) (by simpa using him))
  obtain ⟨V, A, hA, hV, hrepr⟩ := exists_two_phase_restriction_of_cfc_level
    (fun z => (smoothedPowerPhaseDerivative p tau z : ℂ)) 0 1 (-1) U N hinv hG hroots
  refine ⟨V, hV, ?_⟩
  rw [hrepr]
  have hone : IsSelfAdjoint (1 : N →L[ℂ] N) := IsSelfAdjoint.one (N →L[ℂ] N)
  have hscalar : IsSelfAdjoint ((-1 : ℂ) - 1) :=
    ((IsSelfAdjoint.one ℂ).neg).sub (IsSelfAdjoint.one ℂ)
  have hscaled : IsSelfAdjoint (((-1 : ℂ) - 1) • (A : N →L[ℂ] N)) :=
    hscalar.smul hA.isSelfAdjoint
  have hsum : IsSelfAdjoint ((1 : N →L[ℂ] N) + ((-1 : ℂ) - 1) • A) :=
    IsSelfAdjoint.add (R := N →L[ℂ] N) hone hscaled
  simpa only [one_smul] using hsum

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
