/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientPlanes
public import ForTauCeti.Analysis.InnerProductSpace.PositiveSpectralBasis

/-!
# Simultaneous phase coordinates on the whole positive gradient space

The symmetric gradient restricted to its positive point-spectral space has
an internal orthogonal eigenspace decomposition. On each level we use the
phase basis supplied by constrained local minimality, rather than an arbitrary
spectral basis. Mathlib's collected orthonormal basis then combines the levels
without losing the transporter or reflection-paired eigenvector equations.

This constructs coordinates on the entire positive space, including repeated
levels and the maximal level. Pairing this basis by source reflection and
adjoining the gradient kernel gives the subsequent ambient decomposition.
The construction also permits the positive space to be zero-dimensional.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The entire positive gradient space at a constrained local minimum has
an orthonormal phase basis. Source reflection pairs every vector with an
opposite-gradient eigenvector, and every pair attains its exact scalar cost. -/
theorem positive_gradient_phase_basis_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
    let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
    ∃ n : ℕ, ∃ (e : OrthonormalBasis (Fin n) ℂ H) (g alpha beta : Fin n → ℝ),
      (∀ i, 0 < g i) ∧
      (∀ i, G (e i : E) = (g i : ℂ) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (e i : E) =
        Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i)) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, ‖1 - Complex.exp ((alpha i : ℂ) * Complex.I)‖ ^ p.toReal +
        ‖1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
          phaseMinimum p.toReal ((alpha i + beta i) / 2)) ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let D (_ : ℝ) (x : E) : Prop := ∃ a b : ℝ,
    (U : E →L[ℂ] E) x = Complex.exp ((a : ℂ) * Complex.I) • x ∧
    (U : E →L[ℂ] E) (K.reflection x) =
      Complex.exp (((-b : ℝ) : ℂ) * Complex.I) • K.reflection x ∧
    (a + b) / 2 ∈ Ioo 0 (Real.pi / 2) ∧
    ‖1 - Complex.exp ((a : ℂ) * Complex.I)‖ ^ p.toReal +
      ‖1 - Complex.exp (((-b : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
        phaseMinimum p.toReal ((a + b) / 2) ∧
    a ∈ Ioo 0 Real.pi ∧ b ∈ Ioo 0 Real.pi
  have hG : G.toLinearMap.IsSymmetric :=
    (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).isSymmetric
  have hlevel (r : ℝ) (hr : 0 < r)
      (hs : Module.End.HasEigenvalue G.toLinearMap (r : ℂ)) :
      ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ
        (Module.End.eigenspace G.toLinearMap (r : ℂ)))) ℂ
          (Module.End.eigenspace G.toLinearMap (r : ℂ)), ∀ i, D r (b i : E) := by
    have hspec : (r : ℂ) ∈ spectrum ℂ G := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hs
    obtain ⟨b, alpha, beta, hu, hw, hmean, hcost, hbounds⟩ :=
      gradient_eigenspace_phase_basis_of_isLocalMinOn_transports_complex
        p hp hp1 hp2 K Q U htrans hmin r hr hspec
    exact ⟨b, fun i => ⟨alpha i, beta i, hu i, hw i, hmean i, hcost i, hbounds i⟩⟩
  obtain ⟨n, e, g, hg, hGe, hD⟩ :=
    hG.exists_positive_spectral_basis_of_eigenspace_bases D hlevel
  choose alpha beta hu hw hmean hcost hbounds using hD
  exact ⟨n, e, g, alpha, beta, hg, hGe, hu, hw, hmean, hcost, hbounds⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
