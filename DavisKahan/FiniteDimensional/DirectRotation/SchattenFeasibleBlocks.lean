/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenNoMixing
import ForTauCeti.Analysis.Normed.Lp.ProdLp
import ForTauCeti.Analysis.InnerProductSpace.PairedTransportVariation

/-!
# Feasible variations of paired gradient blocks

A common right unitary on two paired spaces commutes with their swapping
reflection. Its orthogonal extension therefore preserves the source projection,
and a local minimum of the ambient transport cost induces a local minimum
of the actual paired cost.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal Topology

variable {E R F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] [CompleteSpace R]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- A local minimum of an ambient transport cost induces a local minimum
on every paired reflection block, with the remaining unitary block fixed.
The coordinate equivalence may change the ambient carrier type. -/
theorem isLocalMin_paired_cost_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (U V : unitary (E →L[ℂ] E)) (Z : unitary (R →L[ℂ] R))
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (e : WithLp 2 (WithLp 2 (E × E) × R) ≃ₗᵢ[ℂ] F)
    (P Q : F →L[ℂ] F) (P₀ : R →L[ℂ] R) (W : unitary (F →L[ℂ] F))
    (hP : P = e.conjStarAlgEquiv
      (((1 / 2 : ℂ) •
        (1 + (LinearIsometryEquiv.withLpProdComm 2 ℂ E E :
          WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)))).withLpProdMap 2 P₀))
    (hW : (W : F →L[ℂ] F) = e.conjStarAlgEquiv
      (((U : E →L[ℂ] E).withLpProdMap 2 (V : E →L[ℂ] E)).withLpProdMap 2
        (Z : R →L[ℂ] R)))
    (htrans : (W : F →L[ℂ] F) * P * star (W : F →L[ℂ] F) = Q)
    (hmin : IsLocalMinOn
      (fun T : F →L[ℂ] F => UnitarilyInvariantSeminorm.schatten ℂ F F p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) :
    IsLocalMin (pairedSchattenCost p U V H) 0 := by
  apply isLocalMin_paired_variation_of_isLocalMinOn_transports_complex
    (fun T : F →L[ℂ] F => UnitarilyInvariantSeminorm.schatten ℂ F F p
      (LinearMap.id - T.toLinearMap) ^ p.toReal) (pairedSchattenCost p U V H)
    (UnitarilyInvariantSeminorm.schatten ℂ R R p
      (LinearMap.id - (Z : R →L[ℂ] R).toLinearMap) ^ p.toReal)
    U V Z H hH e P Q P₀ W hP hW htrans ?_ hmin
  intro t
  rw [schatten_displacement_conj_linearIsometryEquiv e _ p hp,
    schatten_displacement_rpow_withLpProdMap _ _ p hp,
    ← pairedSchattenCost_eq_block_displacement p hp U V H t]

/-- At an ambient transport minimum, the large-phase subspaces on a
paired reflection block are orthogonal. The complementary block is arbitrary. -/
theorem overlap_eq_zero_of_isLocalMinOn_block_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (a b : ℝ) (ha : a ∈ Set.Ioo 0 (criticalAngle p.toReal))
    (hb : b ∈ Set.Ioo (criticalAngle p.toReal) Real.pi)
    (hbalance : phaseAmplitude p.toReal a = phaseAmplitude p.toReal b)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (Z : unitary (R →L[ℂ] R))
    (e : WithLp 2 (WithLp 2 (E × E) × R) ≃ₗᵢ[ℂ] F)
    (P Q : F →L[ℂ] F) (P₀ : R →L[ℂ] R) (W : unitary (F →L[ℂ] F))
    (hP : P = e.conjStarAlgEquiv
      (((1 / 2 : ℂ) •
        (1 + (LinearIsometryEquiv.withLpProdComm 2 ℂ E E :
          WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)))).withLpProdMap 2 P₀))
    (hW : (W : F →L[ℂ] F) = e.conjStarAlgEquiv
      (((U : E →L[ℂ] E).withLpProdMap 2 (V : E →L[ℂ] E)).withLpProdMap 2
        (Z : R →L[ℂ] R)))
    (htrans : (W : F →L[ℂ] F) * P * star (W : F →L[ℂ] F) = Q)
    (hmin : IsLocalMinOn
      (fun T : F →L[ℂ] F => UnitarilyInvariantSeminorm.schatten ℂ F F p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) : A * B = 0 := by
  apply overlap_eq_zero_of_isLocalMin_paired_cost p hp hp1 hp2 a b ha hb hbalance
    U V A B hA hB hU hV
  exact isLocalMin_paired_cost_of_isLocalMinOn_transports p hp U V Z (A * B + B * A)
    (isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint)
    e P Q P₀ W hP hW htrans hmin

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
