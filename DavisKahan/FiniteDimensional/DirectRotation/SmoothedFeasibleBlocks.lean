/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNoMixing
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedBlockCost
public import ForTauCeti.Analysis.InnerProductSpace.PairedTransportVariation

/-!
# Feasible paired Charbonnier variations inside an ambient transporter

Orthogonal extension of the common right variation preserves the actual
source projection and its ambient target. Thus an ambient local minimum
inherits the paired no-overlap condition. The paired block coordinates
are explicit inputs here; their construction from stationarity is downstream.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E R F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] [CompleteSpace R]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- Ambient local minimality transfers to the actual paired curve, with
arbitrary complementary block and arbitrary isometric ambient coordinates. -/
theorem isLocalMin_paired_cost_of_isLocalMinOn_transports_complex
    (tau : ℝ) (U V : unitary (E →L[ℂ] E)) (Z : unitary (R →L[ℂ] R))
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
      (fun T : F →L[ℂ] F => smoothedDisplacementCost tau T.toLinearMap)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) : IsLocalMin (pairedSmoothedCost tau U V H) 0 := by
  apply isLocalMin_paired_variation_of_isLocalMinOn_transports_complex
    (fun T : F →L[ℂ] F => smoothedDisplacementCost tau T.toLinearMap)
    (pairedSmoothedCost tau U V H) (smoothedDisplacementCost tau (Z : R →L[ℂ] R).toLinearMap)
    U V Z H hH e P Q P₀ W hP hW htrans ?_ hmin
  intro t
  rw [smoothedDisplacementCost_conj_linearIsometryEquiv_complex,
    smoothedDisplacementCost_withLpProdMap_complex, smoothedDisplacementCost_withLpProdMap_complex]
  rfl

/-- At an actual ambient local minimum, the negative-curvature phase
projections on any reflection-paired block are disjoint. -/
theorem overlap_eq_zero_of_isLocalMinOn_block_transports_complex
    (tau a b : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I))
    (hbalance : smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I)))
    (hnegative : Real.cos b < ((smoothingRadius tau)⁻¹) ^ 2)
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
      (fun T : F →L[ℂ] F => smoothedDisplacementCost tau T.toLinearMap)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) : A * B = 0 := by
  apply overlap_eq_zero_of_isLocalMin_paired_cost tau a b htau hab hbalance hnegative
    U V A B hA hB hU hV
  exact isLocalMin_paired_cost_of_isLocalMinOn_transports_complex tau U V Z (A * B + B * A)
    (isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint)
    e P Q P₀ W hP hW htrans hmin

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
