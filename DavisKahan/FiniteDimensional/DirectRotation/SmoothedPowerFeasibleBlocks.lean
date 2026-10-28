/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerVariation
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralCost
public import ForTauCeti.Analysis.InnerProductSpace.PairedTransportVariation

/-!
# Feasible ambient variations of smoothed-power spectral blocks

The actual family trace splits in paired reflection coordinates. The
existing generic feasible-variation theorem then transfers an ambient
constrained local minimum to the paired cost, proving no overlap.
This fills the feasibility obligation of C1 once the actual blocks have
been constructed; it does not assume independent principal planes.

The proof adapts `SmoothedFeasibleBlocks` using classical arbitrary-penalty
spectral cost identities and the already shared transport geometry.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

variable {E R F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] [CompleteSpace R]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- Actual ambient local minimality transfers to the common paired curve.
The cost splitting needs no convexity or positive-smoothing assumption. -/
theorem isLocalMin_paired_cost_of_isLocalMinOn_transports
    (p tau : ℝ) (U V : unitary (E →L[ℂ] E)) (Z : unitary (R →L[ℂ] R))
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
    (hmin : IsLocalMinOn (displacementCost p tau)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q} (W : F →L[ℂ] F)) :
    IsLocalMin (fun t : ℝ =>
      displacementCost p tau ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))) +
      displacementCost p tau ((V : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H)))) 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  apply isLocalMin_paired_variation_of_isLocalMinOn_transports_complex
    (displacementCost p tau) _ (displacementCost p tau (Z : R →L[ℂ] R))
    U V Z H hH e P Q P₀ W hP hW htrans ?_ hmin
  intro t
  have hexp : NormedSpace.exp (t • (Complex.I • H)) ∈ unitary (E →L[ℂ] E) := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  let A : unitary (E →L[ℂ] E) := ⟨_, mul_mem U.2 hexp⟩
  let B : unitary (E →L[ℂ] E) := ⟨_, mul_mem V.2 hexp⟩
  let AB : unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) :=
    ⟨(A : E →L[ℂ] E).withLpProdMap 2 (B : E →L[ℂ] E),
      ContinuousLinearMap.withLpProdMap_mem_unitary A.2 B.2⟩
  let C : unitary (WithLp 2 (WithLp 2 (E × E) × R) →L[ℂ]
      WithLp 2 (WithLp 2 (E × E) × R)) :=
    ⟨(AB : _ →L[ℂ] _).withLpProdMap 2 (Z : R →L[ℂ] R),
      ContinuousLinearMap.withLpProdMap_mem_unitary AB.2 Z.2⟩
  let rho := fun s : ℝ => (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p
  change normalDisplacementSpectralCost rho (e.conjStarAlgEquiv (C : _ →L[ℂ] _)) =
    normalDisplacementSpectralCost rho (A : E →L[ℂ] E) +
      normalDisplacementSpectralCost rho (B : E →L[ℂ] E) +
        normalDisplacementSpectralCost rho (Z : R →L[ℂ] R)
  rw [normalDisplacementSpectralCost_conj rho e C,
    normalDisplacementSpectralCost_withLpProdMap rho AB Z,
    normalDisplacementSpectralCost_withLpProdMap rho A B]

/-- At an actual ambient local minimum, high-phase spectral projections
in any reflection-paired reducing block are disjoint. -/
theorem overlap_eq_zero_of_isLocalMinOn_block_transports
    (p tau a b : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hab : Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I))
    (hbalance : smoothedPowerPhaseSlope p tau a = smoothedPowerPhaseSlope p tau b)
    (hnegative : Real.cos b < smoothedPowerCriticalCosine p tau)
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
    (hmin : IsLocalMinOn (displacementCost p tau)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q} (W : F →L[ℂ] F)) : A * B = 0 := by
  apply highPhaseProjections_mul_eq_zero_of_localMin p tau a b hp hp2 htau hab hbalance
    hnegative U V A B hA hB hU hV
  exact isLocalMin_paired_cost_of_isLocalMinOn_transports p tau U V Z (A * B + B * A)
    (isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint)
    e P Q P₀ W hP hW htrans hmin

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
