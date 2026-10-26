/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.OperatorIdeal.ApproximationNumbers.Core
public import DavisKahan.OperatorIdeal.ApproximationNumbers.Real
public import DavisKahan.OperatorIdeal.CanonicalRealView
public import TauCeti.Analysis.OperatorIdeal.Family.KyFan.Dominance

/-!
# Scalar-generic approximation-number endpoints and ideal families

This public module assembles the lower approximation-number foundation with
its complex and real analytic endpoints. The scalar-generic endpoint wrappers
and the downstream Ky Fan dominant ideal families live here, above both
scalar-specific implementations, avoiding the former real-proof import cycle.

The strong-cutoff capability is scalar-generic. Ideal comparisons use accepted
`SymmetricOperatorIdealFamily` carriers with the native
`OperatorIdealFamily.IsKyFanDominant` property. Analytic kernels request ideal
completeness separately. Real estimates use `SymmetricOperatorIdealFamily.gaugeReal`.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open scoped ENNReal
open Filter

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Analytic capability asserting strong-cutoff convergence for approximation
numbers over a scalar field.  This is separated from `RCLike`: the latter is
an open algebraic typeclass, while this property is currently established for
the standard real and complex scalar fields. -/
class HasApproximationNumberStrongCutoff
    (𝕜 : Type u) [RCLike 𝕜] : Prop where
  tendsto_comp_strongProjection :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι},
      (∀ i, IsOrthogonalProjectionMap (P i)) →
      StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E) →
      ∀ (n : ℕ) (K : E →L[𝕜] F),
        Tendsto
          (fun i => approximationSingularValue n (K ∘L P i))
          l (𝓝 (approximationSingularValue n K))

/-- The strong-cutoff convergence holds over `ℝ`.  Supplied as an instance so
the field-generic development can be used at `ℝ` without naming the real proof. -/
instance realHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff.{0, v, w} ℝ where
  tendsto_comp_strongProjection :=
    ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real

/-- The strong-cutoff convergence holds over `ℂ`. -/
instance complexHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff.{0, v, w} ℂ where
  tendsto_comp_strongProjection :=
    approximationSingularValue_comp_strongProjection_tendsto_complex

/-- Real-Hilbert-space continuity of approximation numbers under strongly
convergent orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {ι : Type w} {P : ι → ER →L[ℝ] ER} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ ER))
    (n : ℕ) (K : ER →L[ℝ] FR) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
    hPproj hP n K

/-- Real-Hilbert-space finite Ky Fan convergence under strongly convergent
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {ι : Type w} {P : ι → ER →L[ℝ] ER} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ ER))
    (k : ℕ) (K : ER →L[ℝ] FR) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) :=
  ApproximationNumbersReal.kyFanApproximationGauge_comp_strongProjection_tendsto_real
    hPproj hP k K

/-- Continuity of each approximation number under strongly convergent
orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff.{u, v, w} 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  HasApproximationNumberStrongCutoff.tendsto_comp_strongProjection
    (𝕜 := 𝕜) hPproj hP n K

omit [CompleteSpace F] in
/-- Ky Fan's addition inequality for approximation numbers. -/
theorem kyFanApproximationGauge_add_le
    (k : ℕ) (K L : E →L[𝕜] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  by
    change ((K + L).kyFanGauge k : ℝ) ≤ K.kyFanGauge k + L.kyFanGauge k
    exact_mod_cast ContinuousLinearMap.kyFanGauge_add_le K L k


/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff.{u, v, w} 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGaugeReal_eq_sum]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto
      hPproj hP n K)

/-- Finite Ky Fan majorization transfers finite ideal membership and the real gauge bound. -/
theorem mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'} (hB : N.Mem B)
    (h : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.Mem A ∧ N.gaugeReal A ≤ N.gaugeReal B := by
  have hle : N.gauge A ≤ N.gauge B := by
    apply OperatorIdealFamily.gauge_le_of_forall_kyFanGauge_le
    intro k
    exact_mod_cast h k
  exact ⟨ne_top_of_le_ne_top hB hle, ENNReal.toReal_mono hB hle⟩

/-- Scaled Fan dominance in the exact form consumed by the Sylvester theorem. -/
theorem mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'} {δ : ℝ}
    (hδ : 0 < δ)
    (hB : N.Mem B)
    (h : ∀ k, δ * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.Mem A ∧
      δ * N.gaugeReal A ≤
        N.gaugeReal B := by
  let d : 𝕜 := (δ : 𝕜)
  have hd : d ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
  have hdnorm : ‖d‖ = δ := by
    simp [d, abs_of_pos hδ]
  have hscaled : ∀ k,
      kyFanApproximationGauge k (d • A) ≤
        kyFanApproximationGauge k B := by
    intro k
    rw [kyFanApproximationGauge_smul, hdnorm]
    exact h k
  obtain ⟨hdA, hgauge⟩ := mem_and_gauge_le_of_all_kyFanApproximationGauge_le N hB hscaled
  have hA : N.Mem A := by
    have hinv := N.smul_mem d⁻¹ hdA
    rw [← mul_smul, inv_mul_cancel₀ hd, one_smul] at hinv
    exact hinv
  refine ⟨hA, ?_⟩
  have hhom : N.gaugeReal (d • A) = ‖d‖ * N.gaugeReal A :=
    N.gaugeReal_smul d hA
  rw [hdnorm] at hhom
  linarith

/-- **A Ky Fan gauge is unchanged by moving an orthogonal projection across the
adjoint.**

`‖P K‖_(k) = ‖K⋆ P‖_(k)` for an orthogonal projection `P`.  Derived identically
in `Sylvester/Unbounded/OrderedCutoff.lean` and
`Sylvester/Unbounded/OrderedFromCutoffs.lean`, which share no import edge. -/
theorem kyFanApproximationGauge_proj_comp_eq_adjoint_comp
    {k : ℕ} {P : F →L[𝕜] F} (hP : IsOrthogonalProjectionMap P) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (P ∘L K) =
      kyFanApproximationGauge k (K.adjoint ∘L P) := by
  rw [← kyFanApproximationGauge_adjoint k (P ∘L K)]
  simp only [ContinuousLinearMap.adjoint_comp]
  rw [hP.2.clm_adjoint_eq]

end ExactSinTheta
end DavisKahan
end TauCeti
