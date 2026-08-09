/-
Compactness, boundedness, and response-regularity bridges for raw-response Quench.

The final theorem should not expose finite nets, covering-number certificates,
replicate-mean Lipschitz proofs, population-mean Lipschitz proofs, or response
norm envelopes as independent assumptions.  This module derives those objects
from finite-dimensional compactness and one pathwise raw-response Lipschitz
condition.
-/

import DkpsQuench2026.Response.RawSampling
import DkpsQuench2026.Rates.PolynomialCover

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

open Acharyya2024
open Acharyya2025.GrowingResponse

universe u v wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- A probability measure cannot live on an empty model type.
-/
theorem nonempty_model_of_probability
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf] :
    Nonempty (Model Q X) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have huniv : (Set.univ : Set (Model Q X)) = ∅ := Set.univ_eq_empty_iff.mpr h
  have h1 : Pf Set.univ = 1 := measure_univ
  rw [huniv, measure_empty] at h1
  exact one_ne_zero h1.symm

/-- A population response map on a finite model class has a uniform norm
bound automatically.

Use the maximum of the finite set of norms, enlarged by zero.  This theorem
removes the explicit population response envelope from the finite-model final
interface.
-/
theorem exists_populationMean_norm_bound_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μmodel : Model Q X → Acharyya2024.Mat m p) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖μmodel f‖ ≤ B := by
  obtain ⟨B, hB⟩ := Finite.exists_le (fun f => ‖μmodel f‖)
  exact ⟨max 0 B, le_max_left _ _, fun f => (hB f).trans (le_max_right _ _)⟩

/-- Pathwise raw-response Lipschitzness passes to the concrete replicate mean.

-/
theorem modelReplicateMean_lipschitz_of_raw
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (L : Real)
    (Hlip : RawResponseLipschitz ψ replicates Y L)
    (n : Nat) (ω : Ωresp) (f g : Model Q X) :
    ‖modelReplicateMean replicates Y n ω f -
        modelReplicateMean replicates Y n ω g‖ ≤
      L * ‖ψ f - ψ g‖ := by
  rcases Nat.eq_zero_or_pos (replicates n) with hr | hr
  · have hrr : (replicates n : ℝ) = 0 := by exact_mod_cast hr
    simp only [modelReplicateMean, replicateMean, hrr, inv_zero, zero_smul, sub_self,
      norm_zero]
    exact mul_nonneg Hlip.constant_nonneg (norm_nonneg _)
  · have hr' : (replicates n : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hbound : ‖∑ k, (Y n f k ω - Y n g k ω)‖ ≤
        (replicates n : ℝ) * (L * ‖ψ f - ψ g‖) := by
      calc ‖∑ k, (Y n f k ω - Y n g k ω)‖
          ≤ ∑ k, ‖Y n f k ω - Y n g k ω‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin (replicates n), (L * ‖ψ f - ψ g‖) :=
            Finset.sum_le_sum (fun k _ => Hlip.bound n f g k ω)
        _ = (replicates n : ℝ) * (L * ‖ψ f - ψ g‖) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [modelReplicateMean, replicateMean]
    rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (replicates n : ℝ)⁻¹)]
    calc (replicates n : ℝ)⁻¹ * ‖∑ k, (Y n f k ω - Y n g k ω)‖
        ≤ (replicates n : ℝ)⁻¹ * ((replicates n : ℝ) * (L * ‖ψ f - ψ g‖)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = L * ‖ψ f - ψ g‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hr', one_mul]

/-- Pathwise raw-response Lipschitzness passes to the population mean.

Do not assume population Lipschitzness separately in a final theorem; this is
exactly the bridge that derives it.
-/
theorem populationMean_lipschitz_of_raw
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (L : Real)
    (Hlip : RawResponseLipschitz ψ replicates Y L)
    (n : Nat) (f g : Model Q X) :
    ‖μmodel f - μmodel g‖ ≤ L * ‖ψ f - ψ g‖ := by
  let := Hraw.probability n
  let k : Fin (replicates n) := ⟨0, Hraw.replicates_pos n⟩
  have hintf : Integrable (Y n f k) (μresp n) :=
    (Hraw.memLp_two n f k).integrable one_le_two
  have hintg : Integrable (Y n g k) (μresp n) :=
    (Hraw.memLp_two n g k).integrable one_le_two
  have hmeanf : ∫ ω, Y n f k ω ∂(μresp n) = μmodel f := by
    ext c
    have h : (EuclideanSpace.proj c : Acharyya2024.Mat m p →L[Real] Real)
          (∫ ω, Y n f k ω ∂(μresp n)) =
        ∫ ω, Y n f k ω c ∂(μresp n) :=
      (ContinuousLinearMap.integral_comp_comm _ hintf).symm
    rw [Hraw.mean_entry n f k c] at h
    exact h
  have hmeang : ∫ ω, Y n g k ω ∂(μresp n) = μmodel g := by
    ext c
    have h : (EuclideanSpace.proj c : Acharyya2024.Mat m p →L[Real] Real)
          (∫ ω, Y n g k ω ∂(μresp n)) =
        ∫ ω, Y n g k ω c ∂(μresp n) :=
      (ContinuousLinearMap.integral_comp_comm _ hintg).symm
    rw [Hraw.mean_entry n g k c] at h
    exact h
  calc
    ‖μmodel f - μmodel g‖ =
        ‖∫ ω, (Y n f k ω - Y n g k ω) ∂(μresp n)‖ := by
      rw [integral_sub hintf hintg, hmeanf, hmeang]
    _ ≤ ∫ ω, ‖Y n f k ω - Y n g k ω‖ ∂(μresp n) :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, L * ‖ψ f - ψ g‖ ∂(μresp n) := by
      apply integral_mono_ae
      · exact (hintf.sub hintg).norm
      · exact integrable_const _
      · exact Filter.Eventually.of_forall fun ω => Hlip.bound n f g k ω
    _ = L * ‖ψ f - ψ g‖ := by simp

/-- Construct the two regularity certificates used by finite-net extension from
one pathwise raw-response Lipschitz condition.

The sample and population constants are both the same fixed `L`.  This theorem
is the intended constructor used by the infinite-model capstone.
-/
theorem uniformModelResponseRegularity_of_raw_lipschitz
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (L : Real)
    (Hlip : RawResponseLipschitz ψ replicates Y L) :
    UniformModelResponseRegularity ψ
      (modelReplicateMean replicates Y) μmodel
      (fun _ => L) (fun _ => L) :=
  { sample_nonneg := fun _ => Hlip.constant_nonneg
    population_nonneg := fun _ => Hlip.constant_nonneg
    sample_lipschitz := fun n ω f g =>
      modelReplicateMean_lipschitz_of_raw ψ replicates Y L Hlip n ω f g
    population_lipschitz := fun n f g =>
      populationMean_lipschitz_of_raw μresp ψ replicates Y μmodel variance Hraw L Hlip n f g }

/-- Compact perspective range and population Lipschitzness imply a population
response norm envelope.

Choose an anchor model using `nonempty_model_of_probability`; compactness gives
a perspective norm bound.  Then compare every population response with the
anchor response and use the Lipschitz estimate.  The returned bound may be very
loose; its purpose is to eliminate a caller-visible envelope hypothesis.
-/
theorem exists_populationMean_norm_bound_of_compact_lipschitz
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ))
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (L : Real) (hL : 0 ≤ L)
    (hμlip : ∀ f g,
      ‖μmodel f - μmodel g‖ ≤ L * ‖ψ f - ψ g‖) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖μmodel f‖ ≤ B := by
  obtain ⟨f0⟩ := nonempty_model_of_probability Pf
  obtain ⟨Bψ, hBψ0, hBψ⟩ := exists_perspective_norm_bound_of_isCompact_range ψ hcompact
  refine ⟨max 0 (L * (2 * Bψ) + ‖μmodel f0‖), le_max_left _ _, fun f => ?_⟩
  have hψsub : ‖ψ f - ψ f0‖ ≤ 2 * Bψ :=
    calc ‖ψ f - ψ f0‖ ≤ ‖ψ f‖ + ‖ψ f0‖ := norm_sub_le _ _
      _ ≤ Bψ + Bψ := add_le_add (hBψ f) (hBψ f0)
      _ = 2 * Bψ := by ring
  calc ‖μmodel f‖
      = ‖(μmodel f - μmodel f0) + μmodel f0‖ := by rw [sub_add_cancel]
    _ ≤ ‖μmodel f - μmodel f0‖ + ‖μmodel f0‖ := norm_add_le _ _
    _ ≤ L * ‖ψ f - ψ f0‖ + ‖μmodel f0‖ := by linarith [hμlip f f0]
    _ ≤ L * (2 * Bψ) + ‖μmodel f0‖ := by
        linarith [mul_le_mul_of_nonneg_left hψsub hL]
    _ ≤ max 0 (L * (2 * Bψ) + ‖μmodel f0‖) := le_max_right _ _

/-- Turn polynomial covers at arbitrary radii into a coherent growing finite
net for a prescribed shrinking radius sequence.

No nesting of the nets is required by the later concentration theorem.
-/
theorem exists_growingPerspectiveNet_with_polynomial_card
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ))
    (radius : Nat → Real)
    (hradiusPos : ∀ n, 0 < radius n)
    (hradiusZero : Tendsto radius atTop (𝓝 0)) :
    ∃ net : GrowingPerspectiveNet ψ, ∃ C : Real,
      0 ≤ C ∧
      (∀ n, ((net.centers n).card : Real) ≤
        C * (max 1 (radius n)⁻¹) ^ d) ∧
      (∀ n, net.radius n = radius n) := by
  obtain ⟨C, hC, hcov⟩ := exists_polynomial_perspective_covers_of_isCompact_range ψ hcompact
  choose centers hcover hcard using fun n => hcov (radius n) (hradiusPos n)
  exact ⟨⟨radius, hradiusPos, hradiusZero, centers, hcover⟩, C, hC, hcard, fun _ => rfl⟩

end DkpsQuench2026
