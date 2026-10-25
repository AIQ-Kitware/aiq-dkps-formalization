/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt

/-!
# Further Hilbert–Schmidt consequences

The accepted Hilbert–Schmidt family owns the extended gauge, finite-gauge
submodule, and completeness. No separate norm or membership predicate is defined here.

The remaining results are a pointwise-on-a-basis Fatou bound for the energy,
negation invariance of the real norm, and a contraction estimate for that norm.

## Provenance

These DKPS consequences were authored by Jon Crall and Claude Opus 5. The
parallel extended norm, chosen basis, and ideal-membership API were retired in
favor of `OperatorIdealFamily.hilbertSchmidt`.
-/

public section

open scoped ENNReal NNReal

namespace ContinuousLinearMap

variable {𝕜 E F G H ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Pointwise convergence on a Hilbert basis bounds the limit's energy by the liminf. -/
theorem hilbertSchmidtEnergy_le_liminf {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hptwise : ∀ i, Filter.Tendsto (fun n => ‖T n (b i)‖ₑ ^ 2) u
      (nhds (‖L (b i)‖ₑ ^ 2))) :
    L.hilbertSchmidtEnergy b ≤
      Filter.liminf (fun n => (T n).hilbertSchmidtEnergy b) u := by
  classical
  rw [L.hilbertSchmidtEnergy_eq_iSup_sum b]
  refine iSup_le fun s => ?_
  have hfin : Filter.Tendsto (fun n => ∑ i ∈ s, ‖T n (b i)‖ₑ ^ 2) u
      (nhds (∑ i ∈ s, ‖L (b i)‖ₑ ^ 2)) :=
    tendsto_finsetSum _ fun i _ => hptwise i
  calc ∑ i ∈ s, ‖L (b i)‖ₑ ^ 2
      = Filter.liminf (fun n => ∑ i ∈ s, ‖T n (b i)‖ₑ ^ 2) u := hfin.liminf_eq.symm
    _ ≤ Filter.liminf (fun n => (T n).hilbertSchmidtEnergy b) u :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => by
          rw [hilbertSchmidtEnergy_def]; exact ENNReal.sum_le_tsum s)


omit [CompleteSpace F] in
/-- Negation leaves the canonical real Hilbert–Schmidt norm unchanged. -/
@[simp] theorem hilbertSchmidtNorm_neg (T : E →L[𝕜] F) :
    (-T).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using
    hilbertSchmidtNorm_smul (-1 : 𝕜) T

/-- Contractive factors do not enlarge the Hilbert–Schmidt norm of a finite-energy map. -/
theorem hilbertSchmidtNorm_comp_isometries_le (L : F →L[𝕜] G) {T : E →L[𝕜] F}
    (b : HilbertBasis ι 𝕜 E) (hT : T.hilbertSchmidtEnergy b ≠ ∞)
    (R : H →L[𝕜] E) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    (L ∘L T ∘L R).hilbertSchmidtNorm ≤ T.hilbertSchmidtNorm := by
  calc
    _ ≤ ‖L‖ * T.hilbertSchmidtNorm * ‖R‖ :=
      hilbertSchmidtNorm_comp_comp_le L T R b hT
    _ ≤ 1 * T.hilbertSchmidtNorm * 1 := by
      gcongr <;> simp only [one_mul, T.hilbertSchmidtNorm_nonneg]
    _ = T.hilbertSchmidtNorm := by ring

end ContinuousLinearMap
