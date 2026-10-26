/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
public import DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization

/-!
# The source norm class is inhabited

`NormalizedUnitaryInvariantNorm` is the Lean type for Davis--Kahan's Section 1
norm class, and every source-exact façade quantifies over it.  A universally
quantified statement over an *empty* type is vacuous, so the façades mean nothing
until the class is shown to have members.

Until 2026-09-05 the repository never constructed one.  This module does: the
`k`-th Ky Fan norm is a member for every `k ≥ 1`, and those are the norms Davis
and Kahan's own Fan-dominance argument runs over.

**What was and was not missing.**  The layer beneath,
`FanDominantIdealFamily`, was already inhabited by
`FanDominantIdealFamily.kyFan`, so this module builds on that rather than
repeating it.  What had no witness was the *normalized* class: the single extra
field `gauge_rankOne_eq_one`, which is the source's `‖u v*‖ = ‖u‖ ‖v‖` after
scaling both vectors to norm one.  It is discharged by
`approximationSingularValue_rankOne`, which says a norm-one rank-one operator has
singular values `1, 0, 0, …`, so the Ky Fan sum of the first `k ≥ 1` of them is
`1`.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-- **The `k`-th Ky Fan norm as a member of the source norm class.** -/
noncomputable def kyFanNormalizedUnitaryInvariantNorm
     (k : ℕ) (hk : 0 < k) :
    NormalizedUnitaryInvariantNorm.{u, v} 𝕜 where
  toFanDominantIdealFamily := FanDominantIdealFamily.kyFan k hk
  gauge_rankOne_eq_one := by
    intro E F _ _ _ _ _ _ V hVnorm hVrank
    rw [FanDominantIdealFamily.kyFan_gauge]
    have hsum : kyFanApproximationGauge k V
        = ∑ n ∈ Finset.range k, approximationSingularValue n V := by
      change V.kyFanGaugeReal k = _
      rw [ContinuousLinearMap.kyFanGaugeReal_eq_sum]
      simp only [approximationSingularValue]
    rw [hsum]
    have hval : ∀ n ∈ Finset.range k,
        approximationSingularValue n V = if n = 0 then 1 else 0 := fun n _ =>
      SymmetricNormingFunction.approximationSingularValue_rankOne hVnorm hVrank n
    rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (1 : ℝ))]
    simp [hk]

/-- The gauge of the Ky Fan member is the Ky Fan gauge, definitionally. -/
@[simp]
theorem gauge_kyFanNormalizedUnitaryInvariantNorm
     (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk).gauge A
      = kyFanApproximationGauge k A :=
  FanDominantIdealFamily.kyFan_gauge k hk A

/-- Every bounded operator lies in the Ky Fan member's ideal. -/
theorem mem_kyFanNormalizedUnitaryInvariantNorm
     (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk).Mem A :=
  FanDominantIdealFamily.kyFan_mem k hk A

/-- **The source norm class is inhabited over `ℂ`.**  So every source-exact
façade quantifying over `NormalizedUnitaryInvariantNorm ℂ` says something. -/
theorem nonempty_normalizedUnitaryInvariantNorm_complex :
    Nonempty (NormalizedUnitaryInvariantNorm.{0, v} ℂ) :=
  ⟨kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) 1 one_pos⟩

/-- **The source norm class is inhabited over `ℝ`.** -/
theorem nonempty_normalizedUnitaryInvariantNorm_real :
    Nonempty (NormalizedUnitaryInvariantNorm.{0, v} ℝ) :=
  ⟨kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℝ) 1 one_pos⟩

end

end ExactSinTheta
end DavisKahan
end TauCeti
