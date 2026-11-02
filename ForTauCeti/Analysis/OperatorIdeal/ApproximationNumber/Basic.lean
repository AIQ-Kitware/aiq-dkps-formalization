/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Approximation numbers under a contractive split embedding

The approximation-number definition and elementary calculus are owned by
Tau Ceti. This donor retains only invariance under a contractive embedding
with a contractive left inverse, over arbitrary seminormed spaces and an
arbitrary nontrivially normed field. The accepted isometry-equivalence API
requires surjectivity; this result does not. Its values use the canonical
nonnegative `ContinuousLinearMap.singularValue` directly.

The former real data alias, infimum, norm/rank, homogeneity, monotonicity,
perturbation and ideal-law wrappers are retired. Real scalar consumers apply
native inequalities through `NNReal.coe_le_coe` and native equalities through
`congrArg NNReal.toReal`; no forwarding aliases remain here.

## Provenance of the original calculus

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/Normed/Operator/ApproximationNumber.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations: `ContinuousLinearMap.approximationNumber` and the order
  and ideal API in the same namespace, plus two pieces of plumbing that have
  since moved out so that this module carries approximation-number API and
  nothing else: the universe helper `Cardinal.le_natCast_of_lift_le` (now the iff
  `Cardinal.lift_le_natCast` in `ForTauCeti/SetTheory/Cardinal/Lift.lean`) and
  the rank-of-composition bounds `rank_comp_left_le_of_rank_le` and
  `rank_comp_right_le_rank` (now `ContinuousLinearMap.rank_comp_le_natCast_right`
  and `ContinuousLinearMap.rank_comp_le_left` in
  `ForTauCeti/LinearAlgebra/Dimension/RankComp.lean`, generalized to
  `LinearMap`).
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss,
  Arnav Mehta, Rawad Kansoh; Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* The Davis--Kahan file was itself adapted from Mathlib PR #32126.
* Extraction class: **copied**, converted to the Tau Ceti module system, then
  renamed conclusion-outward per the signature-polish backlog
  No mathematical change; see Appendix A of that document for the name index.
* Spectra influence: **none** — this module has no Spectra dependency and never
  did; it imports only Mathlib.
-/

public section

namespace ContinuousLinearMap

universe u v w x

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} {F : Type w} {G : Type x}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Postcomposition with a contraction having a contractive left inverse preserves
all approximation numbers, without surjectivity, completeness or dimension assumptions. -/
theorem singularValue_comp_eq_of_leftInverse {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι :
    Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (T : E →L[𝕜] F) (n : ℕ) :
    (ι ∘L T).singularValue n = T.singularValue n := by
  have hι' : ‖ι‖₊ ≤ 1 := by exact_mod_cast hι
  have hπ' : ‖π‖₊ ≤ 1 := by exact_mod_cast hπ
  have hcomp : π ∘L (ι ∘L T) = T := by
    ext x
    exact hπι (T x)
  refine le_antisymm ?_ ?_
  · calc (ι ∘L T).singularValue n ≤ ‖ι‖₊ * T.singularValue n :=
          ι.singularValue_comp_le_left T n
      _ ≤ 1 * T.singularValue n := mul_le_mul_of_nonneg_right hι' bot_le
      _ = T.singularValue n := one_mul _
  · calc T.singularValue n = (π ∘L (ι ∘L T)).singularValue n := by rw [hcomp]
      _ ≤ ‖π‖₊ * (ι ∘L T).singularValue n := π.singularValue_comp_le_left _ n
      _ ≤ 1 * (ι ∘L T).singularValue n := mul_le_mul_of_nonneg_right hπ' bot_le
      _ = (ι ∘L T).singularValue n := one_mul _

end ContinuousLinearMap
