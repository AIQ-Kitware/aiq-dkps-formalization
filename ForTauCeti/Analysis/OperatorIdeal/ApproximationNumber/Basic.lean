/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
module

public import ForTauCeti.LinearAlgebra.Dimension.RankComp
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Real scalar statements about canonical approximation numbers

Tau Ceti owns the zero-based sequence
`ContinuousLinearMap.singularValue : ℕ → ℝ≥0`. All maintained formulas now use
that native sequence, with explicit coercions to `ℝ` where real analysis needs
them. The former local `ContinuousLinearMap.approximationNumber` data alias is
retired; no replacement alias or notation is introduced.

The zero-based convention is `a₀(T) = ‖T‖` and
`aₙ(T) = inf {‖T - R‖ | rank R ≤ n}`. The one-based Pietsch convention is
`sₙ = a_{n-1}`. These scalar statements retain arbitrary nontrivially normed
fields and seminormed source/target spaces, without Hilbert, completeness or
dimension hypotheses. The remaining real-valued law statements are being
consumed in dependency order; they do not own an approximation-number definition.

## Provenance

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

noncomputable section

universe u v w x y

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} {F : Type w}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

private instance approximationNumberIndexNonempty (n : ℕ) :
    Nonempty {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)} :=
  ⟨⟨0, by simp [LinearMap.rank_zero]⟩⟩

/-- The defining infimum.  Stated for proofs that genuinely need the
construction; it is deliberately not a `simp` lemma, since a `ciInf` over a
subtype is not a useful normal form for a norm-like quantity.  Prefer
`ContinuousLinearMap.approximationNumber_le_norm_sub` and
`ContinuousLinearMap.le_approximationNumber_iff`. -/
theorem approximationNumber_eq_iInf (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) =
      ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖ := by
  rw [T.singularValue_def, NNReal.coe_iInf]
  simp only [coe_nnnorm]
/-- Every admissible approximation of rank at most `n` bounds `aₙ(T)` above. -/
theorem approximationNumber_le_norm_sub (T : E →L[𝕜] F) {n : ℕ}
    {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal)) :
    (T.singularValue n : ℝ) ≤ ‖T - R‖ := by
  exact_mod_cast T.singularValue_le_nnnorm_sub (by exact_mod_cast hR)

/-- Characteristic lower-bound property: `x` bounds `aₙ(T)` from below exactly
when it bounds every admissible approximation error. -/
theorem le_approximationNumber_iff (T : E →L[𝕜] F) {n : ℕ} {x : ℝ} :
    x ≤ (T.singularValue n : ℝ) ↔
      ∀ R : E →L[𝕜] F, R.rank ≤ (n : Cardinal) → x ≤ ‖T - R‖ := by
  constructor
  · intro hx R hR
    exact hx.trans (T.approximationNumber_le_norm_sub hR)
  · intro h
    rw [T.approximationNumber_eq_iInf]
    apply le_ciInf
    rintro ⟨R, hR⟩
    exact h R hR

/-- A best approximation of rank at most `n` computes `aₙ(T)`: if no admissible
`S` does better than `R`, then the infimum is attained at `R`.

Existence of such an `R` is not automatic — the defining infimum need not be
attained — which is why this is stated with the minimality hypothesis rather
than as an unconditional `∃`. -/
theorem approximationNumber_eq_norm_sub_of_forall_le (T : E →L[𝕜] F) {n : ℕ}
    {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal))
    (hbest : ∀ S : E →L[𝕜] F, S.rank ≤ (n : Cardinal) →
      ‖T - R‖ ≤ ‖T - S‖) :
    (T.singularValue n : ℝ) = ‖T - R‖ := by
  have hbest' : ∀ S : E →L[𝕜] F, S.rank ≤ n →
      ‖T - R‖₊ ≤ ‖T - S‖₊ := by
    intro S hS
    exact_mod_cast hbest S (by exact_mod_cast hS)
  have h := T.singularValue_eq_nnnorm_sub (by exact_mod_cast hR) hbest'
  simpa using congrArg NNReal.toReal h

/-- The **zeroth** approximation number is the operator norm: allowing rank-`0`
approximants allows only `0`.  This is the statement that fixes the zero-based
convention; see the module docstring.  Not to be confused with
`ContinuousLinearMap.approximationNumber_zero`, which is about the zero
*operator*. -/
@[simp]
theorem approximationNumber_index_zero (T : E →L[𝕜] F) :
    (T.singularValue 0 : ℝ) = ‖T‖ := by
  simp [singularValue_zero]

/-- Approximation numbers decrease with the allowed rank. -/
theorem approximationNumber_antitone (T : E →L[𝕜] F) :
    Antitone (fun approximationIndex : ℕ => (T.singularValue approximationIndex : ℝ)) := by
  intro n m hnm
  exact_mod_cast (T.antitone_singularValue hnm)

/-- Every approximation number is bounded by the operator norm. -/
theorem approximationNumber_le_norm (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤ ‖T‖ := by
  exact_mod_cast T.singularValue_le_nnnorm n

/-- The zero operator has every approximation number equal to zero.  Named for
the operator, as in Mathlib's `LinearMap.singularValues_zero`; the companion
`ContinuousLinearMap.approximationNumber_index_zero` is the one about index
`0`. -/
@[simp]
theorem approximationNumber_zero (n : ℕ) :
    ((0 : E →L[𝕜] F).singularValue n : ℝ) = 0 := by
  simp [zero_singularValue]

/-- **The rank cutoff.**  An operator of rank at most `n` is its own best
approximation of rank at most `n`, so `aₙ(T) = 0`.

This is the first of the four statements roadmap topic T09 §A4 asks for.  It holds
over any normed pair — no inner product, no completeness, no finite dimension —
because `R := T` is admissible in the defining infimum. The converse over a complete
field is accepted as
`ContinuousLinearMap.singularValue_eq_zero_iff_rank_le` in Tau Ceti
`ApproximationNumber.Compact`; it needs neither an inner product nor finite dimension. -/
theorem approximationNumber_eq_zero_of_rank_le (T : E →L[𝕜] F) {n : ℕ}
    (hT : T.rank ≤ (n : Cardinal)) :
    (T.singularValue n : ℝ) = 0 := by
  rw [singularValue_eq_zero_of_rank_le (by exact_mod_cast hT)]
  rfl

/-- Every approximation number at or past the rank vanishes: the cutoff
`ContinuousLinearMap.approximationNumber_eq_zero_of_rank_le` in the form a
consumer with a *finite* rank bound uses. -/
theorem approximationNumber_eq_zero_of_rank_le_of_le (T : E →L[𝕜] F) {r n : ℕ}
    (hT : T.rank ≤ (r : Cardinal)) (hrn : r ≤ n) :
    (T.singularValue n : ℝ) = 0 :=
  T.approximationNumber_eq_zero_of_rank_le
    (hT.trans (Nat.cast_le.mpr hrn))

/-- Near-minimizers exist: the defining infimum is approached to within any
`ε > 0` by an admissible approximant.  This is the workhorse behind every
inequality below, each of which builds an approximant for the left-hand side out
of near-minimizers for the right. -/
theorem exists_rank_le_norm_sub_lt_approximationNumber_add (T : E →L[𝕜] F)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F,
      R.rank ≤ (n : Cardinal) ∧
        ‖T - R‖ < (T.singularValue n : ℝ) + ε := by
  have hlt : (T.singularValue n : ℝ) < (T.singularValue n : ℝ) + ε := by
    exact lt_add_of_pos_right _ hε
  rw [T.approximationNumber_eq_iInf] at hlt
  obtain ⟨⟨R, hR⟩, hdist⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨R, hR, by simpa only [← T.approximationNumber_eq_iInf] using hdist⟩

/-- Approximation numbers are `1`-Lipschitz in the ambient operator norm.  The
index-shifted `ContinuousLinearMap.approximationNumber_add_le` is the sharper
statement; this is its `n = 0` specialization in the second summand, kept
separate because perturbation arguments want the norm on the right. -/
theorem approximationNumber_add_le_add_norm (T S : E →L[𝕜] F) (n : ℕ) :
    ((T + S).singularValue n : ℝ) ≤ (T.singularValue n : ℝ) + ‖S‖ := by
  exact_mod_cast T.singularValue_add_le S n

/-- **Each approximation number is `1`-Lipschitz in the operator norm:**
`|aₙ(T) − aₙ(S)| ≤ ‖T − S‖`.

This is the reverse-triangle form of `approximationNumber_add_le_add_norm`, and
it is the perturbation statement downstream arguments actually want: it says the
whole `s`-sequence moves no faster than the operator does.  In finite dimensions
it specializes to Weyl's inequality for singular values, via
`singularValue_eq_linearMap_singularValues`. -/
theorem abs_approximationNumber_sub_approximationNumber_le (T S : E →L[𝕜] F) (n : ℕ) :
    |(T.singularValue n : ℝ) - (S.singularValue n : ℝ)| ≤ ‖T - S‖ := by
  exact_mod_cast T.abs_singularValue_sub_singularValue_le S n

/-- The additive ideal inequality: `a_{m+n}(T + S) ≤ aₘ(T) + aₙ(S)`, because two
approximants of ranks at most `m` and `n` add to one of rank at most `m + n`.
The index shift is exact in the zero-based convention — one-based `s`-numbers
would carry an `m + n - 1` here. -/
theorem approximationNumber_add_le
    (T S : E →L[𝕜] F) (m n : ℕ) :
    ((T + S).singularValue (m + n) : ℝ) ≤
      (T.singularValue m : ℝ) + (S.singularValue n : ℝ) := by
  exact_mod_cast T.singularValue_add_index_le S m n

/-- **Composition multiplicativity across indices**: `a_{m+n}(S ∘ T) ≤ aₘ(S) · aₙ(T)`.

The name carries `add` deliberately.  `approximationNumber_comp_comp_le` is the *two-sided ideal*
bound `aₙ(L ∘ T ∘ R) ≤ ‖L‖ · aₙ(T) · ‖R‖`, a different theorem at a fixed index; this one splits
the index, which is what makes the approximation numbers behave like a multiplicative scale and is
the input to the Schatten Hölder inequalities.

The approximant is `R₁ ∘ T + (S - R₁) ∘ R₂`, whose rank is at most `m + n` because each summand is
bounded by the rank of *its own* finite-rank factor — the left one by `R₁`, the right one by `R₂`.
The residual then factors as `(S - R₁) ∘ (T - R₂)`, so the two approximation errors multiply. -/
theorem approximationNumber_comp_add_le_mul
    {G : Type x} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    ((S ∘L T).singularValue (m + n) : ℝ) ≤
      (S.singularValue m : ℝ) * (T.singularValue n : ℝ) := by
  exact_mod_cast S.singularValue_comp_add_le_mul T m n

/-- Right ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_le_mul_norm
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] F) (A : G →L[𝕜] E) (n : ℕ) :
    ((T ∘L A).singularValue n : ℝ) ≤
      (T.singularValue n : ℝ) * ‖A‖ := by
  exact_mod_cast T.singularValue_comp_le_right A n

/-- Left ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_le_norm_mul
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    ((B ∘L T).singularValue n : ℝ) ≤
      ‖B‖ * (T.singularValue n : ℝ) := by
  exact_mod_cast B.singularValue_comp_le_left T n

/-- Two-sided ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_comp_le
    {G : Type x} {H : Type y}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E)
    (n : ℕ) :
    ((L ∘L T ∘L R).singularValue n : ℝ) ≤
      ‖L‖ * (T.singularValue n : ℝ) * ‖R‖ := by
  exact_mod_cast L.singularValue_comp_comp_le T R n

/-- **Approximation numbers do not see an enlargement of the codomain.**

`ι` embeds `F` into `G` with `‖ι‖ ≤ 1`, and `π` is a left inverse with `‖π‖ ≤ 1`; the
model is the inclusion of `F` as one summand of an `ℓ²` direct sum together with the
projection back onto it.  Postcomposing with `ι` then leaves every approximation number
where it was, because both ideal inequalities apply and `π ∘ ι = id` closes the loop.
(The two hypotheses force `ι` to be isometric: `‖y‖ = ‖π (ι y)‖ ≤ ‖ι y‖ ≤ ‖y‖`.)

Nothing here needs an inner product, completeness, or a bound on any dimension.  Its use
is to move an operator into a codomain with room for as many orthonormal vectors as an
argument needs, without changing the quantity being computed. -/
theorem approximationNumber_comp_eq_of_leftInverse
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι : Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (T : E →L[𝕜] F) (n : ℕ) :
    ((ι ∘L T).singularValue n : ℝ) = (T.singularValue n : ℝ) := by
  have hcomp : π ∘L (ι ∘L T) = T := by
    ext x
    exact hπι (T x)
  refine le_antisymm ?_ ?_
  · calc ((ι ∘L T).singularValue n : ℝ)
        ≤ ‖ι‖ * (T.singularValue n : ℝ) := approximationNumber_comp_le_norm_mul ι T n
      _ ≤ 1 * (T.singularValue n : ℝ) :=
        mul_le_mul_of_nonneg_right hι ((T.singularValue n).coe_nonneg)
      _ = (T.singularValue n : ℝ) := one_mul _
  · calc (T.singularValue n : ℝ)
        = ((π ∘L (ι ∘L T)).singularValue n : ℝ) := by rw [hcomp]
      _ ≤ ‖π‖ * ((ι ∘L T).singularValue n : ℝ) :=
        approximationNumber_comp_le_norm_mul π (ι ∘L T) n
      _ ≤ 1 * ((ι ∘L T).singularValue n : ℝ) :=
        mul_le_mul_of_nonneg_right hπ (((ι ∘L T).singularValue n).coe_nonneg)
      _ = ((ι ∘L T).singularValue n : ℝ) := one_mul _

/-- Approximation numbers are absolutely homogeneous. -/
@[simp]
theorem approximationNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    ((c • T).singularValue n : ℝ) = ‖c‖ * (T.singularValue n : ℝ) := by
  rw [T.singularValue_smul]
  simp

end ContinuousLinearMap

end

end
