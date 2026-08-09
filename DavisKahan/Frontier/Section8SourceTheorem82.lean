/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8Residual
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry

/-!
# Davis--Kahan 1970, Theorem 8.2, under the paper's standing convention

`Section8Perturbation.lean` and `Section8Residual.lean` prove the branch
selection from the printed hypotheses alone, and they conclude with the
*directed* quarter-angle bound `directedGap P Q < √2/2`.  That was deliberate:
with only the printed hypotheses of Theorem 8.2 in scope, the symmetric
projector gap can be `1`, so the conclusion read symmetrically is false.  The
counterexample is recorded in `Section8Perturbation.lean` and is a dimension
mismatch -- `P = ⊥`, `Q = ⊤` on a one-dimensional space.

This module supplies the missing standing convention and derives the printed
conclusion exactly.

## What the paper's `Θ` presupposes

`Θ` is not defined for an arbitrary pair of subspaces.  Section 1 builds it from
the entries `C_j` of a unitary `V` satisfying equation (1.4),

```
V P = Q V,      V Pᗮ = Qᗮ V,
```

and immediately notes that (1.4) forces equation (1.5),

```
dim P H = dim Q H,      dim Pᗮ H = dim Qᗮ H
```

("the second equality is a consequence of the first if `dim P H` is finite").
`Θ_j := arccos (C_j C_j⋆)^{1/2}` and `Θ ≃ diag (Θ_0, Θ_1)` are then defined from
those entries, and the paper's own dictionary (Section 1, after (1.17)) reads

```
‖P - Q‖ = ‖sin Θ‖    (all norms),
```

which is `maximalAngle P Q = arcsin (subspaceGap P Q)` here.  So (1.5) is
exactly the standing hypothesis that makes `Θ < π/4` a meaningful assertion, and
it is the minimal one: it is what the paper states, not something stronger
reverse-engineered from the conclusion.

`IsQuarterAcute P Q` is **not** assumed anywhere below.  It is the conclusion.

## Why the finite form of (1.5), and not the cardinal form

In finite dimensions (1.5) is `finrank ℂ P = finrank ℂ Q`; its second half is
automatic.  Under it, `opNorm_projection_sub_eq_opNorm_sinThetaMap` identifies
the symmetric and directed gaps, and the printed conclusion follows from the
directed theorem with nothing else added.

The *cardinal* reading of (1.5) does not suffice, and this is worth recording so
that a later agent does not "generalize" the hypothesis away.  Under the
cardinal reading the printed conclusion is **false**, and the counterexample
satisfies every printed hypothesis of Theorem 8.2:

> Let `E` be a separable infinite-dimensional Hilbert space with orthonormal
> basis `e₀, e₁, …`, put `H := E × E`, and let `A` be `0` on the first summand
> and `10` on the second.  Take `K = 0`, `β = α = 0`, `δ = 1`.
>
> * `Q := E × 0` reduces `A + K = A`, with `spectrum(Λ₀) = {0} ⊆ [β, α]` and
>   `spectrum(Λ₁) = {10}` outside `(β - δ, α + δ)` -- the `sin 2Θ` hypotheses.
> * `P := span{e₁, e₂, …} × 0` reduces `A`, with
>   `spectrum(A₀) = {0} ⊆ [β - δ/2, α + δ/2]` -- Theorem 8.2's extra placement.
> * `‖K‖ = 0 < δ/2` -- the printed perturbation alternative.
> * Both halves of (1.5) hold as cardinals: `dim P = dim Q = ℵ₀` and
>   `dim Pᗮ = dim Qᗮ = ℵ₀`, so a unitary satisfying (1.4) exists and `Θ` is
>   defined.
>
> Yet `e₀ ∈ Q` is orthogonal to `P`, so `‖P_P - P_Q‖ = 1` and the symmetric `Θ`
> is `π/2`.  The directed conclusion `directedGap P Q = 0 < √2/2` is of course
> true, which is exactly the point.

Equal (infinite) dimension does not make the two directed gaps agree.  In finite
dimensions the same configuration is impossible: `P ≤ Q` with equal rank forces
`P = Q`.  So the finite form of (1.5) is not a lazy restriction but the correct
reading; the dimension-free statement stays directed, and the exact printed
statement carries the finite rank convention.  The degenerate `P = ⊥`, `Q = ⊤`
example recorded in `Section8Perturbation.lean` is the finite instance of the
same phenomenon, there excluded by (1.5) itself.

## What is exported

* `subspaceGap_eq_directedGap_of_finrank_eq` -- the bridge, (1.5) in its finite
  form;
* `theorem8_2_sinTwoTheta_perturbation_source` and
  `theorem8_2_sinTwoTheta_residual_source` -- the `sin 2Θ` conclusions Theorem
  8.2 inherits, specialized to its configuration and stated with its
  hypotheses, so the exported Section 8.2 surface carries them rather than
  merely pointing at Section 7;
* `theorem8_2_perturbationHalfGap_source_maximalAngle_lt`,
  `theorem8_2_residualHalfGap_source_maximalAngle_lt`,
  `theorem8_2_branch_source_maximalAngle_lt` -- the printed `Θ < π/4`;
* `theorem8_2_source` -- the whole printed theorem, both alternatives and both
  conclusions, in one statement.

The directed theorems keep their names and are *not* superseded: they are the
strongest statement available from the explicit hypotheses alone, and they are
what the dimension-free consumers use.
-/

open scoped InnerProductSpace
open Module (finrank)

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section8

open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.Foundation

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### 1. Equation (1.5), and what it buys -/

omit [CompleteSpace H] in
/-- **Davis--Kahan equation (1.5), finite form.**  For subspaces of equal rank
the symmetric projector gap and the directed gap coincide, so `‖sin Θ‖` may be
computed from either.

This is `TauCeti.opNorm_projection_sub_eq_opNorm_sinThetaMap` in the Section 8
vocabulary; both sides are literally the operator norms that
`Submodule.projectionGap` and `Submodule.directedProjectionGap` unfold to. -/
theorem subspaceGap_eq_directedGap_of_finrank_eq [FiniteDimensional ℂ H]
    (P Q : Submodule ℂ H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hrank : finrank ℂ P = finrank ℂ Q) :
    subspaceGap P Q = directedGap P Q :=
  TauCeti.opNorm_projection_sub_eq_opNorm_sinThetaMap P Q hrank

/-- Under equation (1.5), a directed quarter-angle bound is the printed
`Θ < π/4`. -/
theorem maximalAngle_lt_pi_div_four_of_directedGap_lt [FiniteDimensional ℂ H]
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hdir : directedGap P Q < Real.sqrt 2 / 2) :
    maximalAngle P Q < Real.pi / 4 := by
  refine (DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  show subspaceGap P Q < Real.sqrt 2 / 2
  rw [subspaceGap_eq_directedGap_of_finrank_eq P Q hrank]
  exact hdir

/-! ### 2. The `sin 2Θ` conclusions Theorem 8.2 inherits

Theorem 8.2 says "in addition to `δ‖sin 2Θ‖ ≤ 2‖H‖` **or**
`δ‖sin 2Θ₀‖ ≤ 2‖R‖`, we have `Θ < π/4`".  The two displayed inequalities are the
`sin 2Θ` theorem's own conclusions, not new content; they are restated here at
Theorem 8.2's hypotheses so that the exported surface carries the whole printed
assertion. -/

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, perturbation form.**

`δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, inherited from the maintained `sin 2Θ` development
(`sinTwoTheta_perturbation`) with `Q` as the subspace carrying the printed gap.
Nothing here is re-proved; the printed spectral placement of `Λ₀` and `Λ₁` is
exactly a `FiniteGapConfiguration` for `A + K` at `Q`. -/
theorem theorem8_2_sinTwoTheta_perturbation_source
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ := by
  have hA0 : IsSelfAdjointOperator (A + K) := hA.add hK
  have hQred : Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hfinite : Foundation.FiniteGapConfiguration (A + K) Q delta := ⟨beta, alpha, hab, hQ, hQperp⟩
  have h := sinTwoTheta_perturbation (A := A + K) (B := A) hA0 hQred hPred hdelta hfinite
  have hdiff : ‖A - (A + K)‖ = ‖K‖ := by
    rw [show A - (A + K) = -K by abel, norm_neg]
  rwa [hdiff] at h

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, residual form.**

`δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` with `R` the printed residual (1.8),
`R = (A + H) E₀ - E₀ A₀`.  Inherited from `sinTwoTheta_residual`; the trial
embedding is the inclusion `E₀ = P.subtypeL`, whose range is `P`. -/
theorem theorem8_2_sinTwoTheta_residual_source
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
      2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ := by
  classical
  let : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hA0 : IsSelfAdjointOperator (A + K) := hA.add hK
  have hQred : Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hfinite : Foundation.FiniteGapConfiguration (A + K) Q delta := ⟨beta, alpha, hab, hQ, hQperp⟩
  have hrange : LinearMap.range (P.subtypeL : P →L[ℂ] H).toLinearMap = P := by
    ext x
    simp
  have : (LinearMap.range (P.subtypeL : P →L[ℂ] H).toLinearMap).HasOrthogonalProjection := by
    rw [hrange]; infer_instance
  have hX : IsometricEmbedding (P.subtypeL : P →L[ℂ] H) := fun x => rfl
  have hM : IsSelfAdjointOperator (compressOperator P A) := by
    intro x y
    show ⟪compressOperator P A x, y⟫_ℂ = ⟪x, compressOperator P A y⟫_ℂ
    have := hA (x : H) (y : H)
    simpa [compressOperator, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr y.2,
      Submodule.starProjection_eq_self_iff.mpr x.2] using this
  have h := sinTwoTheta_residual (A := A + K) hA0 hQred (P.subtypeL : P →L[ℂ] H) hX
    hM hdelta hfinite
  have hangle : sinTwoThetaEmbedding Q (P.subtypeL : P →L[ℂ] H) =
      DavisKahanExt.sinTwoAngleOperator Q P := by
    rw [sinTwoThetaEmbedding_eq_rangeAngle Q (P.subtypeL : P →L[ℂ] H) hX]
    congr 1
    simp only [hrange]
  rwa [hangle] at h

/-! ### 3. The printed conclusion `Θ < π/4` -/

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, printed form.**

`Θ < π/4` under the printed hypotheses together with the standing convention
(1.5).  The proof adds nothing to `theorem8_2_perturbationHalfGap_source`; (1.5)
only converts its directed conclusion into the symmetric one. -/
theorem theorem8_2_perturbationHalfGap_source_maximalAngle_lt [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_perturbationHalfGap_source hA hK hdelta hab hQ hQperp hPred hP hsmall)

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, printed form.** -/
theorem theorem8_2_residualHalfGap_source_maximalAngle_lt [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_residualHalfGap_source hA hK hdelta hab hQ hQperp hPred hP hRsmall)

/-- **Theorem 8.2's printed disjunction, printed conclusion.** -/
theorem theorem8_2_branch_source_maximalAngle_lt [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_branch_source hA hK hdelta hab hQ hQperp hPred hP hsmall)

/-! ### 4. The whole printed theorem -/

/-- **Davis--Kahan 1970, Theorem 8.2.**

> Add to the hypotheses of the `sin 2θ` theorem either `‖H‖₁ < δ/2` or
> `‖R‖₁ < δ/2`, and assume the spectrum of `A₀` lies in
> `[β - δ/2, α + δ/2]`.  Then, in addition to `δ‖sin 2Θ‖ ≤ 2‖H‖` or
> `δ‖sin 2Θ₀‖ ≤ 2‖R‖`, we have `Θ < π/4`.

Every hypothesis below is one of those, plus the Section 1 standing convention
(1.5) in its finite form.  Every conclusion below is one of those: the two
displayed `sin 2Θ` estimates, which Theorem 8.2 inherits and which hold under
either alternative, and the strict quarter angle, which is Theorem 8.2's own
content.

`‖·‖₁` is the bound norm throughout Theorem 8.2, which is what the operator
norms here are. -/
theorem theorem8_2_source [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ ∧
      delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
        2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ ∧
      maximalAngle P Q < Real.pi / 4 :=
  ⟨theorem8_2_sinTwoTheta_perturbation_source hA hK hdelta hab hQ hQperp hPred,
    theorem8_2_sinTwoTheta_residual_source hA hK hdelta hab hQ hQperp hPred,
    theorem8_2_branch_source_maximalAngle_lt hA hK hdelta hab hQ hQperp hPred hP
      hrank hsmall⟩

end Section8
end Frontier
end Experimental
end DavisKahan
end TauCeti
