/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section8.Theorem82Unbounded
import DavisKahan.SinTheta.Natural.Reducing
import ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-!
# The static branch bound for Theorem 8.2 at unbounded scope

Theorem 8.2's closed quarter branch is the paper's connectedness step, and
`Theorem82Unbounded.lean` carries it as a hypothesis.  This module discharges it
on the part of the printed range where a *static* argument reaches.

The `sin Θ` theorem at unbounded scope, read at the operator norm, gives

```text
(δ/2) · directedGap P Q ≤ ‖H‖
```

from Theorem 8.2's own printed hypotheses -- the separation between the
unperturbed block on `P`, whose spectrum the theorem places in
`[β − δ/2, α + δ/2]`, and the perturbed block on `Qᗮ`, whose spectrum it places
off `(β − δ, α + δ)`.  So `directedGap P Q ≤ 2‖H‖/δ`, and the closed branch is
free whenever `2‖H‖/δ ≤ √2/2`, that is `‖H‖ ≤ (√2/4) δ`.

The printed hypothesis is `‖H‖ < δ/2`, so this covers a strict sub-interval.
The module docstring of `Theorem82Unbounded.lean` records what the rest costs.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester

noncomputable section

universe v

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete.  `local instance` does not propagate through imports, so it is
reinstalled here. -/
local instance instCompleteSpaceCoeBranchBound
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- **The `sin Θ` estimate at the operator norm, unbounded ambient scope,
directed form.**

`δ · directedGap P Q ≤ ‖H‖` from the separation between the unperturbed block on
`P` and the perturbed block on `Qᗮ`.

The trial datum is the inclusion of `P`; the residual it produces is `H`
restricted to `P`, whose norm is at most `‖H‖`, and that is where the printed
perturbation norm enters. -/
theorem directedGap_le_of_reducingGap_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : DavisKahan.IsSelfAdjointOperator Hop)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    δ * DavisKahan.directedGap P Q ≤ ‖Hop‖ := by
  classical
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hA0 : IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A P hPred) :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A P hPred hA.dense_domain hA
  have hX : DavisKahan.IsometricEmbedding (P.subtypeL : P →L[ℂ] Hc) := fun _ => rfl
  have hXdom : ∀ x : (TauCeti.LinearPMap.reducingRestriction A P hPred).domain,
      (P.subtypeL (x : P) : Hc) ∈ (TauCeti.LinearPMap.addBounded A Hop).domain := by
    intro x
    exact x.2
  have hReq : ∀ x : (TauCeti.LinearPMap.reducingRestriction A P hPred).domain,
      (TauCeti.LinearPMap.addBounded A Hop) ⟨P.subtypeL (x : P), hXdom x⟩ -
          P.subtypeL ((TauCeti.LinearPMap.reducingRestriction A P hPred) x) =
        (Hop ∘L (P.subtypeL : P →L[ℂ] Hc)) (x : P) := by
    intro x
    have hxA : ((x : P) : Hc) ∈ A.domain := x.2
    show (A (⟨((x : P) : Hc), hxA⟩ : A.domain) : Hc) + Hop ((x : P) : Hc)
        - (A (⟨((x : P) : Hc), hxA⟩ : A.domain) : Hc) = Hop ((x : P) : Hc)
    abel
  have key := DavisKahan.ExactSinTheta.sinTheta_unbounded_complex_reducingSubspace
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 1 one_pos)
    (TauCeti.LinearPMap.addBounded A Hop) hB.dense_domain hB.isClosed hB Q hQred
    (TauCeti.LinearPMap.reducingRestriction A P hPred)
    hA0.dense_domain hA0.isClosed hA0
    (P.subtypeL : P →L[ℂ] Hc) (Hop ∘L (P.subtypeL : P →L[ℂ] Hc)) hX hXdom hReq hδ hgap
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) 1 one_pos _)
  obtain ⟨-, hle⟩ := key
  rw [KyFanDominantIdealFamily.kyFan_gauge, KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hle
  have hblock : (ContinuousLinearMap.id ℂ Hc -
      Q.subtypeL ∘L ContinuousLinearMap.adjoint Q.subtypeL) = Qᗮ.starProjection := by
    rw [Submodule.adjoint_subtypeL]
    exact (Submodule.starProjection_orthogonal Q).symm
  rw [hblock] at hle
  have hgapeq : ‖Qᗮ.starProjection ∘L (P.subtypeL : P →L[ℂ] Hc)‖ =
      DavisKahan.directedGap P Q :=
    TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection Qᗮ.starProjection P
  rw [hgapeq] at hle
  refine hle.trans ?_
  calc ‖Hop ∘L (P.subtypeL : P →L[ℂ] Hc)‖ ≤ ‖Hop‖ * ‖(P.subtypeL : P →L[ℂ] Hc)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Hop‖ := by
        have : ‖(P.subtypeL : P →L[ℂ] Hc)‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
          simp
        nlinarith [norm_nonneg Hop, norm_nonneg (P.subtypeL : P →L[ℂ] Hc)]

/-- **Davis--Kahan 1970, Theorem 8.2's acute conclusion at unbounded ambient
scope, with the closed branch discharged.**

`Theta < pi/4` from Theorem 8.2's printed hypotheses alone on the sub-range
`2‖H‖ ≤ (sqrt 2 / 2) delta`, that is `‖H‖ ≤ (sqrt 2 / 4) delta`.  Nothing is
carried that the paper does not print except that inequality, which is stronger
than the printed `‖H‖ < delta / 2`.

Two separations appear, and both are printed.  `hgap` is the `sin 2Theta`
theorem's own gap on the perturbed blocks at `Q`, which gives
`delta ‖sin 2Theta‖ ≤ 2 ‖H‖`.  `hgapHalf` is Theorem 8.2's extra hypothesis
`spec(A_0) ⊆ [beta - delta/2, alpha + delta/2]`, in the form the unbounded
`sin Theta` theorem consumes: it separates the unperturbed block on `P` from the
perturbed block on `Q^perp` by `delta/2`, which is exactly the distance the
printed containments leave.

`hcross` is Section 3's standing assumption (3.5), which is what turns the
directed bound into the symmetric one; the module docstring records why the rest
of the printed range needs the paper's connectedness argument. -/
theorem theorem8_2_branch_maximalAngle_lt_unbounded_smallPerturbation_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : DavisKahan.IsSelfAdjointOperator Hop)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hgapHalf : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) (δ / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : 2 * ‖Hop‖ ≤ Real.sqrt 2 / 2 * δ) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hroot : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hdir := directedGap_le_of_reducingGap_unbounded_complex hA Hop hHop hPred hQred
    (by positivity) hgapHalf
  have hsym : DavisKahan.subspaceGap P Q = DavisKahan.directedGap P Q :=
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q hcross
  have hclosed : DavisKahan.subspaceGap P Q ≤ Real.sqrt 2 / 2 := by
    rw [hsym]
    nlinarith [hdir, hsmall, hδ]
  have hbound := norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
    hA Hop hHop hPred hQred hδ hgap
  rw [norm_sinTwoAngleOperator_eq_norm_block] at hbound
  have hblock : ‖TauCeti.DavisKahanExt.sinTwoAngleOperator P Q‖ < 1 := by
    nlinarith [hbound, hsmall, hδ, hroot,
      norm_nonneg (TauCeti.DavisKahanExt.sinTwoAngleOperator P Q)]
  exact theorem8_2_branch_maximalAngle_lt_unbounded_complex hclosed hcross.symm hblock

end

end Section8
end DavisKahan1970
end TauCeti
