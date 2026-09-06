/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAngleUnbounded
import DavisKahan.Sources.DavisKahan1970.Ideals.NormalizedUnitaryInvariantNormExamples
import DavisKahan.DoubleAngle.RealAngleIdentification
import DavisKahan.Geometry.Angle.DoubleAngleGapBound

/-!
# Theorem 8.2's acute branch at unbounded scope

Davis--Kahan add to the `sin 2Θ` theorem's hypotheses a smallness condition --
`‖H‖ < δ/2` or `‖R‖ < δ/2` -- and a spectral containment, and conclude both the
double-angle estimate and `Θ < π/4`.

The printed proof runs a homotopy `A(σ) = A + H − σH` with a continuously varying
spectral projector, and the old plan turned that into a required unbounded
Riesz/continuation library.  It is not needed.  The acute conclusion is Theorem
8.1's *closed* branch plus the double-angle bound:

```text
Theorem 8.1 (unbounded)   ⟹  ‖P_P − P_Q‖ ≤ √2/2
‖H‖ < δ/2 and sin 2Θ      ⟹  ‖sin 2Θ‖ ≤ 2‖H‖/δ < 1
bootstrap comparison      ⟹  √2 · directedGap ≤ ‖sin 2Θ‖
                          ⟹  ‖P_P − P_Q‖ < √2/2
```

The bootstrap's hypothesis is exactly "on the closed quarter branch", which is
what the homotopy existed to establish and what Theorem 8.1 now supplies at
unbounded scope.  Its constant depends on `‖H‖/δ` only, never on `‖A‖`, which is
why the paper writes `<` here and `≤` in Theorem 8.1, and why this bound survives
where Theorem 8.1's strict supremum bound does not.

The `sin 2Θ` estimate is read at the operator norm, which is the first Ky Fan
norm and therefore a member of the source norm class -- the inhabitation result
is what makes the instantiation possible.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester

noncomputable section

universe v

/-- **The `sin 2Θ` estimate at the operator norm, unbounded ambient scope.**

The operator norm is the first Ky Fan norm, hence a member of the source norm
class, so the printed universal-norm estimate specializes to it. -/
theorem norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
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
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    δ * ‖TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q‖ ≤ 2 * ‖Hop‖ := by
  set N : NormalizedUnitaryInvariantNorm.{0, v} ℂ :=
    kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) 1 one_pos with hN
  obtain ⟨-, hle⟩ := sinTwoTheta_ambient_unbounded_perturbedGap_sourceExact_complex
    N hA Hop hHop hPred hQred hδ hgap
    (mem_kyFanNormalizedUnitaryInvariantNorm 1 one_pos Hop)
  rw [hN] at hle
  rw [gauge_kyFanNormalizedUnitaryInvariantNorm 1 one_pos,
    gauge_kyFanNormalizedUnitaryInvariantNorm 1 one_pos,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hle
  exact hle

/-- **Davis--Kahan 1970, Theorem 8.2's acute conclusion at unbounded ambient
scope, perturbation branch.**

`Theta < pi/4` from the printed smallness hypothesis `‖H‖ < delta/2`, given the
closed branch that Theorem 8.1 supplies.

Two hypotheses are carried rather than derived, and both are named assembly steps
for this row rather than mathematics that is missing.

* The **closed branch** `‖P_P − P_Q‖ ≤ √2/2` is what Theorem 8.1 supplies at
  unbounded scope.  It is a hypothesis here because Theorem 8.1's unbounded
  statement takes ordered *form* bounds while Theorem 8.2's printed hypotheses
  are spectral containments, and translating between them at unbounded scope is
  step 1.
* The **strict contraction** is stated on the one-sided block
  `2 P_{P^perp} P_Q P_P`, which is what the bootstrap comparison consumes.
  `norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex` above supplies
  the same bound for the functional-calculus `sin 2Theta`; identifying the two
  norms -- they have the same approximation numbers -- is step 2. -/
theorem theorem8_2_branch_maximalAngle_lt_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hclosed : DavisKahan.subspaceGap P Q ≤ Real.sqrt 2 / 2)
    (hcross : DavisKahan.CrossedDefectsEquivalent Q P)
    (hblock : ‖TauCeti.DavisKahanExt.sinTwoAngleOperator P Q‖ < 1) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 :=
  DavisKahan.maximalAngle_lt_pi_div_four_of_le_of_norm_sinTwoAngle_lt_one
    P Q hcross hclosed hblock

/-- **The two spellings of `sin 2Theta` have the same norm.**

The unbounded estimate is proved for the functional-calculus `sin 2Theta`; the
bootstrap comparison that turns the closed branch into the open one consumes the
one-sided block `2 P_{U^perp} P_V P_U`.  Both have the norm of the directed
double-angle sine, which is symmetric in the pair because the *doubled* sines
have the same complete approximation-number sequence even though the undoubled
ones do not. -/
theorem norm_sinTwoAngleOperator_eq_norm_block
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (U V : Submodule ℂ Hc) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V‖ =
      ‖TauCeti.DavisKahanExt.sinTwoAngleOperator U V‖ := by
  rw [TauCeti.DavisKahan.Angle.sinTwoAngleOperator_complex,
    TauCeti.DavisKahanExt.norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC,
    TauCeti.DavisKahan.Angle.norm_sinTwoAngleOperator_eq_norm_directedSinTwoAngleOperatorC_swap]
  exact (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap
    U V).norm_eq

/-- **The acute conclusion from the printed smallness hypothesis.**

`‖H‖ < delta/2` and the closed branch give `Theta < pi/4`.  This is the
perturbation branch of Theorem 8.2 at unbounded ambient scope, with the closed
branch -- which unbounded Theorem 8.1 supplies -- still carried as a hypothesis. -/
theorem theorem8_2_branch_maximalAngle_lt_of_small_perturbation_unbounded_complex
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
    (hclosed : DavisKahan.subspaceGap P Q ≤ Real.sqrt 2 / 2)
    (hcross : DavisKahan.CrossedDefectsEquivalent Q P)
    (hsmall : ‖Hop‖ < δ / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hbound := norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
    hA Hop hHop hPred hQred hδ hgap
  rw [norm_sinTwoAngleOperator_eq_norm_block] at hbound
  have hblock : ‖TauCeti.DavisKahanExt.sinTwoAngleOperator P Q‖ < 1 := by
    nlinarith [hbound, hsmall, hδ,
      norm_nonneg (TauCeti.DavisKahanExt.sinTwoAngleOperator P Q)]
  exact theorem8_2_branch_maximalAngle_lt_unbounded_complex hclosed hcross hblock

end

end Section8
end DavisKahan1970
end TauCeti
