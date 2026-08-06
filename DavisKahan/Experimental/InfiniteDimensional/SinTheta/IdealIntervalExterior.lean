/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle

/-!
# The open ideal-valued projector-difference estimate

`projectionDifference_ideal_intervalExterior` is the one remaining tactic `sorry` on the
`SinTheta` side, and `ideal_sinTheta` is its only consumer.  Both live here rather than in
`SinTheta/General.lean` so that the sorry-free part of that development can be imported by
continuation and Section 8 modules without dragging an admission into their closures.

**What is missing, precisely.**  `projectionDifference_sylvester` and
`SymmetricNormIdeal.gauge_projectionCross_le` (both in `SinTheta/General.lean`, both
proved) supply the Sylvester equation and the constant-one contraction of the cross term.
What does not exist is the constant-one Sylvester estimate on a *union of two*
interval/exterior rectangles: every constant-one estimate in the tree
(`Sylvester/ShiftedInverseGauge.lean`, `Sylvester/Unbounded/IntervalExterior.lean`) is
single-rectangle, and shifting cannot separate all four corner pairs at once.

**Do not reach for the triangle inequality on the two corners.**  That gives constant two
and is already proved, as `sinTheta_spectrum_gauge_symmetric` in
`DavisKahan/Sylvester/Spectrum.lean`.  The constant-one claim is sharp — equality holds at
`B - A = d (P_U - P_V)` — so there is no cheap route.

A second obstruction, not visible from the statement: the constant-one machinery is stated
for `TauCeti.SymmetricOperatorIdealFamily`, while this theorem quantifies over the bespoke
`SymmetricNormIdeal`.  The only bridge, `SymmetricNormIdeal.ofRectangular`, runs the wrong
way, so discharging this also needs a reverse bridge or a native re-proof.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Experimental.Foundation

open DavisKahan

open DavisKahan.Experimental

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

-- The three functional-calculus hypotheses `SinTheta/General.lean` carries in the same
-- section: two structural, and one (`ContinuousFunctionalCalculus`) that Mathlib currently
-- supplies only at `𝕜 = ℂ`.  Carrying them keeps the development scalar-general without
-- pretending the general case exists.
variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

section OperatorAbsoluteValue

/-- **Leaf obligation.** The ideal-valued symmetric projector-difference
estimate: both mixed interval/exterior gaps bound the ideal gauge of the
projector difference by the gauge of the perturbation, with the sharp
constant-one dependence on the gap.

**Reduced 2026-08-04** — see the section above.  `projectionDifference_sylvester`
and `SymmetricNormIdeal.gauge_projectionCross_le` supply the equation and the
contraction; what is missing is the constant-one Sylvester estimate on a *union
of two* interval/exterior rectangles.  Do **not** reach for the triangle
inequality on the two corners: that gives constant two, and it is already proved
elsewhere. -/
theorem projectionDifference_ideal_intervalExterior
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ}
    (hlr : left ≤ right) (hlr' : left' ≤ right') (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : I.mem (B - A)) :
    I.mem (projection U - projection V) ∧
      d * I.gauge (projection U - projection V) ≤ I.gauge (B - A) :=
  sorry

/-- Symmetric-ideal form.

Lean proof route for a weaker agent:

1. Decompose the full sine operator into the two directed off-diagonal blocks.
2. Apply the interval/exterior ideal-valued Sylvester estimate to each block, using `hmem` for the perturbation.
3. Recombine the blocks through the two-projection decomposition or the symmetric-angle identity.
4. Return both ideal membership and the gauge inequality.


Ext-agent signature audit (GPT 5.6 High): Plausible with the full ambient sine
convention because the self-adjoint off-diagonal blocks occur as adjoint pairs. The
proof must establish the corresponding ideal block identity; do not combine two directed
estimates by a triangle inequality, which would lose the sharp constant.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem ideal_sinTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ}
    (hlr : left ≤ right) (hlr' : left' ≤ right') (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : I.mem (B - A)) :
    I.mem (sinAngleOperator U V) ∧
      d * I.gauge (sinAngleOperator U V) ≤ I.gauge (B - A) := by
  have hdiff := projectionDifference_ideal_intervalExterior
    I hA hB hU hV hlr hlr' hd hUV hVU hmem
  have habs := I.operatorAbsoluteValue_mem_and_gauge_eq hdiff.1
  simpa [sinAngleOperator, habs.2] using
    And.intro habs.1 hdiff.2

/-- Ideal-norm `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. Use the reflection-defect form of `sinTwoTheta_reflectionDefect` in the ideal gauge.
2. Show the reflection defect equals the off-diagonal extraction of `B-A` up to the factor two because `V` reduces `B`.
3. Apply `gauge_offDiagonalPart_le` and `hmem`.
4. Package ideal membership before the numerical inequality.


Ext-agent signature audit (GPT 5.6 High): Correct roadmap target under finite-gap
geometry and ideal membership of the perturbation. The proof must work with ambient
reflection blocks so multiplicities match.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem ideal_sinTwoTheta
    [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hmem : I.mem (B - A)) :
    I.mem (sinTwoAngleOperator U V) ∧
      d * I.gauge (sinTwoAngleOperator U V) ≤ 2 * I.gauge (B - A) := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' := hA.reflection_conjugate V
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  obtain ⟨l, r, l', r', hlr, hlr', hUU', hU'U⟩ :=
    finiteGap_mixedIntervalExterior V hfinite
  have hAB : I.mem (A - B) := by
    simpa [neg_sub] using I.smul_mem (-1 : 𝕜) hmem
  have hnegAB : I.mem (-(A - B)) := by
    simpa using I.smul_mem (-1 : 𝕜) hAB
  have hdefMem : I.mem (A'-A) := by
    rw [show A'-A = reflectionDefect V A by rfl,
      reflectionDefect_eq_perturbationDefect A B V hV]
    have h := I.add_mem
      (I.ideal_mem (reflectionOperator V) (reflectionOperator V) hAB) hnegAB
    simpa [sub_eq_add_neg] using h
  have hsin := projectionDifference_ideal_intervalExterior
    I hA hA' hU hU' hlr hlr' hd hUU' hU'U hdefMem
  have hdefGauge : I.gauge (A'-A) ≤ 2 * I.gauge (B-A) := by
    rw [show A'-A = reflectionDefect V A by rfl,
      reflectionDefect_eq_perturbationDefect A B V hV]
    have hconj : I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V) =
        I.gauge (A-B) :=
      I.unitary_invariant
        (reflectionOperator V) (reflectionOperator V) (A-B)
        (reflectionOperator_isUnitary V) (reflectionOperator_isUnitary V)
        (reflectionOperator_involutive V) (reflectionOperator_involutive V) hAB
    have htri := I.triangle
      (I.ideal_mem (reflectionOperator V) (reflectionOperator V) hAB) hnegAB
    have hgneg : I.gauge (-(A - B)) = I.gauge (A - B) := by
      simpa using I.gauge_smul (-1 : 𝕜) hAB
    have hgBA : I.gauge (A - B) = I.gauge (B - A) := by
      simpa [neg_sub] using I.gauge_smul (-1 : 𝕜) hmem
    calc I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V - (A-B))
        = I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V +
            -(A-B)) := by rw [sub_eq_add_neg]
      _ ≤ I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V) +
            I.gauge (-(A-B)) := htri
      _ = I.gauge (A-B) + I.gauge (A-B) := by rw [hconj, hgneg]
      _ = 2 * I.gauge (B-A) := by rw [hgBA]; ring
  obtain ⟨hmemS, hgaugeS⟩ := I.sinTwoAngle_mem_and_gauge_le U V hsin.1
  refine ⟨hmemS, ?_⟩
  -- the gauge only goes one way, and this is the way it goes: passing from the
  -- projector difference to the one-sided operator can only decrease it.
  calc d * I.gauge (sinTwoAngleOperator U V)
      ≤ d * I.gauge
          (U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) := by
        gcongr
    _ ≤ I.gauge (A' - A) := hsin.2
    _ ≤ 2 * I.gauge (B - A) := hdefGauge
end OperatorAbsoluteValue

end DavisKahanExt
end TauCeti
