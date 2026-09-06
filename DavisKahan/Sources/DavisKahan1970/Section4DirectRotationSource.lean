/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance
import DavisKahan.Sources.DavisKahan1970.Section4Real

/-!
# Section 4 on the source's own object: the direct rotation

Davis and Kahan enter Section 4 with **the direct rotation** already
established by Section 3, and compare it against an arbitrary unitary carrying
`U` onto `V`.  Their object is that rotation.  It is not a chosen isometry
between the two crossed defect spaces.

The declarations underneath these façades take such an isometry `J` and speak of
`nonacuteDirectRotation U V J`.  That is the right shape for the mathematics --
Proposition 3.2 shows the direct rotation is *not* unique, so a construction has
to choose -- and the wrong shape for a source boundary, where the chosen
identification is an implementation detail that the paper never mentions.

Each façade below takes the source's own hypothesis, the standing convention
(3.5) `CrossedDefectsEquivalent`, and produces a `D` satisfying the paper's
direct-rotation predicate `IsDirectRotation` together with the printed
extremality.  `nonacuteDirectRotation_isDirectRotation` is the bridge; nothing
else happens here.

Proposition 4.2 needs no façade: its canonical statement already takes
`CrossedDefectsEquivalent` and never names a rotation, because its conclusion is
about the principal angles and an arbitrary competitor.
-/

open TauCeti.DavisKahan.Angle

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta

noncomputable section

universe v

/-! ### Over `ℂ` -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 4.1, on the source's own direct rotation.**

Under the standing convention (3.5) a direct rotation exists, and for it both
printed formulations hold: the pointwise angle bound against an arbitrary
competitor `W`, and the singular-value identity and domination. -/
theorem proposition4_1_directRotation_sourceExact_complex
    [TopologicalSpace.SeparableSpace H]
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) :
    ∃ D : H →L[ℂ] H, DavisKahan.IsDirectRotation U V D ∧
      ((∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
        Orthonormal ℂ v ∧
          ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
            TauCeti.principalAngleSequence U V (n : ℕ) ≤
              TauCeti.vectorAngle ℂ (v n : H) (W (v n : H))) ∧
        (∀ n : ℕ,
          (ContinuousLinearMap.approximationNumber
              ((1 - D) ∘L DavisKahan.projection U) n : Real) =
            2 * Real.sin (TauCeti.principalAngleSequence U V n / 2)) ∧
        ∀ n : ℕ,
          ContinuousLinearMap.approximationNumber
              ((1 - D) ∘L DavisKahan.projection U) n ≤
            ContinuousLinearMap.approximationNumber
              ((1 - W) ∘L DavisKahan.projection U) n) := by
  obtain ⟨J⟩ := hcrossed
  exact ⟨DavisKahan.nonacuteDirectRotation U V J,
    DavisKahan.nonacuteDirectRotation_isDirectRotation U V J,
    proposition4_1_compact_nonacute_complex U V hcompact J W hWunitary hWmap⟩

/-- **Davis--Kahan 1970, Corollary 4.1, on the source's own direct rotation.**

The displacement of the direct rotation is minimal in every normalized unitarily
invariant norm. -/
theorem corollary4_1_directRotation_sourceExact_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    ∃ D : H →L[ℂ] H, DavisKahan.IsDirectRotation U V D ∧
      N.Mem ((1 - D) ∘L DavisKahan.projection U) ∧
        N.gauge ((1 - D) ∘L DavisKahan.projection U) ≤
          N.gauge ((1 - W) ∘L DavisKahan.projection U) := by
  obtain ⟨J⟩ := hcrossed
  exact ⟨DavisKahan.nonacuteDirectRotation U V J,
    DavisKahan.nonacuteDirectRotation_isDirectRotation U V J,
    corollary4_1_compact_nonacute_sourceExact_complex N U V hcompact J W
      hWunitary hWmap hWmem⟩

/-- **Davis--Kahan 1970, Proposition 4.3, on the source's own direct rotation.** -/
theorem proposition4_3_directRotation_sourceExact_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    ∃ D : H →L[ℂ] H, DavisKahan.IsDirectRotation U V D ∧
      N.Mem ((1 - star D) * (1 - D)) ∧
        N.gauge ((1 - star D) * (1 - D)) ≤ N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨J⟩ := hcrossed
  exact ⟨DavisKahan.nonacuteDirectRotation U V J,
    DavisKahan.nonacuteDirectRotation_isDirectRotation U V J,
    proposition4_3_compact_nonacute_sourceExact_complex N U V hcompact J W
      hWunitary hWmap hWmem⟩

end Complex

/-! ### Over `ℝ` -/

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 4.1 over `ℝ`, on the source's own direct
rotation.** -/
theorem proposition4_1_directRotation_sourceExact_real
    [TopologicalSpace.SeparableSpace E]
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) :
    ∃ D : E →L[ℝ] E, DavisKahan.IsDirectRotation U V D ∧
      ((∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
        Orthonormal ℝ v ∧
          ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
            TauCeti.principalAngleSequence U V (n : ℕ) ≤
              TauCeti.vectorAngle ℝ (v n : E) (W (v n : E))) ∧
        (∀ n : ℕ,
          (ContinuousLinearMap.approximationNumber
              ((1 - D) ∘L DavisKahan.projection U) n : Real) =
            2 * Real.sin (TauCeti.principalAngleSequence U V n / 2)) ∧
        ∀ n : ℕ,
          ContinuousLinearMap.approximationNumber
              ((1 - D) ∘L DavisKahan.projection U) n ≤
            ContinuousLinearMap.approximationNumber
              ((1 - W) ∘L DavisKahan.projection U) n) := by
  obtain ⟨J⟩ := hcrossed
  exact ⟨DavisKahan.nonacuteDirectRotation U V J,
    DavisKahan.nonacuteDirectRotation_isDirectRotation U V J,
    proposition4_1_compact_nonacute_real U V hcompact J W hWunitary hWmap⟩

/-- **Davis--Kahan 1970, Corollary 4.1 over `ℝ`, on the source's own direct
rotation.** -/
theorem corollary4_1_directRotation_sourceExact_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    ∃ D : E →L[ℝ] E, DavisKahan.IsDirectRotation U V D ∧
      N.Mem ((1 - D) ∘L DavisKahan.projection U) ∧
        N.gauge ((1 - D) ∘L DavisKahan.projection U) ≤
          N.gauge ((1 - W) ∘L DavisKahan.projection U) := by
  obtain ⟨J⟩ := hcrossed
  exact ⟨DavisKahan.nonacuteDirectRotation U V J,
    DavisKahan.nonacuteDirectRotation_isDirectRotation U V J,
    corollary4_1_compact_nonacute_sourceExact_real N U V hcompact J W
      hWunitary hWmap hWmem⟩

/-- **Davis--Kahan 1970, Proposition 4.3 over `ℝ`, on the source's own direct
rotation.** -/
theorem proposition4_3_directRotation_sourceExact_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    ∃ D : E →L[ℝ] E, DavisKahan.IsDirectRotation U V D ∧
      N.Mem ((1 - star D) * (1 - D)) ∧
        N.gauge ((1 - star D) * (1 - D)) ≤ N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨J⟩ := hcrossed
  exact ⟨DavisKahan.nonacuteDirectRotation U V J,
    DavisKahan.nonacuteDirectRotation_isDirectRotation U V J,
    proposition4_3_compact_nonacute_sourceExact_real N U V hcompact J W
      hWunitary hWmem hWmap⟩

end Real

end

end DavisKahan1970
end TauCeti
