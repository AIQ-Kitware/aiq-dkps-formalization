/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import DavisKahan.Interop.Spectra.DirectRotation
-- supplies `spectraReflectionProduct` and `IsAcute.symm`
import DavisKahan.Interop.Spectra.DirectRotationSquare
-- supplies the completed nonacute construction and acute characterizations used
-- to ground the Proposition 3.2 and Corollary 3.2 source statements below.  The
-- construction depends on the polar and acute machinery under `MathAhead`, which
-- itself never imports this module, so the dependency is acyclic.
import DavisKahan.Experimental.MathAhead.HiddenFoundations.Section3Nonacute
-- supplies the forward direction of the operator-level Halmos classification
-- (`sameHalmosInvariant_of_pairEquiv`).  This module imports only Frontier/Core,
-- so the dependency is acyclic.
import DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosClassification

/-!
# Section 3 frontier: separation and classification of two subspaces

These declarations state the remaining source results and the reusable
classification bridges beneath them.  The first completion target is the
constructive nonacute direct-rotation criterion.  The spectral-multiplicity
formulation is separated from the operator-level Halmos classification so the
latter can be completed without inventing direct-integral infrastructure.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section3

open SpectraBridge

universe u v

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- Davis--Kahan 1970, Proposition 3.1: in the acute case, positivity of the
diagonal compressions characterizes the unique direct rotation. -/
theorem proposition3_1_positivity_characterization
    (hacute : IsAcute U V) (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T) :
    IsPaperDirectRotation U V T ↔
      T = spectraDirectRotation U V hacute := by
  sorry

omit [CompleteSpace H] [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection] in
/-- The paper's crossed intersections are exactly the Halmos source and target
defect spaces. -/
theorem crossed_intersections_are_halmos_defects :
    halmosSourceDefect U V = U ⊓ Vᗮ ∧
      halmosTargetDefect U V = Uᗮ ⊓ V :=
  ⟨rfl, rfl⟩

/-- Davis--Kahan 1970, Proposition 3.2: a nonacute direct rotation exists
exactly when the crossed defect spaces have equal Hilbert dimension, expressed
constructively by a linear isometric equivalence. -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent :
    (∃ T : H →L[ℂ] H, IsPaperDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V :=
  MathAhead.HiddenFoundations.proposition3_2_completed U V

/-- Explicit parameterization of the freedom in Proposition 3.2.  Distinct
unitaries between the crossed defect spaces must produce distinct direct
rotations. -/
theorem proposition3_2_parameterized_nonuniqueness
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) →
          (H →L[ℂ] H),
      (∀ J, IsPaperDirectRotation U V (build J)) ∧
      Function.Injective build :=
  MathAhead.HiddenFoundations.proposition3_2_parameterization_completed U V hdefect

/-- A unitary principal square root of the reflection product. -/
structure IsPrincipalUnitarySquareRoot
    (A T : H →L[ℂ] H) : Prop where
  unitary_mem : T ∈ unitary (H →L[ℂ] H)
  square_eq : T * T = A
  spectrum_right_half_plane :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re

/-- Davis--Kahan 1970, Proposition 3.3, converse direction.  The crossed
intersection mapping condition selects the correct square root on the
minus-one spectral subspace. -/
theorem proposition3_3_principalSquareRoot_converse
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot
      (spectraReflectionProduct U V) T)
    (hcross : T '' (halmosSourceDefect U V : Set H) =
      (halmosTargetDefect U V : Set H)) :
    IsPaperDirectRotation U V T := by
  sorry

/-- Davis--Kahan 1970, Proposition 3.4 in source form: under the half-angle
condition, the square of the direct rotation is the direct rotation between
the reflected source and target subspaces. -/
theorem proposition3_4_square_is_reflected_directRotation
    (hacute : IsAcute U V)
    (hhalf : ∀ x : H,
      0 ≤ RCLike.re
        ⟪x, (spectraOperatorAbsoluteValue
          (spectraCanonicalIntertwiner U V)) x⟫_ℂ - ‖x‖ ^ 2 / 2) :
    -- the reflected pair is existentially quantified, so its orthogonal
    -- projections cannot be found by instance search; they are bound here and
    -- reinstated with `haveI` inside the body
    ∃ (Uref Vref : Submodule ℂ H) (iU : Uref.HasOrthogonalProjection)
        (iV : Vref.HasOrthogonalProjection),
      haveI : Uref.HasOrthogonalProjection := iU
      haveI : Vref.HasOrthogonalProjection := iV
      ∃ hacuteRef : IsAcute Uref Vref,
        spectraDirectRotation U V hacute *
            spectraDirectRotation U V hacute =
          spectraDirectRotation Uref Vref hacuteRef := by
  sorry

/-- A subspace on which both projections reduce and every nonzero source or
target vector has the same projection cosine. -/
def IsFixedCosineReducingSubspace
    (M : Submodule ℂ H) (c : ℝ) : Prop :=
  (projection U).Reduces M ∧
  (projection V).Reduces M ∧
  (∀ x : H, x ∈ M → x ∈ U → ‖projection V x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ V → ‖projection U x‖ = c * ‖x‖)

/-- The fixed-cosine spectral subspace on the generic Halmos summand.

The pair is bound explicitly rather than taken from the section: the body is
still an open obligation, so auto-inclusion would not fire and the subspace
would spuriously fail to depend on the pair it is defined from. -/
noncomputable def fixedCosineSubspace (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (c : ℝ) : Submodule ℂ H := by
  sorry

/-- Davis--Kahan 1970, Proposition 3.5: in the acute case each fixed-angle
spectral subspace is the unique maximal reducing subspace with that angle. -/
theorem proposition3_5_fixedAngle_maximal
    (hacute : IsAcute U V) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c ∧
      ∀ M : Submodule ℂ H,
        IsFixedCosineReducingSubspace U V M c →
          M ≤ fixedCosineSubspace U V c := by
  sorry

/-- Davis--Kahan 1970, Corollary 3.2: interchanging the subspaces preserves the
angle data and reverses the canonical quarter-turn. -/
theorem corollary3_2_reversal_source_form
    (hacute : IsAcute U V) :
    spectraDirectRotation V U
        (_root_.ForMathlib.DavisKahan.IsAcute.symm hacute) =
      star (spectraDirectRotation U V hacute) :=
  MathAhead.Section3.corollary3_2_reversal_completed U V hacute

end OneSpace

section Classification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- Equality of the four elementary Halmos summands, expressed without a
finite-rank substitute. -/
structure SameHalmosTrivialDimensions : Prop where
  common : Nonempty
    (halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
  exterior : Nonempty
    (halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)

/-- The modern operator-level complete invariant: trivial dimensions plus the
unitary-equivalence class of the generic cosine square. -/
structure SameHalmosOperatorInvariant : Prop where
  trivial : SameHalmosTrivialDimensions U₁ V₁ U₂ V₂
  generic : BoundedOperatorsUnitaryEquivalent
    (genericHalmosCosineSq U₁ V₁)
    (genericHalmosCosineSq U₂ V₂)

/-- Forward direction of the operator-level Halmos classification: a unitary
equivalence of the ordered pairs induces the complete operator invariant.  The
restriction of the equivalence to each elementary Halmos summand is a linear
isometric equivalence, and on the generic remainder it intertwines the
cosine-square operator.  Proved axiom-clean in
`MathAhead.HiddenFoundations.sameHalmosInvariant_of_pairEquiv`. -/
theorem sameHalmosOperatorInvariant_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  obtain ⟨hc, hs, ht, he, hg⟩ :=
    MathAhead.HiddenFoundations.sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
  exact ⟨⟨hc, hs, ht, he⟩, hg⟩

/-- Operator-level Halmos classification.  This is the constructive spine of
Davis--Kahan Theorem 3.1 and does not require a direct-integral presentation.

The forward direction is proved (`sameHalmosOperatorInvariant_of_pairEquiv`).
The converse — reconstructing a pair-equivalence from the operator invariant —
still needs two bricks, neither yet available: (1) the generic 2×2 Halmos model,
which upgrades a bare unitary equivalence of the two generic cosine-square
operators to a unitary of the generic subspaces intertwining *both* projections
(equivalently, the reconstruction of the reducing angle pair from `cos²Θ`); and
(2) the block-diagonal orthogonal assembly gluing the four elementary summand
isometries and the generic-part unitary into a global `H₁ ≃ₗᵢ[ℂ] H₂` carrying
`U₁, V₁` to `U₂, V₂`.  On the four elementary summands the assembled map
automatically intertwines both projections, so brick (2) reduces to a
Hilbert-sum gluing and brick (1) is the sole genuinely missing mathematics. -/
theorem twoProjection_operator_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  refine ⟨sameHalmosOperatorInvariant_of_pairEquiv U₁ V₁ U₂ V₂, ?_⟩
  intro _hinv
  sorry

/-- Davis--Kahan 1970, Theorem 3.1: spectral multiplicity data of the two angle
operators, together with the elementary multiplicities, form a complete
invariant. -/
theorem theorem3_1_spectralMultiplicity_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericHalmosCosineSq U₁ V₁)
        (genericHalmosCosineSq U₂ V₂) := by
  sorry

/-- Ordered eigenvalue data for a compact positive contraction.  The eventual
implementation should use approximation numbers or compact self-adjoint
spectral theory and record multiplicities. -/
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (A : K →L[ℂ] K) : ℕ → ℝ := by
  sorry

/-- Davis--Kahan 1970, Corollary 3.1: when the cross-projection is compact, the
angle eigenvalue lists and elementary multiplicities classify the pair. -/
theorem corollary3_1_compact_angleList_classification
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList (genericHalmosCosineSq U₁ V₁) =
        compactAngleEigenvalueList (genericHalmosCosineSq U₂ V₂) := by
  sorry

end Classification

end Section3
end Frontier
end Experimental
end DavisKahan
end ForMathlib
