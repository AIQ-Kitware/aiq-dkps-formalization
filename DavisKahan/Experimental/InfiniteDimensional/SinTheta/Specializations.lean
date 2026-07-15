/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Canonical

/-!
# Specialization bridges from the canonical unbounded sine theorem

This module records how bounded problems should enter the canonical API.  It
is intentionally downstream of `Canonical`: bounded operators are embedded as
full-domain closed operators, their spectral hypotheses are transported to the
closed-operator spectral layer, and the bounded conclusion is then obtained
from the general theorem.

The independent proof in `Bounded.lean` remains useful.  It is not used as a
parent of the declarations here.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Bounded data packaged for derivation from the canonical generalized
unbounded theorem. -/
structure BoundedGeneralSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜)) where
  A : E →L[𝕜] E
  A₀ : F →L[𝕜] F
  Λ₁ : G →L[𝕜] G
  X : F →L[𝕜] E
  F₀ : H →L[𝕜] E
  F₁ : G →L[𝕜] E
  ambient_symmetric : A.IsSymmetric
  trial_symmetric : A₀.IsSymmetric
  complement_symmetric : Λ₁.IsSymmetric
  exact_decomposition : OrthogonalExactDecomposition F₀ F₁
  intertwines : A ∘L F₁ = F₁ ∘L Λ₁
  gap : ℝ
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound X frameLowerBound
  spectral_gap : UnboundedSylvesterGap
    (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A₀)
    (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded Λ₁) gap
  residual_mem : N.toRectangularSymmetricIdealFamily.Mem
    (generalResidual A X A₀)

namespace BoundedGeneralSinThetaProblem

/-- Embed a bounded problem into the full-domain closed-operator problem used
by the canonical theorem.  The remaining proof burden is entirely in the
bounded-to-closed self-adjoint and domain-equation bridge, not in a duplicate
sine-theta proof. -/
noncomputable def toGeneral
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : BoundedGeneralSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    GeneralSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N := by
  let D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) := {
    A := ForMathlib.DavisKahanExt.ClosedOperator.ofBounded P.A
    A₀ := ForMathlib.DavisKahanExt.ClosedOperator.ofBounded P.A₀
    Λ₁ := ForMathlib.DavisKahanExt.ClosedOperator.ofBounded P.Λ₁
    X := P.X
    F₁ := P.F₁
    residual := generalResidual P.A P.X P.A₀
    X_maps_domain := by intro x; simp
    F₁_maps_domain := by intro y; simp
    residual_eq := by
      intro x
      change P.A (P.X (x : F)) - P.X (P.A₀ (x : F)) =
        (generalResidual P.A P.X P.A₀) (x : F)
      simp only [generalResidual, ContinuousLinearMap.comp_apply, sub_apply]
    intertwines := by
      intro y
      have hy := congrArg (fun T : G →L[𝕜] E => T (y : G)) P.intertwines
      change P.A (P.F₁ (y : G)) = P.F₁ (P.Λ₁ (y : G))
      simpa only [ContinuousLinearMap.comp_apply] using hy
  }
  exact {
    data := D
    exactMap := P.F₀
    ambient_selfAdjoint :=
      ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint
        P.A P.ambient_symmetric
    trial_selfAdjoint :=
      ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint
        P.A₀ P.trial_symmetric
    complement_selfAdjoint :=
      ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint
        P.Λ₁ P.complement_symmetric
    exact_decomposition := P.exact_decomposition
    gap := P.gap
    frameLowerBound := P.frameLowerBound
    gap_pos := P.gap_pos
    frameLowerBound_pos := P.frameLowerBound_pos
    lowerFrame := P.lowerFrame
    spectral_gap := P.spectral_gap
    residual_mem := P.residual_mem
  }

/-- Bounded generalized sine theorem derived from the canonical theorem. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : BoundedGeneralSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (directedSinThetaOperator P.X P.F₀ P.lowerFrame
          P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (directedSinThetaOperator P.X P.F₀ P.lowerFrame
              P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge
            (generalResidual P.A P.X P.A₀) :=
  GeneralSinThetaProblem.result N (P.toGeneral N)

end BoundedGeneralSinThetaProblem

omit [CompleteSpace E] [CompleteSpace F] in
/-- Convert the bounded interval/exterior predicate to the closed-operator gap
predicate.  Both predicates use the same closed-operator real spectrum by
definition. -/
theorem intervalExteriorGap_to_unbounded
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    {β α δ : ℝ}
    (hgap : IntervalExteriorGap A B β α δ) :
    UnboundedIntervalExteriorGap
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded B)
      β α δ := by
  exact hgap

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
