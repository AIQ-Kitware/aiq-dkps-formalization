/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Geometry.Angle.Proposition35Infinite

/-!
# Davis--Kahan 1970, Proposition 3.5, in arbitrary Hilbert dimension

This file is the paper-facing surface for Proposition 3.5.  The proposition is
stated in Section 3 for an acute pair of closed subspaces in a real or complex
Hilbert space, without a finite-dimensional hypothesis.

The implementation in `DavisKahan.Geometry.Angle.Proposition35Infinite`
constructs the literal bounded angle

`Theta = arcsin |P - Q|`,

the acute direct rotation `W`, and the quarter turn `J` from the polar
resolution

`W = cos Theta + J sin Theta`.

The theorems below expose the six printed assertions: the four commutations,
the vector-angle identity on an angle eigenvector, and the unique maximality of
the corresponding angle eigenspace under the paper's conditions (a)--(c).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open DavisKahan.Experimental
open DavisKahan.Experimental.MathAhead.HiddenFoundations
open DavisKahan.Experimental.Frontier.Section3
open DavisKahan.Experimental.Proposition35

noncomputable section

/-- The literal operator angle used in Proposition 3.5. -/
alias proposition3_5_angleOperator := section3AngleOperator

/-- The paper's direct rotation in Proposition 3.5. -/
alias proposition3_5_directRotation := section3DirectRotation

/-- The paper's quarter turn `J`, zero on the zero-angle space. -/
alias proposition3_5_quarterTurn := section3QuarterTurn

/-- The spectral eigenspace `Omega({theta}) H` at an angle eigenvalue. -/
alias proposition3_5_angleEigenspace := section3AngleEigenspace

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The defining polar resolution of the quarter turn used by Proposition 3.5:
`W = cos Theta + J sin Theta`. -/
theorem proposition3_5_directRotation_resolution (hacute : TauCeti.IsAcute U V) :
    proposition3_5_directRotation U V =
      section3CosAngleOperator U V +
        proposition3_5_quarterTurn U V ∘L section3SinAngleOperator U V :=
  section3DirectRotation_eq_cos_add_quarterTurn_sin U V hacute

/-- **Davis--Kahan 1970, Proposition 3.5, the four commutation assertions.**
In the acute case `Theta` commutes with `P`, `Q`, the quarter turn `J`, and the
direct rotation `W`. -/
theorem proposition3_5_commutations (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (projection U) ∧
      Commute (proposition3_5_angleOperator U V) (projection V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  ⟨section3AngleOperator_comm_projection U V,
    section3AngleOperator_comm_projection_right U V,
    section3AngleOperator_comm_quarterTurn U V hacute,
    section3AngleOperator_comm_directRotation U V hacute⟩

/-- **Davis--Kahan 1970, Proposition 3.5, eigenvector assertion.**
If `x` is a nonzero eigenvector of `Theta` with eigenvalue `theta`, the vector
angle from `x` to its direct rotation is exactly `theta`.  `vectorAngle` is the
paper's vector angle (1.14), using the real part of the inner product. -/
theorem proposition3_5_eigenvector_angle (hacute : TauCeti.IsAcute U V)
    {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : proposition3_5_angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (proposition3_5_directRotation U V x) = θ :=
  vectorAngle_section3DirectRotation_eq_of_angleOperator_apply U V hacute hx0 hx

/-- The actual angle eigenspace is the fixed-cosine Halmos eigenspace used by
the paper's maximality argument. -/
theorem proposition3_5_angleEigenspace_eq_fixedCosineSubspace
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    proposition3_5_angleEigenspace U V θ = fixedCosineSubspace U V (Real.cos θ) :=
  section3AngleEigenspace_eq_fixedCosineSubspace U V hacute hθ

/-- **Davis--Kahan 1970, Proposition 3.5, maximal-eigenspace assertion.**
For every genuine angle eigenvalue `theta`, `Omega({theta}) H` itself has the
printed properties (a)--(c), and every subspace having those printed properties
is contained in it.  Thus it is the unique maximal such subspace. -/
theorem proposition3_5_angleEigenspace_uniqueMaximal
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    IsPrintedFixedCosineReducingSubspace U V
        (proposition3_5_angleEigenspace U V θ) (Real.cos θ) ∧
      ∀ M : Submodule 𝕜 H,
        IsPrintedFixedCosineReducingSubspace U V M (Real.cos θ) →
          M ≤ proposition3_5_angleEigenspace U V θ := by
  have h := proposition3_5_angleEigenspace_maximal U V hacute hθ
  exact
    ⟨isPrintedFixedCosineReducingSubspace_of_isFixedCosineReducingSubspace
        U V (Real.cos θ) h.1,
      h.2⟩

end Generic

end DavisKahan1970
end TauCeti
