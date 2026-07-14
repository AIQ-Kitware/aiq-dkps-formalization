/-
# Arbitrary-separated finite Sylvester theory with constant pi/2

Two advertising-level leaves of the completed generic theory:

* the Bhatia--Davis--McIntosh bound for every rectangular unitarily invariant
  norm;
* an exact finite two-sided unitary-orbit certificate for each particular
  separated Sylvester solution.
-/

import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
## Comparator maintenance rule

The open proofs below are deliberate challenge placeholders. The
implementations live in the ordinary library module imported by the paired
leaderboard.
-/


namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Arbitrary-disjoint-spectrum Sylvester bound in every rectangular
unitarily invariant norm, with constant pi/2. -/
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  sorry

/-- Exact finite unitary-orbit certificate, of mass at most pi/2, for a
particular separated Sylvester solution. -/
theorem sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    RectangularUnitarilyInvariantNorm.HasFiniteUnitaryOrbitCertificate
      (Real.pi / 2) (((δ : 𝕜)) • X) C := by
  sorry

end DavisKahanTheory
end ForMathlib
