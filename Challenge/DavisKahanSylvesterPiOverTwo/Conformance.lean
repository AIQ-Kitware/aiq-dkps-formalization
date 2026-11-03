/-
# Arbitrary-separated finite Sylvester theory with constant pi/2

The exact finite two-sided unitary-orbit certificate for each particular
separated Sylvester solution. The ordinary rectangular seminorm bound now
uses the accepted TauCeti pairwise API (#24932) directly and is retired here.
-/

module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
-- `PointSpectraSeparated` is the *hypothesis* predicate of the challenge, not part of what is to
-- be proved; the challenged theorems live in `DavisKahan.FiniteDimensional.Sylvester.All`,
-- which only the paired leaderboard imports.
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap

/-!
## Comparator maintenance rule

The open proofs below are deliberate challenge placeholders. The
implementations live in the ordinary library module imported by the paired
leaderboard.
-/


public section

-- Comparator statement holes are intentional; see Challenge/README.md.
set_option warn.sorry false

namespace TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Exact finite unitary-orbit certificate, of mass at most pi/2, for a
particular separated Sylvester solution. -/
theorem sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    UnitarilyInvariantSeminorm.HasFiniteUnitaryOrbitCertificate
      (Real.pi / 2) (((δ : 𝕜)) • X) C := by
  sorry

end TauCeti
