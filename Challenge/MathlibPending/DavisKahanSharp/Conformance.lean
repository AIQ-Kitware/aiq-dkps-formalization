/-
# Sharp symmetric Davis--Kahan sin-Theta theorem (pending comparator challenge)

This challenge imports the trusted statement vocabulary but not the theorem's
implementation. The paired leaderboard imports the completed project theorem.
-/

import DavisKahan.FiniteDimensional.Core.All

/-!
## Comparator maintenance rule

The proof hole in this module is a deliberate challenge placeholder. Do not
discharge it in this repository and do not count it as formalization debt.
The implementation belongs in `DavisKahan/FiniteDimensional/SinTheta/Perturbation.lean`; Comparator
verifies that implementation against this independently compiled statement.
-/


namespace TauCeti
namespace DavisKahanTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- Sharp full-space sin-Theta bound for every unitarily invariant norm under
forward and reverse interval/exterior gaps. -/
theorem sinAngleOperator_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (hgapUV : IntervalExteriorGap A B U V a b δ)
    (hgapVU : IntervalExteriorGap B A V U c d δ) :
    δ * N (sinAngleOperator U V) ≤ N (B - A) := by
  sorry

end DavisKahanTheory
end TauCeti