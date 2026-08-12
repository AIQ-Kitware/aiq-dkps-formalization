import DavisKahan.FiniteDimensional.Core.All

/-!
# Sharp finite Davis--Kahan projector-difference theorems

This is the canonical modern projector/subspace-distance presentation that sits
alongside the four trigonometric headline challenges.  It is not a fifth named
Section 2 trigonometric theorem; it is the familiar projector formulation of
the same perturbation theory.

The factor-one operator-norm theorem for two reducing subspaces carrying
matching selected and complementary spectral gaps, followed by its canonical
spectral-subspace specialization. No rank comparison is assumed.

## Comparator maintenance rule

The open proofs below are deliberate challenge placeholders. The
implementations live in the ordinary library module imported by the paired
leaderboard.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Sharp factor-one projector-difference theorem under two-sided gaps. -/
theorem projector_difference_opNorm {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 E} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hW : IsInvariant B W)
    {c g ε : ℝ} (hg : 0 < g)
    (hUhi : SpectrumIn A U (Set.Ici (c + g)))
    (hUlo : SpectrumIn A Uᗮ (Set.Iic c))
    (hWhi : SpectrumIn B W (Set.Ici (c + g)))
    (hWlo : SpectrumIn B Wᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - W.starProjection : E →L[𝕜] E)‖ ≤ ε / g := by
  sorry

/-- Sharp factor-one projector-difference theorem for canonical spectral
subspaces. -/
theorem spectralProjector_difference_opNorm {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hAhi : SpectrumIn A (spectralSubspace A s) (Set.Ici (c + g)))
    (hAlo : SpectrumIn A (spectralSubspace A s)ᗮ (Set.Iic c))
    (hBhi : SpectrumIn B (spectralSubspace B t) (Set.Ici (c + g)))
    (hBlo : SpectrumIn B (spectralSubspace B t)ᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((spectralSubspace A s).starProjection
        - (spectralSubspace B t).starProjection : E →L[𝕜] E)‖ ≤ ε / g := by
  sorry

end DavisKahanTheory
end TauCeti