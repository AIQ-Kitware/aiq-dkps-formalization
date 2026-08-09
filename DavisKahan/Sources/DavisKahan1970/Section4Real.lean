/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section4
import DavisKahan.Sources.DavisKahan1970.Section4BasisAngleEnergy
import DavisKahan.Geometry.Polar.DirectRotationReal
import DavisKahan.OperatorIdeal.ComplexificationApproximation

/-!
# Davis--Kahan 1970, Section 4 over a **real** Hilbert space

Standing assumption 1 of the paper is that the Hilbert space is "real or
complex", and Section 4 is written over an infinite orthonormal sequence, so its
printed scope is a real *or* complex Hilbert space of arbitrary dimension.  The
repository's infinite-dimensional Section 4 is proved over `ℂ`.  This module
supplies the real half, in arbitrary dimension, with no loss of constant and with
ideal membership concluded rather than assumed.

## Why no new analysis is needed

Two facts already in the repository do all the work, and neither was recorded
against the Section 4 rows.

* `…ExactSinTheta.ComplexificationApproximation.approximationNumber_complexify`
  says a real operator and its complexification have **equal** approximation
  numbers -- not merely comparable ones.  Its two halves are the real
  Courant--Fischer localization (lower) and complexification of real finite-rank
  approximants (upper).  Consequently every finite Ky Fan approximation gauge is
  preserved exactly, which is
  `…ComplexificationApproximation.kyFanApproximationGauge_complexify`.
* `DavisKahan/Geometry/Polar/DirectRotationReal.lean` supplies the real direct
  rotation and proves it is the real restriction of the complex one.

So the real minimizer is the real direct rotation, the real competitor is an
arbitrary real orthogonal operator carrying `U` onto `V`, and the inequality is
the complex one read through an equality of approximation numbers.

## The ideal family is real

Corollary 4.1 is stated here over a **real** `KyFanDominantIdealFamily`, not by
transporting a complex one.  That is deliberate: `KyFanDominantIdealFamily` is
`RCLike`-generic but carries no gauge-complexification law, so a complex family's
gauge cannot be read on real operators.  Nothing needs it to be: the certificate
`RestrictedDisplacementApproximationDominance` and the bridge
`restrictedDisplacement_idealGauge_le` are both `RCLike`-generic, so a real
certificate feeds a real family directly.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Section 4, Propositions 4.1 and
  4.3 and Corollary 4.1, and standing assumption 1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental
open TauCeti.DavisKahan.Experimental.ExactSinTheta
open TauCeti.DavisKahan.Experimental.ExactSinTheta.ComplexificationApproximation
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Experimental.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ### Transport of the two displacement shapes -/

/-- The restricted displacement of a complexified operator is the
complexification of the real restricted displacement. -/
theorem complexify_restrictedDisplacement (W : E →L[ℝ] E) :
    complexify ((1 - W) ∘L DavisKahan.projection U) =
      (1 - complexify W) ∘L DavisKahan.projection (complexifySubmodule U) := by
  rw [complexify_comp, complexify_sub, Experimental.complexify_one,
    Experimental.complexify_projection]

/-- The squared full displacement of a complexified operator is the
complexification of the real one. -/
theorem complexify_displacementSquare (W : E →L[ℝ] E) :
    complexify ((1 - star W) * (1 - W)) =
      (1 - star (complexify W)) * (1 - complexify W) := by
  rw [Experimental.complexify_mul, complexify_sub, complexify_sub, Experimental.complexify_one,
    Experimental.complexify_star]

/-- A real intertwining relation complexifies. -/
theorem complexify_intertwines {W : E →L[ℝ] E}
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) :
    complexify W * DavisKahan.projection (complexifySubmodule U) =
      DavisKahan.projection (complexifySubmodule V) * complexify W := by
  rw [← Experimental.complexify_projection, ← Experimental.complexify_projection,
    ← Experimental.complexify_mul, ← Experimental.complexify_mul, hWmap]

/-! ### Proposition 4.1 -/

/-- **Davis--Kahan 1970, Proposition 4.1, over a real Hilbert space of arbitrary
dimension.**

For every orthogonal `W` on a real Hilbert space carrying `U` onto `V`, every
approximation number of the displacement restricted to `U` is minimized by the
real direct rotation.  Approximation numbers stand in for singular values, which
is the correct reading past the compact case. -/
theorem Proposition4_1_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) (n : ℕ) :
    ContinuousLinearMap.approximationNumber
        ((1 - Experimental.directRotationR U V hacute) ∘L DavisKahan.projection U) n ≤
      ContinuousLinearMap.approximationNumber ((1 - W) ∘L DavisKahan.projection U) n := by
  rw [← approximationNumber_complexify, ← approximationNumber_complexify,
    complexify_restrictedDisplacement, complexify_restrictedDisplacement,
    Experimental.complexify_directRotationR]
  exact MathAhead.Section4.proposition4_1_restrictedDisplacement_approximationNumbers_scratch
    (complexifySubmodule U) (complexifySubmodule V)
    (Experimental.isUniformlyAcute_complexifySubmodule U V hacute) (complexify W)
    (Experimental.complexify_mem_unitary hWunitary)
    (complexify_intertwines U V hWmap) n

/-- The Proposition 4.1 certificate for a real pair, in the shape the ideal
bridge consumes. -/
theorem restrictedDisplacementDominance_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) :
    MathAhead.Section4.RestrictedDisplacementApproximationDominance
      ((1 - Experimental.directRotationR U V hacute) ∘L DavisKahan.projection U)
      ((1 - W) ∘L DavisKahan.projection U) where
  approximation_le n := Proposition4_1_real U V hacute W hWunitary hWmap n

/-! ### Corollary 4.1 -/

/-- **Davis--Kahan 1970, Corollary 4.1, over a real Hilbert space of arbitrary
dimension.**

For every Ky-Fan-dominant symmetric ideal family of operators on real Hilbert
spaces, the real direct rotation's restricted displacement lies in the ideal and
its gauge is least among all orthogonal `W` carrying `U` onto `V`.  Membership is
concluded. -/
theorem Corollary4_1_real (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    N.Mem ((1 - Experimental.directRotationR U V hacute) ∘L DavisKahan.projection U) ∧
      N.gauge ((1 - Experimental.directRotationR U V hacute) ∘L DavisKahan.projection U) ≤
        N.gauge ((1 - W) ∘L DavisKahan.projection U) :=
  MathAhead.Section4.restrictedDisplacement_idealGauge_le N
    (restrictedDisplacementDominance_real U V hacute W hWunitary hWmap) hWmem

/-- The operator-norm specialization of Corollary 4.1 over `ℝ`. -/
theorem Corollary4_1_opNorm_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) :
    ‖(1 - Experimental.directRotationR U V hacute) ∘L DavisKahan.projection U‖ ≤
      ‖(1 - W) ∘L DavisKahan.projection U‖ :=
  MathAhead.Section4.restrictedDisplacement_opNorm_le
    (restrictedDisplacementDominance_real U V hacute W hWunitary hWmap)

/-! ### Proposition 4.2 -/

/-- The squared sine of the angle between a unit vector and its displacement
under a real orthogonal operator. -/
def displacementAngleSineSqR (W : E →L[ℝ] E) (x : E) : ℝ :=
  1 - ⟪x, W x⟫_ℝ ^ 2

omit [CompleteSpace E] in
/-- The real displacement-angle cost is the complex one evaluated on the real
copy. -/
theorem displacementAngleSineSq_complexify (W : E →L[ℝ] E) (x : E) :
    MathAhead.Section4.displacementAngleSineSq (complexify W) (ofReal x) =
      displacementAngleSineSqR W x := by
  rw [MathAhead.Section4.displacementAngleSineSq, displacementAngleSineSqR, complexify_ofReal,
    inner_ofReal]
  norm_num

/-- **Davis--Kahan 1970, Proposition 4.2, termwise, over a real Hilbert space of
arbitrary dimension.** -/
theorem displacementAngleSineSq_ge_real
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    {x : E} (hx : x ∈ U) (hxnorm : ‖x‖ = 1) :
    1 - ‖Experimental.canonicalAbsoluteValueR U V x‖ ^ 2 ≤
      displacementAngleSineSqR W x := by
  have h := MathAhead.Section4.displacementAngleSineSq_ge
    (complexifySubmodule U) (complexifySubmodule V)
    (complexify W) (Experimental.complexify_mem_unitary hWunitary)
    (complexify_intertwines U V hWmap)
    ((ofReal_mem_complexifySubmodule_iff U x).2 hx)
    (by rw [ofReal.norm_map]; exact hxnorm)
  rwa [displacementAngleSineSq_complexify,
    ← Experimental.complexify_canonicalAbsoluteValueR, complexify_ofReal,
    ofReal.norm_map] at h

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space**, on an
arbitrary finite subfamily of unit vectors of `U`.  As over `ℂ`, orthonormality
is what makes the two sides the paper's energies, not what makes the estimate
true. -/
theorem sum_displacementAngleSineSq_ge_of_mem_real
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    {ι : Type*} (b : ι → E) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1)
    (s : Finset ι) :
    ∑ i ∈ s, (1 - ‖Experimental.canonicalAbsoluteValueR U V (b i)‖ ^ 2) ≤
      ∑ i ∈ s, displacementAngleSineSqR W (b i) :=
  Finset.sum_le_sum fun i _ =>
    displacementAngleSineSq_ge_real U V W hWunitary hWmap (hb i) (hbnorm i)

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space, with no
summability convention.**  Both sums are unconditionally defined in `ℝ≥0∞` and
the index type is arbitrary. -/
theorem tsum_displacementAngleSineSq_ge_of_mem_real
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    {ι : Type*} (b : ι → E) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1) :
    ∑' i, ENNReal.ofReal (1 - ‖Experimental.canonicalAbsoluteValueR U V (b i)‖ ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSqR W (b i)) :=
  ENNReal.tsum_le_tsum fun i =>
    ENNReal.ofReal_le_ofReal
      (displacementAngleSineSq_ge_real U V W hWunitary hWmap (hb i) (hbnorm i))

/-! ### Proposition 4.3 -/

/-- **Davis--Kahan 1970, Proposition 4.3, over a real Hilbert space of arbitrary
dimension.**

Every Ky Fan sum of the approximation numbers of the squared full displacement
`(1 - Wᵀ)(1 - W)` is minimized by the real direct rotation.  Ky Fan level is the
honest scope: the individual approximation numbers are *not* dominated, which is
what the repository's refutation of Proposition 4.4 records. -/
theorem Proposition4_3_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W) (k : ℕ) :
    kyFanApproximationGauge k
        ((1 - star (Experimental.directRotationR U V hacute)) *
          (1 - Experimental.directRotationR U V hacute)) ≤
      kyFanApproximationGauge k ((1 - star W) * (1 - W)) := by
  rw [← kyFanApproximationGauge_complexify, ← kyFanApproximationGauge_complexify,
    complexify_displacementSquare, complexify_displacementSquare,
    Experimental.complexify_directRotationR]
  exact MathAhead.Section4.proposition4_3_squaredDisplacement_kyFan_scratch
    (complexifySubmodule U) (complexifySubmodule V)
    (Experimental.isUniformlyAcute_complexifySubmodule U V hacute) (complexify W)
    (Experimental.complexify_mem_unitary hWunitary)
    (complexify_intertwines U V hWmap) k

end

end DavisKahan1970
end TauCeti
