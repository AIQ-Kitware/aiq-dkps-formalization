/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
import DavisKahan.SinTheta.SpectralBridge
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# `RCLike` spectral-bridge lemmas

The affine-shift estimates in
`DavisKahan.Experimental.InfiniteDimensional.SinTheta.SpectralBridge` were written
against a `RCLikeSpectralBridge.*` namespace (plus `centered_sylvester_equation`
and `boundedInverseDataOfIsUnit`) that had no definitions anywhere in the tree,
so that file could not elaborate and neither could `SinTheta/General.lean`
downstream.  This file supplies that machinery.

Proved here: the Sylvester recentering identity, the `IsUnit`→bounded-inverse
constructor, the self-adjoint operator-norm/spectral-radius bound (via the
`RCLike` Rayleigh theorem), and self-adjointness→normality of the inverse.

Three genuine `RCLike` spectral facts remain isolated as leaf obligations — none
has direct Mathlib support over general `RCLike` (they hold via complexification):

* `mem_spectrum_sub_real_scalar_iff` — the spectrum of a self-adjoint operator is
  real, so `σ(A - c) = σ(A) - c ⊆ ℝ`;
* `spectrum_inverse_of_isUnit` — the spectral-mapping identity `σ(T⁻¹) = σ(T)⁻¹`;
* `norm_le_of_normal_spectrum_norm_le` — the normal-operator norm/spectral-radius
  bound (Mathlib's version is `CStarAlgebra`, i.e. `ℂ`-only).
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Recentering a Sylvester equation by a real scalar leaves the right-hand side
unchanged: `(A - c)X - X(B - c) = AX - XB`. -/
theorem centered_sylvester_equation
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (X C : F →L[𝕜] E) (c : ℝ)
    (hEq : A ∘L X - X ∘L B = C) :
    (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ∘L X -
      X ∘L (B - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F) = C := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, ← hEq]
  abel

/-- A unit of the bounded-operator ring carries two-sided bounded-inverse data. -/
noncomputable def boundedInverseDataOfIsUnit {T : E →L[𝕜] E} (hunit : IsUnit T) :
    BoundedInverseData T where
  inv := ↑hunit.unit⁻¹
  left_inv := by have h := hunit.unit.inv_mul; rw [hunit.unit_spec] at h; exact h
  right_inv := by have h := hunit.unit.mul_inv; rw [hunit.unit_spec] at h; exact h

/-- A real scalar multiple of the identity is a symmetric operator. -/
theorem isSymmetric_real_smul_id (c : ℝ) :
    (((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E).IsSymmetric := fun x y => by
  simp [inner_smul_left, inner_smul_right, RCLike.conj_ofReal]

namespace RCLikeSpectralBridge

/-- **Leaf obligation.** For self-adjoint `A`, `σ(A - c·1)` is real and equals
`σ(A) - c`; over general `RCLike` this needs the complexification transport of
"self-adjoint spectrum is real". -/
theorem mem_spectrum_sub_real_scalar_iff
    {A : E →L[𝕜] E} (_hA : A.IsSymmetric) {c : ℝ} {z : 𝕜}
    (_hz : z ∈ spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)) :
    ∃ r : ℝ, r ∈ boundedRealSpectrum A ∧ z = (((r - c : ℝ)) : 𝕜) :=
  sorry

/-- A self-adjoint operator whose spectrum sits in the closed ball of radius `ρ`
has operator norm at most `ρ`.  Proof: its norm equals its spectral radius
(`RCLike` Rayleigh theorem), which is bounded by `ρ`. -/
theorem norm_le_of_selfAdjoint_spectrum_subset_closedBall
    {T : E →L[𝕜] E} (hSelf : T.IsSymmetric) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hspec : spectrum 𝕜 T ⊆ Metric.closedBall 0 ρ) : ‖T‖ ≤ ρ := by
  have hSA : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hSelf
  have hrad : spectralRadius 𝕜 T = ‖T‖₊ := ContinuousLinearMap.spectralRadius_eq_nnnorm T hSA
  have hbound : spectralRadius 𝕜 T ≤ (ρ.toNNReal : ENNReal) := by
    refine iSup₂_le fun z hz => ?_
    have hzρ : ‖z‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hspec hz
    have : ‖z‖₊ ≤ ρ.toNNReal := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal ρ hρ]; exact hzρ
    exact_mod_cast this
  rw [hrad] at hbound
  have hnn : ‖T‖₊ ≤ ρ.toNNReal := by exact_mod_cast hbound
  calc ‖T‖ = (‖T‖₊ : ℝ) := rfl
    _ ≤ (ρ.toNNReal : ℝ) := by exact_mod_cast hnn
    _ = ρ := Real.coe_toNNReal ρ hρ

/-- **Leaf obligation.** The spectral-mapping identity `σ(T⁻¹) = σ(T)⁻¹` for a
bounded unit; no direct Mathlib lemma over general `RCLike`. -/
theorem spectrum_inverse_of_isUnit {T : E →L[𝕜] E} (hunit : IsUnit T) :
    spectrum 𝕜 (boundedInverseDataOfIsUnit hunit).inv =
      (fun z : 𝕜 => z⁻¹) '' spectrum 𝕜 T :=
  sorry

/-- The inverse of a self-adjoint unit is self-adjoint, hence normal. -/
theorem inverse_isNormal {T : E →L[𝕜] E} (hTself : T.IsSymmetric) (hunit : IsUnit T) :
    IsStarNormal (boundedInverseDataOfIsUnit hunit).inv := by
  set D := boundedInverseDataOfIsUnit hunit with hD
  have hTSA : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTself
  -- `D.inv⋆` is a left inverse of `T`, so by uniqueness `D.inv⋆ = D.inv`.
  have hleft : (star D.inv) ∘L T = ContinuousLinearMap.id 𝕜 E := by
    have h := congrArg (fun S : E →L[𝕜] E => star S) D.right_inv
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id] at h
    rwa [hTSA.adjoint_eq] at h
  have hself : IsSelfAdjoint D.inv := D.inv_eq hleft
  exact hself.isStarNormal

/-- **Leaf obligation.** A normal operator whose spectrum has norm at most `b` has
operator norm at most `b`.  Mathlib's normal norm/spectral-radius identity is
`CStarAlgebra` (`ℂ`) only; over `RCLike` this needs complexification. -/
theorem norm_le_of_normal_spectrum_norm_le
    {S : E →L[𝕜] E} (_hNormal : IsStarNormal S) {b : ℝ} (_hb : 0 ≤ b)
    (_hspec : ∀ z ∈ spectrum 𝕜 S, ‖z‖ ≤ b) : ‖S‖ ≤ b :=
  sorry

end RCLikeSpectralBridge
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
