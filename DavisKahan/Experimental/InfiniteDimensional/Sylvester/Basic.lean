/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Symmetric
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Resolvent
import ForMathlib.Analysis.InnerProductSpace.SylvesterBound
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
# Infinite-dimensional Sylvester equations

The operator equation `A X - X B = C` is the analytic engine behind the
infinite-dimensional `sin Θ` and residual theorems.

Literature writeup: local TeX, Sections 10--11.
-/


/-! ## Construction plan

* Define the resolvent integral only for complex scalars, a separating contour,
  and operators whose resolvents are defined along that contour.
* Replace the unconditional `solveSylvester` choice by either an inverse of the
  Sylvester operator under separation or an existence-and-uniqueness theorem.
* Prove the contour formula satisfies `AX-XB=C` by inserting the two resolvent
  identities and evaluating winding numbers.
* Derive the ordered constant-one estimate from coercivity; derive the general
  `pi/2` estimate from the contour/double-operator-integral argument.  These are
  distinct theorem families and should remain distinct in the API.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Sylvester operator `X ↦ A X - X B`. -/
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

@[simp] theorem sylvesterOperator_zero
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    sylvesterOperator A B (0 : E →L[𝕜] F) = 0 := by
  simp [sylvesterOperator]

/-- The Sylvester operator preserves addition. -/
theorem sylvesterOperator_add
    (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X + Y) =
      sylvesterOperator A B X + sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp]
  abel

/-- The Sylvester operator preserves subtraction. -/
theorem sylvesterOperator_sub
    (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X - Y) =
      sylvesterOperator A B X - sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp]
  abel

/-- The Sylvester operator commutes with scalar multiplication. -/
theorem sylvesterOperator_smul
    (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (c : 𝕜) (X : E →L[𝕜] F) :
    sylvesterOperator A B (c • X) = c • sylvesterOperator A B X := by
  ext x
  simp [sylvesterOperator, smul_sub]

/-- Resolvent/Bochner integral candidate for the Sylvester solution. -/
noncomputable def sylvesterResolventIntegral (A : F →L[𝕜] F)
    (B : E →L[𝕜] E) (C : E →L[𝕜] F) : E →L[𝕜] F := by
  sorry

/-- Canonical solution selected by the resolvent integral. -/
noncomputable def solveSylvester (A : F →L[𝕜] F)
    (B : E →L[𝕜] E) (C : E →L[𝕜] F) : E →L[𝕜] F :=
  sylvesterResolventIntegral A B C

omit [CompleteSpace E] [CompleteSpace F] in
/-- Bochner/resolvent integral representation of the solution.

`X = ∫ t in Set.Ioi 0, exp(-t A) ∘ C ∘ exp(t B)`.

Ext-agent signature audit (GPT 5.6 High): This unconditional equality is sound only
because `solveSylvester` is intended to be defined by the displayed integral (or by a
choice provably equal to it). It is not an existence theorem without separation.
-/
theorem solveSylvester_eq_resolventIntegral
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (C : E →L[𝕜] F) :
    solveSylvester A B C = sylvesterResolventIntegral A B C := rfl

/-- The resolvent solution satisfies the equation under separated spectra.

Lean proof route for a weaker agent:

1. Use `solveSylvester_eq_resolventIntegral`.
2. Evaluate the Sylvester operator on truncated contour/semigroup integrals.
3. Show the boundary terms converge to zero from spectral separation.
4. Pass the bounded linear Sylvester operator through the integral and obtain `C`.


Ext-agent signature audit (GPT 5.6 High): Correct under positive spectral separation.
The implementation should make the selected solution independent of auxiliary contours.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem sylvester_solve
    {A : F →L[𝕜] F} {B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (C : E →L[𝕜] F) :
    sylvesterOperator A B (solveSylvester A B C) = C := by
  sorry

/-- Sharp constant-one estimate when one spectrum lies in a gap or the convex
hulls are disjoint.

Proof strategy: reduce the spectral hypothesis to ordered quadratic-form
bounds by an affine shift and, when necessary, split the exterior spectrum
into its lower and upper pieces.  Apply the semigroup solution formula and the
bounds

`‖exp(-t A)‖ <= exp(-a t)` and `‖exp(t B)‖ <= exp(b t)`.

Integrating gives `‖X‖ <= ‖C‖ / (a-b)`.  For interval/exterior separation,
solve the two orthogonal spectral pieces separately and recombine them using
orthogonality.  This is the first analytic theorem to prove because its finite
specialization immediately replaces duplicated operator-norm arguments.

Lean proof route for a weaker agent:

1. Shift `A,B` so the spectral bounds become `A≥d/2` and `B≤-d/2`.
2. Represent `X` by the semigroup integral `∫₀∞ exp(-tA) C exp(tB) dt`.
3. Bound the integrand by `exp(-dt)‖C‖` using functional calculus.
4. Integrate, use uniqueness, and multiply by `d`.


Ext-agent signature audit (GPT 5.6 High): The orientation is correct for `A X - X B`:
the hypothesis says the spectrum of `A` lies at least `d` above that of `B`.
Interval/exterior splitting should be a separate corollary.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem norm_sylvester_le_of_orderedSeparation
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  sorry

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The sharp constant-one Sylvester operator-norm bound, quadratic-form
(coercivity) form — dimension-free and completeness-free.**  If the quadratic
form of the self-adjoint `A` is at least `(c+g)‖·‖²` while that of `B` is at most
`c‖·‖²`, and `A X − X B = C`, then `‖X‖ ≤ ‖C‖ / g`.

This is the analytic engine of the infinite-dimensional `sin Θ` theorem, proved
by the integral-free absorption argument
`ForMathlib.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq` (no semigroup
integral, no spectral measure, no dimension hypothesis).  The
`OrderedSpectraSeparated` hypothesis of `norm_sylvester_le_of_orderedSeparation`
now uses spectra of the actual restricted operators.  The remaining bridge is
the bounded spectral-order theorem converting that ordered spectral inclusion
to these quadratic-form bounds; it is already available for complex Hilbert
spaces and remains open at full `RCLike` generality. -/
theorem norm_sylvester_le_of_coercive
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : sylvesterOperator A B X = C) :
    ‖X‖ ≤ ‖C‖ / g :=
  ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq hA hB hg hAc hBc hEq

/-- General separated-spectrum estimate with the `π / 2` constant.

Proof strategy: do not derive this from the ordered theorem.  Choose a scalar
function `f` with Fourier transform representing `1 / (lam-mu)` on pairs of
spectral points at distance at least `d`.  Express the inverse Sylvester map as
an operator integral of left and right unitary groups.  The scalar multiplier
lemma gives total variation `pi/(2*d)`, hence the norm bound.  Formalization
should isolate:

1. the scalar Fourier/multiplier construction;
2. Bochner integration of the two-sided unitary orbit;
3. evaluation of the Sylvester defect;
4. the final `L1` estimate.

This theorem belongs after the constant-one ordered theory.

Lean proof route for a weaker agent:

1. Use the scalar Fourier multiplier for `1/(a-b)` on pairs separated by `d`.
2. Represent `X` as an integral of `exp(itA) C exp(-itB)` against that measure.
3. Bound every unitary orbit term by `‖C‖` and integrate total variation `π/(2d)`.
4. Use uniqueness of the Sylvester solution to identify the integral with the given `X`.


Ext-agent signature audit (GPT 5.6 High): Correct with the universal `π/2` constant for
arbitrary separated self-adjoint spectra. Do not accidentally claim constant one from
absolute pairwise separation alone.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem norm_sylvester_le_of_generalSeparation
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ (Real.pi / 2) * ‖C‖ := by
  sorry

/-- Uniqueness of the bounded Sylvester solution.

Lean proof route for a weaker agent:

1. Apply the general separated-spectrum norm estimate to `X-Y` with right-hand side zero.
2. Use linearity of `sylvesterOperator` and `hX` to prove its defect is zero.
3. Since `d>0`, conclude `‖X-Y‖=0`, then extensionality gives `X=Y`.


Ext-agent signature audit (GPT 5.6 High): Correct and best proved from the general
separated-spectrum estimate, not by duplicating resolvent algebra.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem sylvester_unique
    {A : F →L[𝕜] F} {B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    {X Y : E →L[𝕜] F}
    (hX : sylvesterOperator A B X = sylvesterOperator A B Y) :
    X = Y := by
  have hzero : sylvesterOperator A B (X - Y) = 0 := by
    rw [sylvesterOperator_sub, hX, sub_self]
  have hle := norm_sylvester_le_of_generalSeparation hA hB hd hsep hzero
  rw [norm_zero, mul_zero] at hle
  have hnorm : ‖X - Y‖ = 0 := by
    nlinarith [norm_nonneg (X - Y)]
  rw [← sub_eq_zero]
  exact norm_eq_zero.mp hnorm

end DavisKahanExt
end ForMathlib
