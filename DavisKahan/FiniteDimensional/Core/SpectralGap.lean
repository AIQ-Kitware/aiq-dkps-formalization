/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.SpectralSubspace

/-!
# Finite-dimensional spectral-gap predicates

Canonical separation hypotheses used by the sine, tangent, double-angle, and
Sylvester theorem families.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Two restricted spectra are separated by at least `δ`. -/
def SpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedSpectrum A U → μ ∈ restrictedSpectrum B V →
    δ ≤ |lam - μ|

/-- The mixed separation used by the `sin Θ` theorem: the selected block of
`A` is separated from the complementary block of `B`. -/
def HybridGap (A B : E →ₗ[𝕜] E) (U V : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  SpectraSeparated A U B Vᗮ δ

/-- Absolute separation between the two diagonal blocks of `A`.

This predicate is appropriate for the `sin Θ` and `sin (2Θ)` families and for
the general disjoint-spectrum Sylvester estimate.  It is not sufficient for
the sharp `tan (2Θ)` theorem: interlacing spectra can satisfy absolute
separation while an off-diagonal perturbation produces a quarter-turn angle.
That theorem requires `OrderedInternalGap` (or an equivalent two-sided form
ordering). -/
def InternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  SpectraSeparated A U A Uᗮ δ

/-- Ordered quadratic-form separation between the two blocks of `A`.

The selected block `U` lies above `b`, while its orthogonal complement lies
below `a`.  Together with `a < b`, this is the sharp constant-one hypothesis
used by the finite-dimensional `sin (2 Θ)` theorem. -/
def TwoBlockFormGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (a b : ℝ) : Prop :=
  (∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) ∧
    (∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)

/-- The interval/exterior form of the mixed gap. -/
def IntervalExteriorGap (A B : E →ₗ[𝕜] E) (U V : Submodule 𝕜 E)
    (a b δ : ℝ) : Prop :=
  SpectrumIn A U (Set.Icc a b) ∧
    SpectrumIn B Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- The one-sided gap used by the tangent theorems. -/
def OrderedGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedSpectrum A U → μ ∈ restrictedSpectrum B V →
    lam + δ ≤ μ

/-- Ordered separation of the two diagonal blocks of `A`, in either
orientation.  This stronger predicate is useful when reducing a double-angle
argument to the elementary ordered Sylvester theorem. -/
def OrderedInternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  OrderedGap A U A Uᗮ δ ∨ OrderedGap A Uᗮ A U δ

omit [FiniteDimensional 𝕜 E] in
/-- Spectral inclusion on opposite sides of a cut gives the corresponding
ordered internal gap. -/
theorem orderedInternalGap_of_spectrumIn_Iic_Ici
    {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} {a b : ℝ}
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    OrderedInternalGap A U (b - a) := by
  left
  intro lam μ hlam hμ
  have hlam_le : lam ≤ a := hUa hlam
  have hb_le_hμ : b ≤ μ := hUb hμ
  linarith

omit [FiniteDimensional 𝕜 E] in
/-- Ordered block separation implies absolute block separation.
-/
theorem OrderedInternalGap.internalGap {A : E →ₗ[𝕜] E}
    {U : Submodule 𝕜 E} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : OrderedInternalGap A U δ) : InternalGap A U δ := by
  intro lam μ hlam hμ
  rcases h with hlow | hhigh
  · have hle := hlow lam μ hlam hμ
    have hlam_le : lam ≤ μ := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hlam_le)]
    linarith
  · have hle := hhigh μ lam hμ hlam
    have hμ_le : μ ≤ lam := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hμ_le)]
    linarith


end DavisKahanTheory
end TauCeti