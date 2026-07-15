/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.BoundedOperator.Basic

/-!
# Provisional spectral and embedding interfaces

This module preserves foundational interfaces that remain useful targets for
future work but are not part of the supported bounded dependency graph.  The
abstract spectrum definitions should eventually be replaced by spectra of
actual restricted operators, and the double-angle embedding should eventually
be built from the closed range of an isometric embedding.
-/


/-! ## Construction plan

* Replace `realSpectrum` by the actual spectrum whenever the scalar field and
  operator algebra support it.  For real Hilbert spaces, route spectral
  inequalities through `RealSpectralBridge`; do not create a second opaque
  spectrum once the real bridge exists.
* Define `restrictedSpectrum` from `A.restrict hU`, which requires invariance
  and completeness of the subspace.  The present hypothesis-free declaration
  is only a compatibility surface and should be replaced by a theorem-facing
  construction carrying those data.
* Build `sinTwoThetaEmbedding` from the sine and cosine blocks of the isometric
  embedding.  In principal coordinates its singular values must be
  `sin (2 * theta_i)`; prove this first on the two-plane decomposition and then
  transport it by unitary invariance.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Foundation

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Provisional compatibility predicate for a norm-preserving onto operator. -/
def IsUnitaryOperator (W : E →L[𝕜] E) : Prop :=
  (∀ x, ‖W x‖ = ‖x‖) ∧ Function.Surjective W

/-- A bounded operator represented as an orthogonal projection. -/
def IsOrthogonalProjection (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ P.IsSymmetric

/-- Off-diagonal relative to an explicitly supplied projection. -/
def IsOffDiagonalRelativeToProjection (P H : E →L[𝕜] E) : Prop :=
  P ∘L H ∘L P = 0 ∧
    (ContinuousLinearMap.id 𝕜 E - P) ∘L H ∘L
      (ContinuousLinearMap.id 𝕜 E - P) = 0

/-- Real point spectrum of an `RCLike` operator.

This compatibility layer deliberately uses eigenvectors rather than the
Banach-algebra spectrum.  In finite dimension the two agree for self-adjoint
operators, while this definition remains meaningful without a scalar-specific
functional-calculus bridge. -/
def realSpectrum (A : E →L[𝕜] E) : Set ℝ :=
  {r | ∃ x : E, x ≠ 0 ∧ A x = ((r : ℝ) : 𝕜) • x}

/-- Point spectrum carried by vectors lying in a supplied subspace.

No invariance is required merely to state this set.  The definition records
exactly the eigenpairs whose eigenvectors lie in `U`; theorem-facing uses that
need a genuine restricted operator should additionally supply reduction or
invariance hypotheses. -/
def restrictedSpectrum (A : E →L[𝕜] E)
    (U : Submodule 𝕜 E) : Set ℝ :=
  {r | ∃ x : E, x ∈ U ∧ x ≠ 0 ∧ A x = ((r : ℝ) : 𝕜) • x}

/-- The spectrum carried by `U` is contained in `s`. -/
def SpectrumIn (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (s : Set ℝ) : Prop := restrictedSpectrum A U ⊆ s

/-- A scalar function is uniformly bounded on the provisional real spectrum. -/
def BoundedOnSpectrum (A : E →L[𝕜] E) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ realSpectrum A, |f x| ≤ C

/-- Distance between two real spectral sets. -/
noncomputable def spectralDistance (s t : Set ℝ) : ℝ :=
  sInf {r | ∃ x ∈ s, ∃ y ∈ t, r = |x - y|}

/-- Two restricted spectra are separated by at least `d`. -/
def SpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
    d ≤ |a - b|

/-- The selected block of `A` is separated from the complementary block of
`B`. -/
def HybridGap (A B : E →L[𝕜] E) (U V : Submodule 𝕜 E)
    (d : ℝ) : Prop := SpectraSeparated A U B Vᗮ d

/-- Internal spectral gap of a reducing subspace. -/
def InternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop := SpectraSeparated A U A Uᗮ d

/-- Ordered separation, giving a constant-one Sylvester estimate. -/
def OrderedSpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
    a + d ≤ b

/-- Interval/exterior separation from the classical `sin Θ` theorem. -/
def IntervalExteriorSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F)
    (left right d : ℝ) : Prop :=
  SpectrumIn A U (Set.Icc left right) ∧
    SpectrumIn B V {x | x ≤ left - d ∨ right + d ≤ x}

/-- One spectral component lies in a finite gap of the other. -/
def FiniteGapConfiguration (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  ∃ left right, left ≤ right ∧
    SpectrumIn A U (Set.Icc left right) ∧
    SpectrumIn A Uᗮ {x | x ≤ left - d ∨ right + d ≤ x}

/-- Ordered internal gap, in either orientation. -/
def OrderedInternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  OrderedSpectraSeparated A U A Uᗮ d ∨
    OrderedSpectraSeparated A Uᗮ A U d

/-- Provisional double-angle residual map for an isometric embedding.

Construction route: write `S = P_{Uᗮ} X` for the sine block and
`C = sqrt (X⋆ P_U X)` for the positive cosine block on the coordinate space,
and set the map to `2 S C`; in principal coordinates its singular values are
`sin (2 θ_i)`.  The required square root is a positive-operator square root of
`X⋆ P_U X : F →L[𝕜] F` valid for `RCLike` scalars in infinite dimension.  The
pinned Mathlib registers the continuous-functional-calculus instances on
`F →L[𝕜] F` only for `𝕜 = ℂ` (`CFC.sqrt`), and the local
`LinearMap.IsPositive.sqrt` is finite-dimensional, so no such square root is
available yet; the definition remains open pending that bridge (or a
complexification transport).  The eventual definition should reuse the
supported projection-block API rather than introduce an independent angle
calculus, and should come with the identity
`C ∘L C = X⋆ ∘L P_U ∘L X` from positivity of the compressed projection. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E := by
  sorry

end Foundation
end Experimental
end DavisKahan
end ForMathlib
