/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.BoundedOperator.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Restricted-operator spectra and provisional embedding interfaces

This module provides the theorem-facing spectrum of a bounded operator and of
its actual restriction to an invariant subspace.  These definitions use the
Banach-algebra spectrum, so continuous spectral components are retained in
infinite dimension.  The double-angle embedding remains a provisional target
and should eventually be built from the closed range of an isometric embedding.
-/


/-! ## Construction plan

* Route inequalities derived from real spectra through `RealSpectralBridge`;
  the set definitions here are exact, but the real spectral-order theorem is a
  separate analytic obligation.
* Keep spectral separation hypotheses tied to invariant subspaces.  For a
  self-adjoint operator, the reduction hypotheses used by the paper supply the
  required invariance for both the selected subspace and its orthogonal
  complement.
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

/-- A subspace is invariant under a bounded operator. -/
def InvariantFor (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

/-- Real points in the Banach-algebra spectrum of an `RCLike` operator.

The operator algebra is naturally an algebra over its native scalar field
`𝕜`, not uniformly an algebra over `ℝ`.  We therefore take `spectrum 𝕜 A` and
pull it back along the canonical embedding `ℝ → 𝕜`.  For self-adjoint
operators this captures the full spectrum, while retaining continuous spectral
components in infinite dimension. -/
def realSpectrum (A : E →L[𝕜] E) : Set ℝ :=
  {r | (r : 𝕜) ∈ spectrum 𝕜 A}

/-- Real spectrum of the actual restriction of `A` to an invariant subspace.

The existential packages the invariance proof needed to construct
`A.restrict`.  Proof irrelevance makes the resulting restricted operator
independent of which proof is supplied.  If no invariance proof exists the set
is empty, so theorem-facing containment and separation predicates below also
record invariance explicitly rather than permitting a vacuous gap. -/
def restrictedSpectrum (A : E →L[𝕜] E)
    (U : Submodule 𝕜 E) : Set ℝ :=
  {r | ∃ hU : InvariantFor A U,
    (r : 𝕜) ∈ spectrum 𝕜 (A.restrict hU)}

/-- With a fixed invariance proof, `restrictedSpectrum` is exactly the real
part of the Banach-algebra spectrum of that restriction. -/
theorem restrictedSpectrum_eq_restrictionSpectrum
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (hU : InvariantFor A U) :
    restrictedSpectrum A U = {r : ℝ | (r : 𝕜) ∈ spectrum 𝕜 (A.restrict hU)} := by
  ext r
  constructor
  · rintro ⟨hU', hr⟩
    simpa using hr
  · intro hr
    exact ⟨hU, hr⟩

/-- The spectrum of the actual restriction to `U` is contained in `s`.

Invariance is part of the predicate, preventing a containment hypothesis from
being discharged merely because no restricted operator was available. -/
def SpectrumIn (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (s : Set ℝ) : Prop :=
  InvariantFor A U ∧ restrictedSpectrum A U ⊆ s

/-- A scalar function is uniformly bounded on the real Banach-algebra
spectrum. -/
def BoundedOnSpectrum (A : E →L[𝕜] E) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ realSpectrum A, |f x| ≤ C

/-- Distance between two real spectral sets. -/
noncomputable def spectralDistance (s t : Set ℝ) : ℝ :=
  sInf {r | ∃ x ∈ s, ∃ y ∈ t, r = |x - y|}

/-- Two actual restricted spectra are separated by at least `d`. -/
def SpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  InvariantFor A U ∧ InvariantFor B V ∧
    ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
      d ≤ |a - b|

/-- The selected block of `A` is separated from the complementary block of
`B`. -/
def HybridGap (A B : E →L[𝕜] E) (U V : Submodule 𝕜 E)
    (d : ℝ) : Prop := SpectraSeparated A U B Vᗮ d

/-- Internal spectral gap of an invariant subspace and its invariant
orthogonal complement. -/
def InternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop := SpectraSeparated A U A Uᗮ d

/-- Ordered separation of actual restricted spectra, giving a constant-one
Sylvester estimate. -/
def OrderedSpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  InvariantFor A U ∧ InvariantFor B V ∧
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
