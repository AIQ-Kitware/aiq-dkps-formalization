/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-!
# Sylvester separation predicates

Source-facing interval and ordered gap predicates for Sylvester estimates. The
finite-dimensional Sylvester operator and its separated-spectrum solution are
provided by Tau Ceti's canonical `ContinuousLinearMap.sylvester` API.

## Sources

Solvability of `A X - X B = C` under separated spectra is Rosenblum's theorem, and
the norm estimate under a spectral gap is Bhatia--Davis--McIntosh; both are
distilled in
`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`.

## Provenance

The retained gap predicates were *moved, not restated*. This file was
`DavisKahan/FiniteDimensional/Sylvester/Basic.lean`
before the whole remaining sin-Θ closure moved into
the staging layer. The local finite-dimensional Sylvester operator and solver
formerly in this file have since been retired in favor of Tau Ceti's canonical
`ContinuousLinearMap.sylvester` API.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
/-- Ordered spectral separation for the Sylvester equation. -/
@[expose]
def OrderedSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (δ : ℝ) : Prop :=
  OrderedGap B ⊤ A ⊤ δ ∨ OrderedGap A ⊤ B ⊤ δ

/-- Interval/exterior separation with the spectrum of `B` in `[a,b]` and the
spectrum of `A` outside `(a-δ,b+δ)`. -/
@[expose]
def IntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  Module.End.PointSpectrumIn B ⊤ (Set.Icc a b) ∧
    Module.End.PointSpectrumIn A ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- Interval/exterior separation in either orientation.  The first branch has
the spectrum of `B` in `[a,b]` and that of `A` outside the enlarged interval;
the second branch reverses those roles. -/
@[expose]
def UnorderedIntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  IntervalSylvesterGap A B a b δ ∨ IntervalSylvesterGap B A a b δ


end TauCeti
