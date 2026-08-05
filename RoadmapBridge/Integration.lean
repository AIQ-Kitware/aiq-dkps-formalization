/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
import ForTauCeti.Analysis.InnerProductSpace.SchattenNorm

/-!
# Roadmap bridge: cross-module integration seams

**What this file is for.** Each seam below joins declarations that live in *different*
`ForTauCeti` modules, and each is a place where the two sides can drift apart without any
single module failing to compile.  Every entry is an anonymous `example`, so it asserts
nothing and adds no public name: its only job is to stop elaborating if the seam moves.

The seams are not hypothetical.  All three are recorded regressions or review findings:

1. **A redundant hypothesis on a public signature.**  `sinTheta_spectralSubspace_le` used to
   take an `hAselected : SpectrumIn A (spectralSubspace A (Set.Icc a b)) (Set.Icc a b)`
   argument.  That fact is *free* — it holds of the spectral subspace by construction — and
   is now proved once, as `spectrumIn_spectralSubspace`.  Nothing prevents a future edit from
   re-adding the argument, and the library would still build; the example below would not.
2. **Four names for one number.**  The square Frobenius seminorm, the rectangular Frobenius
   seminorm, the Schatten `S₂` norm and the Hilbert--Schmidt energy are four separate
   definitions in four modules.  Three theorems relate them; this file checks that the
   composite chain closes, which no one of the three does on its own.
3. **A deleted compatibility layer.**  `DavisKahan/SpectralTheory/Compatibility.lean` held 46
   forwarding declarations and was removed.  This file imports canonical owner modules
   directly and names nothing from that layer.

## What this file deliberately does not claim

Two items remain unresolved and no example here is arranged to suggest otherwise:
unbounded graph/Riccati existence, contractivity, bounds and uniqueness; and the exact
spectral-cutoff approximation-number theorem naming the spectral projection, the compression,
the finite-rank hypothesis and the conclusion in one statement.
-/

namespace RoadmapBridge.Integration

open TauCeti

/-! ## Seam 1 — the spectral subspace supplies its own spectral-containment hypothesis

`spectrumIn_spectralSubspace` is the theorem that made the `hAselected` argument redundant.
The example restates the sin-Θ bound with *only* the exterior hypothesis about `B`; if
`hAselected` ever returns to the signature, this stops elaborating. -/

section SpectralSubspaceSinTheta

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

example (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hBoutside : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) :=
  sinTheta_spectralSubspace_le N hA hB hδ hBoutside

/-- The hypothesis that was removed, on its own: it is a theorem, for every operator and
every set, with no side condition. -/
example (A : E →ₗ[𝕜] E) (Ω : Set ℝ) : SpectrumIn A (spectralSubspace A Ω) Ω :=
  spectrumIn_spectralSubspace A Ω

end SpectralSubspaceSinTheta

/-! ## Seam 2 — the finite-dimensional Frobenius chain closes

Four definitions, in four modules:

| object | module | topic |
| --- | --- | --- |
| `UnitarilyInvariantSeminorm.frobenius` | `InnerProductSpace/UnitarilyInvariantSeminorm.lean` | T05 |
| `RectangularUnitarilyInvariantSeminorm.frobenius` | `.../RectangularUnitarilyInvariantSeminorm/Instances.lean` | T07 |
| `RectangularUnitarilyInvariantSeminorm.schattenNorm 2` | `InnerProductSpace/SchattenNorm.lean` | T10 |
| `ContinuousLinearMap.hilbertSchmidtEnergy` | `InnerProductSpace/HilbertSchmidt/Energy.lean` | T10 |

The rectangular seminorm is the canonical reusable owner: the other three are identified
against it.  It is *not* the literal implementation owner — two Frobenius `def`s remain, and
the docstring of `frobenius_toSquare_eq` records exactly why removing one is blocked. -/

section Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Link 1: the square Frobenius seminorm is the square restriction of the rectangular one. -/
example :
    (RectangularUnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)).toSquare =
      UnitarilyInvariantSeminorm.frobenius 𝕜 E :=
  UnitarilyInvariantSeminorm.frobenius_toSquare_eq

/-- Link 2: the Schatten `S₂` norm is the rectangular Frobenius seminorm. -/
example (A : E →ₗ[𝕜] F) :
    RectangularUnitarilyInvariantSeminorm.schattenNorm
        (𝕜 := 𝕜) (E := E) (F := F) 2 (by norm_num) A =
      RectangularUnitarilyInvariantSeminorm.frobenius A :=
  RectangularUnitarilyInvariantSeminorm.schattenNorm_two_apply A

/-- Link 3: the Hilbert--Schmidt energy is the squared rectangular Frobenius seminorm. -/
example [CompleteSpace E] (A : E →L[𝕜] F) :
    A.hilbertSchmidtEnergy (stdOrthonormalBasis 𝕜 E).toHilbertBasis =
      ENNReal.ofReal (RectangularUnitarilyInvariantSeminorm.frobenius A.toLinearMap ^ 2) :=
  RectangularUnitarilyInvariantSeminorm.hilbertSchmidtEnergy_eq_ofReal_frobenius_sq A

/-- **The chain, composed.**  For a square operator the Hilbert--Schmidt energy is the square
of the *square* Frobenius seminorm.  Neither link 1 nor link 3 says this; only their
composite does, and this is the statement a consumer of the paper's `‖·‖²_F` vocabulary
actually needs. -/
example [CompleteSpace E] (A : E →L[𝕜] E) :
    A.hilbertSchmidtEnergy (stdOrthonormalBasis 𝕜 E).toHilbertBasis =
      ENNReal.ofReal (UnitarilyInvariantSeminorm.frobenius 𝕜 E A.toLinearMap ^ 2) := by
  rw [RectangularUnitarilyInvariantSeminorm.hilbertSchmidtEnergy_eq_ofReal_frobenius_sq,
    ← UnitarilyInvariantSeminorm.frobenius_toSquare_eq]
  rfl

/-- **The chain, composed the other way.**  The Schatten `S₂` norm of a square operator is
its square Frobenius seminorm — the statement that lets the operator-ideal topic (T10) and
the unitarily-invariant-norm topic (T05) be read as talking about the same norm. -/
example (A : E →ₗ[𝕜] E) :
    RectangularUnitarilyInvariantSeminorm.schattenNorm
        (𝕜 := 𝕜) (E := E) (F := E) 2 (by norm_num) A =
      UnitarilyInvariantSeminorm.frobenius 𝕜 E A := by
  rw [RectangularUnitarilyInvariantSeminorm.schattenNorm_two_apply,
    ← UnitarilyInvariantSeminorm.frobenius_toSquare_eq]
  rfl

end Frobenius

end RoadmapBridge.Integration
