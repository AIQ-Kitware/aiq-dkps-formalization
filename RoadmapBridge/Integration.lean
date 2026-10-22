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

1. **A redundant hypothesis on a public signature.**  `sinTheta_pointSpectralSubspace_le` used to
   take an `hAselected` asserting spectral containment for the selected block
   `Module.End.pointSpectralSubspace A (Set.Icc a b)`. That fact holds without
   an additional hypothesis, and
   is now proved once, as `pointSpectrumIn_pointSpectralSubspace`.  Nothing prevents a future edit
   from
   re-adding the argument, and the library would still build; the example below would not.
2. **One rectangular seminorm interface.** The examples exercise the inherited `Seminorm`
   laws, independent domain and codomain unitaries, Fan dominance in both directions, and
   the square specialization. They identify the single Frobenius construction with the
   Schatten `S2` norm and finite Hilbert--Schmidt energy.
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
open scoped BigOperators

/-! ## Seam 1 — the spectral subspace supplies its own spectral-containment hypothesis

`pointSpectrumIn_pointSpectralSubspace` is the theorem that made the `hAselected` argument
redundant.
The example restates the sin-Θ bound with *only* the exterior hypothesis about `B`; if
`hAselected` ever returns to the signature, this stops elaborating. -/

section SpectralSubspaceSinTheta

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

example (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hBoutside : PointSpectrumIn B (Module.End.pointSpectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap (Module.End.pointSpectralSubspace A (Set.Icc a b))
        (Module.End.pointSpectralSubspace B (Set.Icc a b))) ≤ N (B - A) :=
  sinTheta_pointSpectralSubspace_le N hA hB hδ hBoutside

/-- The hypothesis that was removed, on its own: it is a theorem, for every operator and
every set, with no side condition. -/
example (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    PointSpectrumIn A (Module.End.pointSpectralSubspace A Ω) Ω :=
  pointSpectrumIn_pointSpectralSubspace A Ω

end SpectralSubspaceSinTheta

/-! ## The unified finite-dimensional norm interface -/

section UnifiedUIN

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

example (N : UnitarilyInvariantSeminorm 𝕜 E F) : Seminorm 𝕜 (E →ₗ[𝕜] F) :=
  N.toSeminorm

example (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E →ₗ[𝕜] F) :
    N.toSeminorm A = N A := rfl

example (N : UnitarilyInvariantSeminorm 𝕜 E F) : N 0 = 0 :=
  map_zero N

example (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E →ₗ[𝕜] F) :
    N (-A) = N A := map_neg_eq_map N A

example (N : UnitarilyInvariantSeminorm 𝕜 E F) (A B : E →ₗ[𝕜] F) :
    N (A + B) ≤ N A + N B := map_add_le_add N A B

example (N : UnitarilyInvariantSeminorm 𝕜 E F) (a : 𝕜)
    (A : E →ₗ[𝕜] F) : N (a • A) = ‖a‖ * N A :=
  map_smul_eq_mul N a A

example (k : ℕ) (A B : E →ₗ[𝕜] F) :
    (A + B).kyFanSum k ≤ A.kyFanSum k + B.kyFanSum k :=
  LinearMap.kyFanSum_add_le A B k

example (N : UnitarilyInvariantSeminorm 𝕜 E F)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) :
    N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = N A :=
  N.map_linearIsometryEquiv_comp_comp U V A

example {A B : E →ₗ[𝕜] F} :
    (∀ k, A.kyFanSum k ≤ B.kyFanSum k) →
      ∀ N : UnitarilyInvariantSeminorm 𝕜 E F, N A ≤ N B := by
  intro h N
  exact N.map_le_of_kyFanSum_le h

example (N : UnitarilyInvariantSeminorm 𝕜 E E) (A : E →ₗ[𝕜] E) :
    N (operatorAbs A) = N A := N.apply_operatorAbs A

noncomputable example : UnitarilyInvariantSeminorm 𝕜 E E :=
  UnitarilyInvariantSeminorm.frobenius 𝕜 E E

example {n : ℕ} (A : E →ₗ[𝕜] F) (hn : Module.finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := F) A =
      Real.sqrt (∑ i, ‖A (b i)‖ ^ 2) := by
  simpa [hn] using UnitarilyInvariantSeminorm.frobenius_apply b A

example (A : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.kyFan (𝕜 := 𝕜) (E := E) (F := F) 0 A = 0 := by
  simp [UnitarilyInvariantSeminorm.kyFan_apply, LinearMap.kyFanSum_def]

example : UnitarilyInvariantSeminorm.schatten 𝕜 E F 2 =
    UnitarilyInvariantSeminorm.frobenius 𝕜 E F :=
  UnitarilyInvariantSeminorm.schatten_two

example [CompleteSpace E] (A : E →L[𝕜] F) :
    A.hilbertSchmidtEnergy (stdOrthonormalBasis 𝕜 E).toHilbertBasis =
      ENNReal.ofReal (UnitarilyInvariantSeminorm.frobenius
        (𝕜 := 𝕜) (E := E) (F := F) A.toLinearMap ^ 2) :=
  UnitarilyInvariantSeminorm.hilbertSchmidtEnergy_eq_ofReal_frobenius_sq A

end UnifiedUIN

end RoadmapBridge.Integration
