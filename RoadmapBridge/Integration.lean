/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Spectral
import ForTauCeti.Analysis.InnerProductSpace.SchattenNorm

/-!
# Roadmap bridge: cross-module integration seams

**What this file is for.** Each seam below joins declarations that live in *different*
`ForTauCeti` modules, and each is a place where the two sides can drift apart without any
single module failing to compile.  Every entry is an anonymous `example`, so it asserts
nothing and adds no public name: its only job is to stop elaborating if the seam moves.

The seams are not hypothetical.  All three are recorded regressions or review findings:

1. **A redundant hypothesis on a public signature.**  `sinTheta_pointSpectralSubspace_le` used to
   take an `hAselected` asserting spectral containment for the selected block;
   that premise follows from `Module.End.pointSpectrumIn_pointSpectralSubspace`.
   The parallel square-operator wrapper has since been removed in favor of
   Tau Ceti's accepted rectangular residual theorem. The example below keeps
   that theorem connected to canonical point-spectral selections.
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

/-! ## Seam 1 — the accepted rectangular theorem handles canonical selections

The accepted Tau Ceti result consumes a trial map into the ambient space and
states the residual bound in a rectangular unitarily invariant seminorm. This
example checks the canonical point-spectral selection directly, deriving its
spectral-containment hypothesis from the public restriction and point-spectrum
APIs rather than relying on a parallel square-operator wrapper. -/

section SpectralSubspaceSinTheta

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

example {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ}
    (hBoutside : Module.End.PointSpectrumIn B (Module.End.pointSpectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    let U := Module.End.pointSpectralSubspace A (Set.Icc a b)
    let V := Module.End.pointSpectralSubspace B (Set.Icc a b)
    let hU : IsInvariant A U := isInvariant_pointSpectralSubspace A (Set.Icc a b)
    let M := A.restrict hU
    let N : UnitarilyInvariantSeminorm 𝕜 U E :=
      UnitarilyInvariantSeminorm.kyFan (𝕜 := 𝕜) (E := U) (F := E) 1
    δ * N ((Vᗮ.starProjection ∘L U.subtypeₗᵢ.toContinuousLinearMap) : U →L[𝕜] E) ≤
      N (B.toContinuousLinearMap.sylvester M.toContinuousLinearMap
        U.subtypeₗᵢ.toContinuousLinearMap) := by
  let U := Module.End.pointSpectralSubspace A (Set.Icc a b)
  let V := Module.End.pointSpectralSubspace B (Set.Icc a b)
  have hU : IsInvariant A U := isInvariant_pointSpectralSubspace A (Set.Icc a b)
  let M := A.restrict hU
  have hM : M.IsSymmetric := hA.restrict_invariant hU
  have hMspec : Module.End.PointSpectrumIn (M : U →ₗ[𝕜] U) ⊤ (Set.Icc a b) :=
    (pointSpectrumIn_restrict_iff A hU (Set.Icc a b)).2
      (Module.End.pointSpectrumIn_pointSpectralSubspace A (Set.Icc a b))
  have hBspec : Module.End.PointSpectrumIn (B : E →ₗ[𝕜] E)
      (Module.End.pointSpectralSubspace B (Set.Icc a b)ᶜ)
      (Set.Ioo (a - δ) (b + δ))ᶜ := by
    rw [Module.End.pointSpectrumIn_iff]
    intro x hxV hx0 lam hxEig
    have hxV' : x ∈ Vᗮ := by
      rw [hB.orthogonal_pointSpectralSubspace (Set.Icc a b)]
      exact hxV
    change lam ∈ (Set.Ioo (a - δ) (b + δ))ᶜ
    exact (Module.End.pointSpectrumIn_iff.mp hBoutside) x hxV' hx0 lam hxEig
  exact UnitarilyInvariantSeminorm.mul_map_starProjection_orthogonal_pointSpectralSubspace_comp_le_map_sylvester_apply
    (N := UnitarilyInvariantSeminorm.kyFan (𝕜 := 𝕜) (E := U) (F := E) 1)
    (A := B.toContinuousLinearMap) (M := M.toContinuousLinearMap)
    (Ω := Set.Icc a b) hB hM hMspec hBspec U.subtypeₗᵢ.toContinuousLinearMap

/-- Canonical point-spectral subspaces provide their own spectral-containment input. -/
example (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    Module.End.PointSpectrumIn A (Module.End.pointSpectralSubspace A Ω) Ω :=
  Module.End.pointSpectrumIn_pointSpectralSubspace A Ω

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
