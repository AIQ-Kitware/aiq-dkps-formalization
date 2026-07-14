/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Basic
import Mathlib.Topology.Basic

/-!
# Rectangular symmetric ideal families for the exact `sin Θ` program

The original Davis--Kahan theorem compares operators between different Hilbert
spaces.  A square endomorphism norm is therefore not a sufficient abstraction.
This module records one coherent norm-ideal family across all source and target
spaces in a fixed universe.

The fields are intentionally explicit.  A concrete instance must provide
membership, the gauge, adjoint invariance, two-sided ideal control, and
completeness.  The bounded and one-unbounded interval/exterior theory uses
only this interface.  The genuinely two-unbounded cutoff route uses the
stronger `KyFanDominantIdealFamily` defined in `ApproximationNumbers.lean`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

/-- A coherent rectangular symmetric norm ideal over Hilbert spaces in one
universe.  `Mem` records finite ideal norm; `gauge` is only used on members. -/
structure RectangularSymmetricIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  Mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → Prop
  gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ
  zero_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      Mem (0 : E →L[𝕜] F)
  add_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F}, Mem A → Mem B → Mem (A + B)
  smul_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) {A : E →L[𝕜] F}, Mem A → Mem (c • A)
  adjoint_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → Mem A.adjoint
  comp_mem :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E),
      Mem A → Mem (L ∘L A ∘L R)
  gauge_nonneg :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → 0 ≤ gauge A
  gauge_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      gauge (0 : E →L[𝕜] F) = 0
  gauge_eq_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → gauge A = 0 → A = 0
  gauge_add_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F}, Mem A → Mem B →
        gauge (A + B) ≤ gauge A + gauge B
  gauge_smul :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) {A : E →L[𝕜] F}, Mem A →
        gauge (c • A) = ‖c‖ * gauge A
  gauge_adjoint :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → gauge A.adjoint = gauge A
  gauge_comp_le :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E),
      Mem A → gauge (L ∘L A ∘L R) ≤ ‖L‖ * gauge A * ‖R‖
  opNorm_le_gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → ‖A‖ ≤ gauge A
  gauge_complete :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : ℕ → E →L[𝕜] F),
      (∀ n, Mem (A n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
        gauge (A m - A n) < ε) →
      ∃ L, Mem L ∧ ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        gauge (A n - L) < ε

namespace RectangularSymmetricIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The ordinary operator norm as a coherent rectangular family. -/
noncomputable def operatorNorm : RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Compact operators equipped with the ordinary operator norm. -/
noncomputable def compactOperatorNorm :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Hilbert--Schmidt operators as a coherent rectangular family. -/
noncomputable def hilbertSchmidt :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Trace-class operators as a coherent rectangular family. -/
noncomputable def traceClass :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Schatten `p` operators as a coherent rectangular family. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Ky Fan `k` gauges, with positive `k`. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

end RectangularSymmetricIdealFamily

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
