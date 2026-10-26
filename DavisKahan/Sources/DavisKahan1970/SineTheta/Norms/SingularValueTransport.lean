/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
public import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Complete singular-value transport for the paper-facing sine operators

Davis--Kahan Theorem 6.1 permits `sin Θ₀` to be any operator with the same
complete singular-value sequence as the canonical cross-projection block.
In infinite dimensions the zero-based approximation numbers are the stable
replacement for the finite singular-value list. This module proves that equal
approximation-number sequences give exactly the same membership and gauge in
every Ky-Fan-dominant unitarily invariant ideal family.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u vE vF vE1 vF1 vE2 vF2 vE3 vF3 vE0 vF0 vS

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type vE} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace SameApproximationSingularValues

section IdealGauge

/-! ### Gauge transport

A a native symmetric ideal family with Ky Fan dominance assigns a gauge to rectangular operators
between Hilbert spaces drawn from a *single* universe: that is how a family
closed under adjoints has to quantify its fields, and it is not an incidental
restriction.  A two-universe variant would be a strictly weaker
object, since a family built for the pair `(v, v)` would no longer apply to the
pair `(v, w)`; there is no single Lean structure carrying one gauge for all
universe pairs at once.

So the results below are stated for a shared universe, which is their natural
generality, while `ContinuousLinearMap.SameSingularValues` and
`SinThetaRepresentativeAcross` above remain genuinely cross-universe:
those are exactly the statements that do not mention a gauge. -/

variable {G H : Type vS}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Transport ideal membership and exact gauge equality along complete
singular-value equality. -/
theorem mem_and_gauge_eq
    (N : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {A B : G →L[𝕜] H}
    (h : ContinuousLinearMap.SameSingularValues A B)
    (hB : N.Mem B) :
    N.Mem A ∧
      N.gaugeReal A =
        N.gaugeReal B := by
  have hraw : N.gauge A =
      N.gauge B :=
    OperatorIdealFamily.gauge_eq_of_sameSingularValues
      (Φ := N.toOperatorIdealFamily) h
  have hA : N.Mem A := by
    change N.gauge A ≠ ⊤
    rw [hraw]
    exact hB
  exact ⟨hA, congrArg ENNReal.toReal hraw⟩

/-- Transfer a sharp scalar gauge estimate to any operator with the same
complete singular-value sequence. -/
theorem mem_and_mul_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {A B C : G →L[𝕜] H} {c : ℝ}
    (h : ContinuousLinearMap.SameSingularValues A B)
    (hB : N.Mem B)
    (hbound : c * N.gaugeReal B ≤
      N.gaugeReal C) :
    N.Mem A ∧
      c * N.gaugeReal A ≤
        N.gaugeReal C := by
  obtain ⟨hA, hgauge⟩ := mem_and_gauge_eq N h hB
  refine ⟨hA, ?_⟩
  rw [hgauge]
  exact hbound

end IdealGauge

end SameApproximationSingularValues

/-- Literal source packaging of the freedom in `sin Theta_0`.  The chosen
representative may act between different Hilbert coordinate spaces, exactly as
in the paper; only its complete singular-value sequence is prescribed. -/
structure SinThetaRepresentativeAcross
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    (canonical : E →L[𝕜] F) where
  operator : E₀ →L[𝕜] F₀
  same_singular_sequence :
    ContinuousLinearMap.SameSingularValues operator canonical

namespace SinThetaRepresentativeAcross

/-- The canonical operator is an admissible representative. -/
@[expose]
noncomputable def canonical (A : E →L[𝕜] F) :
    SinThetaRepresentativeAcross (E₀ := E) (F₀ := F) A where
  operator := A
  same_singular_sequence := ContinuousLinearMap.sameSingularValues_refl A

end SinThetaRepresentativeAcross

/-- Paper-facing packaging of the freedom in the definition of `sin Θ₀`:
the chosen operator has exactly the complete singular-value sequence of the
canonical directed sine block. -/
structure SinThetaRepresentative (canonical : E →L[𝕜] F) where
  operator : E →L[𝕜] F
  same_singular_values : ContinuousLinearMap.SameSingularValues operator canonical

namespace SinThetaRepresentative

/-- The canonical block is itself an admissible paper representative. -/
@[expose]
noncomputable def canonical (A : E →L[𝕜] F) :
    SinThetaRepresentative A where
  operator := A
  same_singular_values := ContinuousLinearMap.sameSingularValues_refl A

/-- Every paper representative has exactly the same ideal membership and
gauge as the canonical block.

Stated for a shared universe, for the reason recorded in the gauge-transport
section above: an ideal-family gauge is defined on operators drawn from one
universe. -/
theorem mem_and_gauge_eq
    {G H : Type vS}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {canonical : G →L[𝕜] H}
    (S : SinThetaRepresentative canonical)
    (hcanonical : N.Mem canonical) :
    N.Mem S.operator ∧
      N.gaugeReal S.operator =
        N.gaugeReal canonical :=
  SameApproximationSingularValues.mem_and_gauge_eq N S.same_singular_values hcanonical

end SinThetaRepresentative

end ExactSinTheta
end DavisKahan
end TauCeti
