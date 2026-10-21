/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.Nuclear.Basic
public import ForTauCeti.Analysis.OperatorIdeal.Family.Basic

/-!
# DKPS trace-class family compatibility

Tau Ceti owns the nuclear gauge and its analytic laws. This module retains the DKPS
`traceClassIdealFamily` spelling for current consumers, with its gauge and completeness inherited
from the canonical nuclear norm. The family construction remains local because Tau Ceti's
`Family.TraceClass` import currently brings its `SymmetricGauge` into dependency closures that
still contain the local `ForTauCeti.Analysis.Normed.SymmetricGauge`. Remove this adapter after that
remaining gauge migration.
-/

public section

open scoped ENNReal

namespace TauCeti

universe u v

/-- **DKPS compatibility family** whose gauge is Tau Ceti's canonical nuclear norm. -/
@[expose]
noncomputable def traceClassIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := A.nuclearENorm
  gauge_add_le A B := A.nuclearENorm_add_le B
  gauge_smul c A := A.nuclearENorm_smul c
  enorm_le_gauge A := A.enorm_le_nuclearENorm
  gauge_comp_le L A R := L.nuclearENorm_comp_comp_le A R
  gauge_adjoint A := A.nuclearENorm_adjoint

/-- The compatibility family's gauge is Tau Ceti's nuclear norm. -/
@[simp] theorem gauge_traceClassIdealFamily {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (traceClassIdealFamily.{u, v} 𝕜).gauge A = A.nuclearENorm := rfl

/-- Tau Ceti's lower-semicontinuity theorem gives complete trace-class carriers. -/
instance isComplete_traceClassIdealFamily {𝕜 : Type u} [RCLike 𝕜] :
    (traceClassIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.IsComplete :=
  OperatorIdealFamily.isComplete_of_lowerSemicontinuous
    (Φ := (traceClassIdealFamily.{u, v} 𝕜).toOperatorIdealFamily)
    (fun _ _ _ _ _ _ _ _ => ContinuousLinearMap.lowerSemicontinuous_nuclearENorm)

end TauCeti
