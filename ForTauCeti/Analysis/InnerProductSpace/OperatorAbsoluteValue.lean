/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

TRANSITIONAL COMPATIBILITY SHIM — NOT an upstream candidate.

The signature-polish backlog (`dev/tauceti-signature-polish-todo.md` §7)
requires a single modulus API: two public definitions of `(T⋆ T)^(1/2)` — one
rectangular, one square — would be blocked on the reuse rubric.  The canonical
definition is now `ContinuousLinearMap.modulus` in
`ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`, stated for
rectangular operators; the square case is a specialization of it.

`operatorAbs` survives here only as a reducible alias with its historical API
restated, so that the Davis--Kahan consumers keep compiling while they migrate.
Delete each declaration once its downstream users have moved to the canonical
name (see the name map in
`dev/tauceti/formathlib-to-fortauceti-migration.md`).  Nothing in this file may
be exported to Tau Ceti.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Historical name for the endomorphism case of
`ContinuousLinearMap.modulus`. -/
noncomputable abbrev operatorAbs (T : E →L[ℂ] E) : E →L[ℂ] E := T.modulus

/-- Historical name for `ContinuousLinearMap.modulus_nonneg`. -/
theorem operatorAbs_nonneg (T : E →L[ℂ] E) : 0 ≤ operatorAbs T :=
  T.modulus_nonneg

/-- Historical name for `ContinuousLinearMap.modulus_isSelfAdjoint`. -/
theorem isSelfAdjoint_operatorAbs (T : E →L[ℂ] E) :
    IsSelfAdjoint (operatorAbs T) :=
  T.modulus_isSelfAdjoint

/-- Historical name for
`ContinuousLinearMap.modulus_mul_self_eq_star_mul_self`. -/
theorem operatorAbs_mul_self (T : E →L[ℂ] E) :
    operatorAbs T * operatorAbs T = star T * T :=
  T.modulus_mul_self_eq_star_mul_self

/-- Historical name for
`ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq`. -/
theorem operatorAbs_unique {T b : E →L[ℂ] E} (hb : 0 ≤ b)
    (h : b * b = star T * T) : b = operatorAbs T :=
  ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq hb h

/-- Historical name for `ContinuousLinearMap.modulus_commute_modulus`. -/
theorem operatorAbs_commute_operatorAbs {S T : E →L[ℂ] E}
    (h : Commute (star S * S) (star T * T)) :
    Commute (operatorAbs S) (operatorAbs T) :=
  ContinuousLinearMap.modulus_commute_modulus h

/-- Historical name for `ContinuousLinearMap.norm_modulus`. -/
theorem norm_operatorAbs (T : E →L[ℂ] E) : ‖operatorAbs T‖ = ‖T‖ :=
  T.norm_modulus

/-- Historical name for `ContinuousLinearMap.norm_modulus_comp`. -/
theorem norm_operatorAbs_mul (S D : E →L[ℂ] E) :
    ‖operatorAbs S * D‖ = ‖S * D‖ :=
  S.norm_modulus_comp D

/-- Historical name for `ContinuousLinearMap.norm_comp_modulus`. -/
theorem norm_mul_operatorAbs (D T : E →L[ℂ] E) :
    ‖D * operatorAbs T‖ = ‖D * star T‖ :=
  D.norm_comp_modulus T

/-- Historical name for `ContinuousLinearMap.norm_modulus_apply`. -/
theorem norm_operatorAbs_apply (T : E →L[ℂ] E) (x : E) :
    ‖operatorAbs T x‖ = ‖T x‖ :=
  T.norm_modulus_apply x

end TauCeti

end
