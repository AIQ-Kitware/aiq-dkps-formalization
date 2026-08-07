/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import DavisKahan.InfiniteDimensional.TanTwoTheta.PaperFaithfulUINorm

/-!
# Full bounded paper-facing `tan 2Theta` (promoted; this module is now a shim)

`paperFaithful_tanTwoTheta_uiNorm` and the finite regression proof moved
verbatim to `DavisKahan.InfiniteDimensional.TanTwoTheta.PaperFaithfulUINorm`,
inside the default build.  Only the namespace changed, from
`TauCeti.DavisKahan.FinishTanTwoTheta` to `TauCeti.DavisKahan`.

The reason for the move is the failure mode this lane's own
`PROOF_OBLIGATIONS.md` records: results proved here are unguarded, and a
refactor elsewhere can break them while every default gate stays green.  That
happened once already, on 2026-07-30.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

/-- Promoted to `TauCeti.DavisKahan.paperTanTwoThetaRepresentative`. -/
alias paperTanTwoThetaRepresentative := TauCeti.DavisKahan.paperTanTwoThetaRepresentative

/-- Promoted to `TauCeti.DavisKahan.paperTanTwoTheta_uiNorm_finite_alternate`. -/
alias paperTanTwoTheta_uiNorm_finite_alternate :=
  TauCeti.DavisKahan.paperTanTwoTheta_uiNorm_finite_alternate

/-- Promoted to `TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm`. -/
alias paperFaithful_tanTwoTheta_uiNorm :=
  TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm

end FinishTanTwoTheta
end DavisKahan
end TauCeti
