/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import DavisKahan.InfiniteDimensional.TanTwoTheta.CanonicalTangentBridge

/-!
# Canonical ambient tangent versus graph tangent (promoted; this is now a shim)

The proof moved verbatim to
`DavisKahan.InfiniteDimensional.TanTwoTheta.CanonicalTangentBridge`, inside the
default build.  Only the namespace changed, from
`TauCeti.DavisKahan.FinishTanTwoTheta` to `TauCeti.DavisKahan`.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

/-- Promoted to
`TauCeti.DavisKahan.canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate`. -/
alias canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate :=
  TauCeti.DavisKahan.canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate

end FinishTanTwoTheta
end DavisKahan
end TauCeti
