/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 Astra Pro
-/
import DavisKahan.Sources.DavisKahan1970.Section4
import DavisKahan.FiniteDimensional.DirectRotation.SmallAngleCounterexample

/-!
# Small-angle strengthening of the Proposition 4.4 refutation

This extension is a separate import from the existing Section 4 source census.
The original 29-target inventory and fixed-angle refutation are unchanged.
The declarations expose the parameterized real four-dimensional construction
and its consequence that no positive angle threshold restores the printed claim.
-/

namespace TauCeti.DavisKahan1970

/-- At every acute positive angle, an orthogonal competitor has smaller trace-norm
full displacement than the canonical direct rotation of its source and target. -/
alias proposition4_4_parameterized_traceNorm_counterexample :=
  DavisKahan.FiniteDimensional.SmallAngleCounterexample.kyFanSum_lt

/-- Both principal angles of the parameterized pair equal the parameter. -/
alias proposition4_4_parameterized_principalAngles :=
  DavisKahan.FiniteDimensional.SmallAngleCounterexample.principalAngles_eq

/-- No positive principal-angle threshold repairs Proposition 4.4. -/
alias proposition4_4_arbitrarilySmall_refutingPair :=
  DavisKahan.FiniteDimensional.arbitrarilySmall_fullDisplacement_refuted

end TauCeti.DavisKahan1970
