/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.Majorization.WeakSubmajorization
import DavisKahan.Sources.DavisKahan1970.Ideals.SequenceGauge
import DavisKahan.Sources.DavisKahan1970.Ideals.StandardFanDominance
import DavisKahan.Sources.DavisKahan1970.Ideals.StandardInstances
import DavisKahan.Sources.DavisKahan1970.Ideals.SpectralSelection
import DavisKahan.Sources.DavisKahan1970.DoubleAngleTangentOperator
import DavisKahan.Sources.DavisKahan1970.StableRiccatiPair
import DavisKahan.Sources.DavisKahan1970.SharpKyFan
import DavisKahan.Sources.DavisKahan1970.SharpIdeal
import FinishTanTwoTheta.DavisKahan.PaperFaithful
import DavisKahan.Sources.DavisKahan1970.Audits.DoubleAngleTangent

/-!
# Sharp bounded `tan 2Theta`

The aggregate imports the approximation-number/Riccati/Fan-dominance core, the
retained duplicate finite regression proof, and the exact unrestricted bounded
paper-facing proof attempt.

The unrestricted declaration `paperFaithful_tanTwoTheta_uiNorm` has no finite
carrier, derives the quarter-acute branch, and concludes the source-ideal bound
for the canonical ambient tangent.  Its two new bridges are implemented in
`InfiniteQuarterAcute` and `CanonicalTangentBridge` and contain no admission.
This source state is ready for compiler review; it is not called compiled or
axiom-clean until the aggregate and the final axiom audit pass.

The separate unrestricted unbounded research target is intentionally not
imported here.
-/
