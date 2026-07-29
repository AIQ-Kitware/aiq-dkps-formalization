/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import FinishTanTwoTheta.Sequence.WeakSubmajorization
import FinishTanTwoTheta.Sequence.MinimalCompletion
import FinishTanTwoTheta.OperatorIdeal.StandardFanDominance
import FinishTanTwoTheta.OperatorIdeal.StandardInstances
import FinishTanTwoTheta.ApproximationNumber.SpectralSelection
import FinishTanTwoTheta.FunctionalCalculus.DoubleAngleTangent
import FinishTanTwoTheta.DavisKahan.StableRiccatiPair
import FinishTanTwoTheta.DavisKahan.SharpKyFan
import FinishTanTwoTheta.DavisKahan.SharpIdeal
import DavisKahan.Sources.DavisKahan1970.Audits.DoubleAngleTangent

/-!
# Sharp `tan 2Theta`: actual completed proof stack

This aggregate imports the substantive bounded infinite-dimensional proof:
approximation-number selection, the canonical double-angle tangent functional
calculus, the stable Riccati estimate, the sharp Ky Fan inequality, and Fan
promotion to maximal and minimal standard symmetric ideals.

It also imports the focused source audit for the finite-dimensional Section 7
unitarily invariant norm theorem and the arbitrary-space sharp operator-norm
branch theorem.

`FinishTanTwoTheta.DavisKahan.Unbounded` is intentionally not imported here.
Its proposed unrestricted unbounded ideal extension depends on a spectral-band
selection statement whose proof route is refuted.  The module remains available
as an explicit research target; excluding it does not weaken any theorem proved
by the imports above or any source theorem recorded by the audit.
-/
