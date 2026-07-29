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
import FinishTanTwoTheta.DavisKahan.PaperFaithful
import DavisKahan.Sources.DavisKahan1970.Audits.DoubleAngleTangent

/-!
# Sharp `tan 2Theta`: proved core and paper-faithful target

This aggregate imports the substantive bounded infinite-dimensional Riccati
proof: approximation-number selection, the canonical double-angle tangent
functional calculus, the stable Riccati estimate, the sharp Ky Fan inequality,
and Fan promotion to maximal and minimal standard symmetric ideals.

It also imports the focused source audit and the explicitly admitted
`paperFaithful_tanTwoTheta_uiNorm` target.  The admitted theorem records the
missing source-shaped endpoint: branch selection and the arbitrary-Hilbert-space
unitary-invariant-norm estimate from the original off-diagonal perturbation and
reducing-subspace hypotheses.  Consequently, a green build of this aggregate is
not an axiom-clean claim that the paper theorem has been proved.

`FinishTanTwoTheta.DavisKahan.Unbounded` is intentionally not imported here.
Its proposed unrestricted unbounded ideal extension depends on a spectral-band
selection statement whose proof route is refuted.  The module remains available
as an explicit research target; excluding it does not weaken any theorem proved
by the imports above or any source theorem recorded by the audit.
-/
