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
# Sharp bounded `tan 2Theta` compatibility aggregate

The unrestricted bounded theorem was proved and promoted into
`DavisKahan.InfiniteDimensional.TanTwoTheta.PaperFaithfulUINorm`, inside the
production Davis--Kahan build. `FinishTanTwoTheta.DavisKahan.PaperFaithful` is now
a compatibility shim exposing the former namespace, while the retained finite
alternate derivation remains a regression route.

The separate unrestricted unbounded research target is intentionally not imported
here.
-/
