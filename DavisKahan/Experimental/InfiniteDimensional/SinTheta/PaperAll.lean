/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.NormCorrespondence
import DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances
import DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
import DavisKahan.Sources.DavisKahan1970.SineTheta.AngleIdentity
import DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngle
import DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngleReal
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCommonDomainTheorems
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCommonCoreTheorems
import DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperSharpness

/-!
# Complete source-faithful sine-theta layer for Davis--Kahan 1970

This aggregate contains the exact Section 6 norm class, literal operator-angle
objects, Lemmas 6.1 and 6.2, the original and generalized sine theorems,
Proposition 6.1, Theorem 6.2, the unbounded common-domain forms, the finite-rank
bound-norm fallback, and sharpness/counterexample models.

It is intentionally separate from the already accepted general sine-theta
aggregate until every declaration in this exact-paper layer has passed the
compiler and dependency audit.
-/
