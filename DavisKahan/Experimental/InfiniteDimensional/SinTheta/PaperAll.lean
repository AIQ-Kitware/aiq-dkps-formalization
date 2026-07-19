/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperNormCorrespondence
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCosineAngle
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperFullAngle
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperFullAngleReal
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCommonDomainTheorems
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperSymmetric
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
