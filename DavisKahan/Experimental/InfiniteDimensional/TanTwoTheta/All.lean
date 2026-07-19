/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonal
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.Unbounded
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.UnboundedVector
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.UnboundedIdeal

/-!
# Experimental tangent-two-theta theory

This aggregate exposes the bounded quarter-acute conversion together with
unbounded operator-norm, per-vector, and ideal-gauge tangent-two-theta
specializations under an explicit quarter-acuteness hypothesis. The sharper
selected-Riccati form remains a separate obligation.
-/
