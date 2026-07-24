/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import DavisKahan.Experimental.Frontier.Section3
import DavisKahan.Experimental.Frontier.Section4
import DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakage
import DavisKahan.Experimental.Frontier.RieszCircle
import DavisKahan.Sources.DavisKahan1970.RemainingSourceSurface
-- Section8 and Section9Analytic are TEMPORARILY out of the aggregate.  The four
-- modules that originally blocked them (Ideals.Symmetric,
-- Core.CompatibilitySinTwoTheta, Sylvester.Resolvent, GraphSubspace) now
-- elaborate; the remaining blocker is
-- `DavisKahan.Experimental.InfiniteDimensional.Sylvester.Basic`, which needs an
-- operator-semigroup / Bochner-integral Sylvester reconstruction (unitaryGroup,
-- semigroup, separatedSylvesterMultiplier, orderedSylvester_reconstruction, ...)
-- that is a genuine missing development, not a rename.  Restore both imports
-- once Sylvester.Basic elaborates.
-- import DavisKahan.Experimental.Frontier.Section8
-- import DavisKahan.Experimental.Frontier.Section9Analytic

/-! # Experimental full-paper frontier aggregate -/
