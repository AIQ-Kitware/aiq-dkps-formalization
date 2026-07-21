/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.All
import DavisKahan.Geometry.Angle.OperatorAngleComplex
import DavisKahan.Geometry.Angle.OperatorAngleReal
import DavisKahan.Geometry.Angle.PaperOperatorAngle
import DavisKahan.Interop.Spectra.RealSpectralRestriction
import DavisKahan.TanTwoTheta.All
import DavisKahan.DoubleAngle.Unbounded
import DavisKahan.DoubleAngle.UnboundedIdeal

/-!
# Canonical infinite-dimensional Davis--Kahan integration

The active infinite-dimensional route is the compiler-clean production and
vendored-Spectra development imported above.  The older duplicate ambient
facades remain in the source tree for historical reference but are no longer
part of the executable Experimental aggregate.
-/
