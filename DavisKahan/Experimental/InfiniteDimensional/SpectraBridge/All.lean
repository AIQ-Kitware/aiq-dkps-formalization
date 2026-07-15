/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.Basic
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.PVMSubspace
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.OperatorAbsoluteValue
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SinAngle
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotation
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationAPI
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationSquare

/-!
# Active shallow Spectra bridge

Only Spectra modules known to avoid the currently unported Stone and spectral
calculus import cone are exported here. The bounded spectral-projection bridge
is preserved under `dev/pending/` and can be reactivated after that dependency
cone is compatible with the root Lean/Mathlib revision.
-/
