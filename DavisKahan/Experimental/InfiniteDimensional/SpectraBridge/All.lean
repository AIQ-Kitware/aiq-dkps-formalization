/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.Basic
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.ClosedOperator
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.PVMSubspace
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SpectralRestriction
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.OperatorAbsoluteValue
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.ApproximationNumberMinMax
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SinAngle
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotation
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationAPI
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationSquare
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.GapResolvent
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.BoundedFromSpectrum
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.UnboundedIntervalExterior
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.BoundedPerturbationSinTheta

/-!
# Active Spectra bridge

The Stone/spectral-calculus import cone of the Spectra library builds against
the root Lean/Mathlib revision as of 2026-07-16, so the bridge now includes
the spectral-theorem-backed gap-resolvent module alongside the shallow
adapters. The bounded spectral-projection bridge preserved under
`dev/pending/` remains available for reactivation.
-/
