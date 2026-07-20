/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.Basic
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.Interop.Spectra.PVMSubspace
import DavisKahan.Interop.Spectra.SpectralRestriction
import DavisKahan.Interop.Spectra.SpectralRestrictionOperator
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.RealSpectralRestriction
import DavisKahan.Interop.Spectra.SpectralRestrictionLocalization
import DavisKahan.Interop.Spectra.OperatorAbsoluteValue
import DavisKahan.Interop.Spectra.ApproximationNumberMinMax
import DavisKahan.Interop.Spectra.SinAngle
import DavisKahan.Interop.Spectra.DirectRotation
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationAPI
import DavisKahan.Interop.Spectra.DirectRotationSquare
import DavisKahan.Interop.Spectra.GapResolvent
import DavisKahan.Interop.Spectra.BoundedFromSpectrum
import DavisKahan.Sylvester.Unbounded.IntervalExterior
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.BoundedPerturbationSinTheta
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SpectralProjectionSinTheta

/-!
# Active Spectra bridge

The Stone/spectral-calculus import cone of the Spectra library builds against
the root Lean/Mathlib revision as of 2026-07-16, so the bridge now includes
the spectral-theorem-backed gap-resolvent module alongside the shallow
adapters. The bounded spectral-projection bridge preserved under
`dev/pending/` remains available for reactivation.
-/
