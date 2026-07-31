/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.MathlibBridge
import ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Subspace
import DavisKahan.SpectralTheory.SpectralRestriction
import DavisKahan.SpectralTheory.SpectralRestrictionOperator
import DavisKahan.SpectralTheory.Real.SpectralRestriction
import DavisKahan.SpectralTheory.SpectralRestrictionLocalization
import DavisKahan.Geometry.Polar.OperatorAbsoluteValue
import DavisKahan.Geometry.Angle.SinAngle
import DavisKahan.Geometry.Polar.DirectRotation
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationAPI
import DavisKahan.Geometry.Polar.DirectRotationSquare
import DavisKahan.SpectralTheory.GapResolvent
import DavisKahan.SpectralTheory.BoundedFromSpectrum
import DavisKahan.Sylvester.Unbounded.IntervalExterior
import DavisKahan.SinTheta.BoundedPerturbation
import DavisKahan.SinTheta.SpectralProjection

/-!
# Active Spectra bridge

The Stone/spectral-calculus import cone of the Spectra library builds against
the root Lean/Mathlib revision as of 2026-07-16, so the bridge now includes
the spectral-theorem-backed gap-resolvent module alongside the shallow
adapters. The bounded spectral-projection bridge preserved under
`dev/pending/` remains available for reactivation.
-/
