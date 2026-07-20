/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.ApproximationNumberMinMax
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.Interop.Spectra.RealSpectrumBridge
import DavisKahan.Interop.Spectra.SpectralRestriction
import DavisKahan.Interop.Spectra.SpectralRestrictionOperator
import DavisKahan.Interop.Spectra.UnitaryConjugation
import DavisKahan.Interop.Spectra.Basic
import DavisKahan.Interop.Spectra.DirectRotation
import DavisKahan.Interop.Spectra.DirectRotationSquare
import DavisKahan.Interop.Spectra.HalmosTwoProjections
import DavisKahan.Interop.Spectra.OperatorAbsoluteValue
import DavisKahan.Interop.Spectra.PVMSubspace
import DavisKahan.Interop.Spectra.SinAngle
import DavisKahan.Interop.Spectra.OrderedHalfLine
import DavisKahan.Interop.Spectra.SpectralRestrictionLocalization

/-!
# Spectra interoperability layer

Representation machinery obtained from the vendored Spectra package, restated
for Davis--Kahan use.  The dependency direction is strict: Mathlib, then
`ForMathlib`, then vendored Spectra, then this layer, then Davis--Kahan theory.
-/
