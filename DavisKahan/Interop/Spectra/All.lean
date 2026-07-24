/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.ApproximationNumberMinMax
import DavisKahan.Interop.Spectra.BoundedSelfAdjointSpectralProjection
import DavisKahan.Interop.Spectra.Basic
import DavisKahan.Interop.Spectra.BoundedFromSpectrum
import DavisKahan.Interop.Spectra.BoundedPerturbationSinTheta
import DavisKahan.Interop.Spectra.BoundedPerturbationSinThetaIdeal
import DavisKahan.Interop.Spectra.BoundedTruncation
import DavisKahan.Interop.Spectra.CircleRieszProjection
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.Interop.Spectra.DirectRotation
import DavisKahan.Interop.Spectra.DirectRotationSquare
import DavisKahan.Interop.Spectra.GapResolvent
import DavisKahan.Interop.Spectra.HalmosTwoProjections
import DavisKahan.Interop.Spectra.OperatorAbsoluteValue
import DavisKahan.Interop.Spectra.OrderedHalfLine
import DavisKahan.Interop.Spectra.PVMSubspace
import DavisKahan.Interop.Spectra.RealSpectralRestriction
import DavisKahan.Interop.Spectra.RealSpectrumBridge
import DavisKahan.Interop.Spectra.ReflectionRestriction
import DavisKahan.Interop.Spectra.SinAngle
import DavisKahan.Interop.Spectra.SpectralCutoff
import DavisKahan.Interop.Spectra.SpectralProjectionSinTheta
import DavisKahan.Interop.Spectra.SpectralRestriction
import DavisKahan.Interop.Spectra.SpectralRestrictionLocalization
import DavisKahan.Interop.Spectra.SpectralRestrictionOperator
import DavisKahan.Interop.Spectra.UnitaryConjugation

/-! # `DavisKahan/Interop/Spectra` -/
