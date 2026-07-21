/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.PVMSubspace
import Spectra.SpectralTheory.SpectralTheorem
import DavisKahan.Interop.Spectra.RealSpectralRestriction

/-!
# Canonical spectral-projection compatibility surface

The former scalar-generic `spectralResolution` facade predated the vendored
Spectra projection-valued measure and the real restriction bridge.  It has been
retired rather than duplicated.  Bounded complex self-adjoint projections are
provided by `boundedSelfAdjointSpectralProjection` and their ranges by
`boundedSelfAdjointSpectralSubspace`.  Real self-adjoint projections and ranges
are provided by `realSelfAdjointSpectralProjection` and
`realSelfAdjointSpectralSubspace`.

Contour identification with the bounded spectral projection is supplied by
`SpectralSeparatingContour.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection`.
The historical generic source is retained under `dev/`.
-/
