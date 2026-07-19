/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationContour
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationRieszIntegral
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationTransport
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationAssembly
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationRotationChain
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSpectralIdentification

/-!
# Concrete continuation infrastructure

This aggregate exposes the completed contour, Riesz-integral, transport,
assembly, rotation-chain, and spectral-identification leaves.  The older
`ContinuationRoadmap` scaffold is intentionally not part of this aggregate.
-/
