/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ContinuationContour
import DavisKahan.SpectralTheory.ContinuationRieszIntegral
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.Transport
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.Assembly
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.RotationChain
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.SpectralIdentification
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.SelectedSubspace
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.SelectedBranch
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.QuarterAcute
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.SelectedGraph
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.WitnessGraph
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.WitnessRiccati
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.WitnessOffDiagonal

/-!
# Concrete continuation infrastructure

This aggregate exposes the completed contour, Riesz-integral, transport,
assembly, rotation-chain, spectral-identification, selected-subspace transport,
selected-branch, quantitative quarter-acuteness, selected-graph, selected-reduction,
witness-native canonical graph, selected Riccati-coordinate, and off-diagonal block leaves.
The older
`ContinuationRoadmap` scaffold is intentionally not part of this aggregate.
-/
