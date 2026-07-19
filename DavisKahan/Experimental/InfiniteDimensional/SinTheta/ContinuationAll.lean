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
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSelectedSubspace
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSelectedBranch
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationQuarterAcute
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSelectedGraph
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationWitnessGraph
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationWitnessRiccati

/-!
# Concrete continuation infrastructure

This aggregate exposes the completed contour, Riesz-integral, transport,
assembly, rotation-chain, spectral-identification, selected-subspace transport,
selected-branch, quantitative quarter-acuteness, selected-graph, selected-reduction,
witness-native canonical graph, and selected Riccati-coordinate leaves.
The older
`ContinuationRoadmap` scaffold is intentionally not part of this aggregate.
-/
