/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.InfiniteDimensional.Sylvester.Basic
public import DavisKahan.DoubleAngle.CompatibilitySinTwoTheta
public import DavisKahan.SpectralTheory.GraphSubspace
public import DavisKahan.InfiniteDimensional.SinTheta.Continuation

/-!
# Infinite-dimensional mathematics pass

Aggregate entry point for the bounded Sylvester, graph-subspace, double-angle
compatibility, ideal, and continuation work prepared in the July 2026
mathematics pass.  Its whole closure became admission-free, so the tree moved
out of `Experimental/` and `DavisKahan.All` reaches this aggregate through
`DavisKahan/InfiniteDimensional/Sylvester/All.lean`.
-/
