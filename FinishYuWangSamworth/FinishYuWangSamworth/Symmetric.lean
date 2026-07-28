/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.GroundedImports

/-!
# Symmetric Yu--Wang--Samworth surface

The citation-critical symmetric results are already grounded in
`DavisKahan.Specialized.Statistics`:

* `yuWangSamworth_sinTheta_le` -- Theorem 2, including the Frobenius/operator
  minimum and the population-only gap;
* `yuWangSamworth_alignedBasis_le` -- the aligned-basis conclusion;
* `yuWangSamworth_eigenvector_le` -- the rank-one Corollary 3 surface.

This module is the stable home for source-shaped wrappers, endpoint
specializations, and any missing citation-facing corollaries discovered by the
forward-citation audit.
-/
