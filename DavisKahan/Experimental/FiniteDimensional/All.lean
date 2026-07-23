/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.SinTheta

/-! # Experimental finite-dimensional Davis--Kahan extensions

Everything else that used to live here was promoted into
`DavisKahan/FiniteDimensional`: the angle operators, rectangular norms,
residual angle embeddings, tangent graph and canonical embeddings, the
generalized trial-map surface, the direct-rotation minimality results and the
sharpness witnesses all compile and are sorry-free, so keeping them out of the
default build meant proved mathematics was not guarded against regression.

What remains is `DoubleAngle/SinTheta`, which collides with the production
module of the same path and needs a merge rather than a move. -/
