/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.All
import DavisKahan.FiniteDimensional.Residual.All
import ForMathlib.Analysis.InnerProductSpace.FrameFactorization
import DavisKahan.FiniteDimensional.Sylvester.All
import DavisKahan.FiniteDimensional.SinTheta.OperatorNorm
import DavisKahan.FiniteDimensional.SinTheta.UnitarilyInvariant
import DavisKahan.FiniteDimensional.SinTheta.Perturbation
import DavisKahan.FiniteDimensional.SinTheta.TrialMap
import DavisKahan.FiniteDimensional.TanTheta.Vector
import DavisKahan.FiniteDimensional.TanTheta.RitzResidual
import DavisKahan.FiniteDimensional.DoubleAngle.Vector
import DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import DavisKahan.FiniteDimensional.DoubleAngle.TanTheta

/-!
# Stable finite-dimensional Davis--Kahan theory

The proof-complete sine, tangent, double-angle, residual, frame-factorization,
and finite Sylvester surfaces. Open extensions are intentionally absent.
-/
