/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberAdjoint
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberSingularValues
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberMinMax

/-!
# Approximation numbers on Hilbert spaces

Compatibility aggregate for the Hilbert-space approximation-number API.
The implementation is split into adjoint invariance, finite-dimensional
singular-value identification, and infinite-dimensional min--max lower bounds.
-/
