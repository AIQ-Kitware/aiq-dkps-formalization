/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.GroundedImports
import FinishYuWangSamworth.Rectangular.FrobeniusGram

/-!
# Rectangular Yu--Wang--Samworth surface

This module is the active mathematical lane for the exact source-shaped
Theorem 4. Existing Gram-operator and singular-subspace infrastructure lives in
`DavisKahan.Specialized.SingularSubspace`; the missing completion is the full
right/left theorem with

* the population squared-singular-value gap;
* `min (sqrt d * ||Ahat - A||_op) ||Ahat - A||_F`;
* the source constant `2 * (2 * sigma_1 + ||Ahat - A||_op)`;
* aligned-basis conclusions; and
* rank-one singular-vector corollaries.
-/
