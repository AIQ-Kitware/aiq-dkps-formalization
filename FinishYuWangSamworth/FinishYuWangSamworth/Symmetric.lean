/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.Symmetric.Theorem1
import FinishYuWangSamworth.Symmetric.AngleIdentity
import FinishYuWangSamworth.Symmetric.OrthogonalSharpness

/-!
# Symmetric Yu--Wang--Samworth surface

This aggregate exposes:

* Theorem 1 in general unitarily invariant, Frobenius, and operator norms;
* Theorem 2 and its aligned-basis conclusion from
  `DavisKahan.Specialized.Statistics`;
* rank-one Corollary 3;
* the exact rank-one double-angle identity recorded as equation (4);
* the Section 2 orthogonal-blocks sharpness example, which exhibits the
  aligned-basis constant `2^{3/2}` and the `√d` dimension dependence as
  unimprovable.
-/
