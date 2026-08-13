/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.Symmetric.Theorem1
import FinishYuWangSamworth.Symmetric.MixedGap
import FinishYuWangSamworth.Symmetric.Corollary1
import FinishYuWangSamworth.Symmetric.AngleIdentity
import FinishYuWangSamworth.Symmetric.OrthogonalSharpness
import FinishYuWangSamworth.Symmetric.MiddleBlockSharpness
import FinishYuWangSamworth.Symmetric.PlanarSharpness

/-!
# Symmetric Yu--Wang--Samworth surface

This aggregate exposes:

* Theorem 1 in general unitarily invariant, Frobenius, and operator norms;
* Theorem 2 and its aligned-basis conclusion from
  `DavisKahan.Specialized.Statistics`;
* rank-one Corollary 3;
* the exact rank-one double-angle identity recorded as equation (4);
* the Section 2 sharpness examples: orthogonal blocks in both the preprint's
  top-block and the published middle-block form, which exhibit the aligned-basis
  constant `2^{3/2}` and the `√d` dimension dependence as unimprovable, and the
  planar rotation, which pins the sine bound's factor `2` at every angle
  including the small-angle regime.
-/
