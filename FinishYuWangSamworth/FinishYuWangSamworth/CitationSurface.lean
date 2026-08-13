/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.Symmetric
import FinishYuWangSamworth.Rectangular
import FinishYuWangSamworth.Appendix

/-!
# Citation-priority Yu--Wang--Samworth API

Numbering here is the **published** Biometrika numbering.  The 2014 preprint
shares one counter and calls the last three Corollary 3, Theorem 4 and Lemma 5,
which several declaration names in this library still spell; the census carries
the translation table.

Every numbered result of the paper is represented, at the printed generality:

1. classical Davis--Kahan Theorem 1;
2. population-gap Theorem 2 and its aligned-frame conclusion, for arbitrary
   ordered eigenframes;
3. rank-one Corollary 1, both displays;
4. right and left singular-subspace Theorem 3, in its corrected form;
5. Appendix Lemma A1.

The surface also includes direct rank-one singular-vector corollaries, the
rank-one algebraic identity recorded as equation (4), all three Section 2
sharpness constructions, the Section 1 illustration that Theorem 1's separation
can vanish, and the deterministic core of the Section 3 diagnosis.
-/
