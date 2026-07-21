/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Geometry.Angle.OperatorAngleComplex
import DavisKahan.Geometry.Angle.OperatorAngleReal
import DavisKahan.Geometry.Angle.PaperOperatorAngle

/-!
# Retired incomplete-scalar abstract angle facade

The former declaration in this module requested a positive square root of an
operator on an arbitrary, possibly incomplete, real or complex inner-product
space.  Such a bounded square root need not preserve the incomplete space, and
the pinned functional calculus is available only on complete complex Hilbert
spaces.  The old signature therefore did not describe a supported canonical
construction.

The completed implementations are:

* `ForMathlib.DavisKahanExt.sinTwoAngleOperatorC` for complete complex spaces;
* `ForMathlib.DavisKahanExt.sinTwoAngleOperatorRC` through real
  complexification;
* `ForMathlib.DavisKahanTheory.sinTwoThetaEmbedding` for finite trial
  coordinates.

The historical source is retained under
`dev/retired-full-part-iii-ambient-route-2026-07-21/`.
-/
