/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/

import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Basic
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.RectangularUINorm
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Residual
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Sylvester
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTwoTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.PartIII
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTwoTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Generalized
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.DirectRotation
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Davis1963
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Sharpness
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Statistics
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SingularSubspace

/-!
# Finite-dimensional Davis--Kahan theory

Umbrella import for the literature-indexed finite theory under
`ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory`.

The classical Part III quartet has a proof-complete, scope-accurate facade in
`DavisKahanTheory.PartIII`.  In particular, the two sine theorems are available
for every unitarily invariant norm, while the classical tangent headlines are
the pole-free vector `tan Theta` theorem and the sharp operator-norm
`tan 2 Theta` theorem.

Other imported modules also contain explicit research scaffolds for stronger
residual, graph-operator, all-UI tangent, direct-rotation, generalized, and
sharpness results.  Their remaining proof holes are extensions of the finite
Part III core, not evidence that the four classical headline theorems are
missing.
-/
