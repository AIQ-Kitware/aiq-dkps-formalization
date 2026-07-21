/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.FiniteDimensional.Residual.AngleEmbeddings
import DavisKahan.TanTwoTheta.All

/-!
# Finite double-angle tangent compatibility surface

The canonical finite coordinate map is
`ForMathlib.DavisKahanTheory.tanTwoThetaEmbedding`, defined as
`(2 S |C|) (C⋆C - S⋆S)⁺`.  Its proof-carrying inverse-on-range identity is
`tanTwoThetaEmbedding_eq_inverseOnRange`.

The former declarations in this file mixed coordinate maps `F → E`, ambient
cross blocks `E → E`, and contour continuation.  Several asserted arbitrary
UI-norm identifications were false because full-space angle operators duplicate
principal-plane multiplicities.  That family has been retired rather than
reintroduced under fictional helper APIs.  The supported bounded complex
operator-norm tan-two-theta theory is imported from `DavisKahan.TanTwoTheta`.
-/
