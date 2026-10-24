/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Modulus

/-!
# Commutation of moduli from commutation of Gram operators

This is the remaining rectangular two-operator consequence from the former
`OperatorModulus.lean`. The modulus and its defining, positivity, norm, kernel,
and single-operator commutation APIs are supplied by the accepted dependency.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower

/-- Moduli of rectangular operators with commuting source Gram operators
commute, even when the two target spaces differ. -/
theorem modulus_commute_modulus {S : E →L[𝕜] F} {T : E →L[𝕜] G}
    (h : Commute (S.adjoint ∘L S) (T.adjoint ∘L T)) :
    Commute S.modulus T.modulus :=
  commute_modulus_of_commute (commute_modulus_of_commute h.symm).symm

end ContinuousLinearMap
