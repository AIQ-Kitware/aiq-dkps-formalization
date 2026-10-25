/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 Astra Pro
-/
module

public import DavisKahan.Sources.DavisKahan1970.Section4SmallAngle

/-!
# Axiom and public-interface audit for the small-angle extension

Compile after the new module. Inspect the printed axiom dependencies: in
particular no `sorryAx` or project-specific unproved axiom may occur. This
file records checks to run; its presence alone is not a completed audit.
-/

public section

open TauCeti
open TauCeti.DavisKahan.FiniteDimensional

#check TauCeti.DavisKahan1970.proposition4_4_parameterized_traceNorm_counterexample
#check TauCeti.DavisKahan1970.proposition4_4_parameterized_principalAngles
#check TauCeti.DavisKahan1970.proposition4_4_arbitrarilySmall_refutingPair

#print axioms SmallAngleCounterexample.projection_V4_coord
#print axioms SmallAngleCounterexample.gram_canonicalIntertwiner
#print axioms SmallAngleCounterexample.principalAngles_eq
#print axioms SmallAngleCounterexample.kyFanSum_displacement_R
#print axioms SmallAngleCounterexample.kyFanSum_displacement_W
#print axioms SmallAngleCounterexample.kyFanSum_lt
#print axioms arbitrarilySmall_fullDisplacement_refuted

/-- Exercise the exported arbitrary-threshold result without unfolding its construction. -/
example (epsilon : Real) (h : 0 < epsilon) :
    ∃ (U V : Submodule Real (EuclideanSpace Real (Fin 4)))
      (ha : IsAcute U V)
      (W : EuclideanSpace Real (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace Real (Fin 4)),
      U.map W.toLinearMap = V ∧
      0 < principalAngles U V 0 ∧
      principalAngles U V 0 < epsilon ∧
      principalAngles U V 0 ≤ Real.pi / 3 ∧
      kyFanSum 4 (LinearMap.id - W.toLinearMap) <
        kyFanSum 4 (LinearMap.id - (directRotation U V ha).toLinearMap) :=
  TauCeti.DavisKahan1970.proposition4_4_arbitrarilySmall_refutingPair epsilon h
