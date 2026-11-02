/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import Mathlib.Analysis.Complex.Basic

/-!
# Canonical resolvents over general fields, real scalars, and complex scalars

The former local generalization of the real TauCeti resolvent core is retired.
These consumer examples retain the field scope and sign convention checks
against the accepted API, including the real absolute-value perturbation bound.
-/

public section

namespace RoadmapBridge.TauCetiResolvent

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

example {A : E →ₗ.[𝕜] E} {z : 𝕜} {R : E →L[𝕜] E}
    (h : A.IsResolventAt z R) :
    Function.Bijective fun x : A.domain => z • (x : E) - A x :=
  h.smul_sub_bijective

example (T : E →L[𝕜] E) (z : 𝕜) :
    z ∈ (T.toLinearMap.toPMap ⊤).resolventSet ↔ z ∈ _root_.resolventSet 𝕜 T :=
  T.mem_resolventSet_toPMap_top_iff z

example [CompleteSpace E] (A : E →ₗ.[𝕜] E) : IsOpen A.resolventSet :=
  A.isOpen_resolventSet

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

example {A : X →ₗ.[ℝ] X} {z w : ℝ} (hz : z ∈ A.resolventSet)
    (hw : |w - z| * ‖A.resolvent z‖ < 1) : w ∈ A.resolventSet :=
  TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one hz (by rwa [Real.norm_eq_abs])

end Real

section Complex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

example {A : X →ₗ.[ℂ] X} {z : ℂ} (hz : z ∈ A.resolventSet) (x : A.domain) :
    A.resolvent z (z • (x : X) - A x) = (x : X) :=
  LinearPMap.resolvent_smul_sub_apply hz x

end Complex

end RoadmapBridge.TauCetiResolvent
