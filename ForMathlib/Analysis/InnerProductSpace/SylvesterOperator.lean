/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.SylvesterBound

/-! # The bounded Sylvester operator

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for upstreaming to Mathlib rather than
  to Tau Ceti — see `ForTauCeti/README.md` on the split between the two staging
  areas.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForMathlib` import firewall admits only
  Mathlib and `ForMathlib` (enforced by `scripts/check_dependency_layers.py`).
-/


variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

/-- The Sylvester operator `X ↦ A X - X B`. -/
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

/-- The Sylvester operator `X ↦ A X - X B`, bundled as a continuous linear map.

`sylvesterOperator` is its underlying function.  The bundled form is what lets
the Sylvester operator be *called* injective, bounded below, or invertible:
those are statements about an operator, not about a family of values.  It is a
difference of the two one-sided composition maps, each of which is continuous
and linear in `X`. -/
noncomputable def sylvesterOperatorL (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] F) :=
  compL 𝕜 E F F A - (compL 𝕜 E E F).flip B

@[simp]
theorem sylvesterOperatorL_apply (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X : E →L[𝕜] F) :
    sylvesterOperatorL A B X = A ∘L X - X ∘L B :=
  rfl

/-- The bundled and unbundled Sylvester operators agree, definitionally.  Stated
so the two cannot drift apart. -/
theorem coe_sylvesterOperatorL (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    ⇑(sylvesterOperatorL A B) = sylvesterOperator A B :=
  rfl

end ContinuousLinearMap

