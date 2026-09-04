/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# The real algebra structure on `E →L[𝕜] E`

Real continuous functional calculus on an operator algebra over an `RCLike` field needs the
algebra to be an `ℝ`-algebra, compatibly with its `𝕜`-action.  Mathlib does not register that:
`Module ℝ (E →L[𝕜] E)` is not even inferable for a general `RCLike 𝕜`, so every consumer of the
modulus, the polar decomposition and the angle operators has been carrying

```text
[Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
```

as hypotheses.  They are not hypotheses.  They are restriction of scalars along
`algebraMap ℝ 𝕜`, and this file registers them.

## Why this is safe

`Algebra` is data, so a second instance is a diamond unless the two agree.  There are two
places where one already exists:

* at `𝕜 = ℝ`, Mathlib's `ContinuousLinearMap.algebra`;
* at `𝕜 = ℂ`, `Algebra.complexToReal`, which this repository installed as the `scoped`
  instance `TauCeti.RealComplexification.complexOperatorRealAlgebra` until it was deleted in
  favour of this file.

Both are definitionally this one — `Algebra.complexToReal` *is* `RestrictScalars.algebra ℝ ℂ`,
and `RestrictScalars.algebra ℝ ℝ` reduces to `ContinuousLinearMap.algebra`.  The instance below
is nevertheless given a low priority so that Mathlib's own instance is the one synthesis finds
at `𝕜 = ℝ`, where it is the more specific answer and the one every existing statement was
elaborated against.

`IsScalarTower` is a `Prop`, so its instance carries no diamond risk at all.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  Written directly here, 2026-09-03, to remove the two-instance
  hypothesis block from the scalar-generic operator API.
* Extraction class: **new**.  It depends on nothing outside Mathlib.
* Namespace: `ContinuousLinearMap`, matching the object it structures.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **The operator algebra over an `RCLike` field is a real algebra**, by restriction of
scalars along `algebraMap ℝ 𝕜`.

Low priority, deliberately: at `𝕜 = ℝ` Mathlib's `ContinuousLinearMap.algebra` is the same
structure and should keep being the one synthesis returns. -/
noncomputable instance (priority := 100) realAlgebra : Algebra ℝ (E →L[𝕜] E) :=
  RestrictScalars.algebra ℝ 𝕜 (E →L[𝕜] E)

/-- The real action on operators factors through the `𝕜`-action. -/
instance (priority := 100) realIsScalarTower : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  RestrictScalars.isScalarTower ℝ 𝕜 (E →L[𝕜] E)

/-! ## What this already unlocks

At `𝕜 = ℂ` the two instances above are the whole gap between Mathlib's complex `C⋆`-algebra
structure on `E →L[ℂ] E` and its real continuous functional calculus.  With them in scope the
calculus is found by synthesis, with no `scoped` instance and no explicit term.  The general
`RCLike` case is `ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean`, which
transports this one. -/

example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    ContinuousFunctionalCalculus ℝ (F →L[ℂ] F) IsSelfAdjoint := inferInstance

end ContinuousLinearMap
