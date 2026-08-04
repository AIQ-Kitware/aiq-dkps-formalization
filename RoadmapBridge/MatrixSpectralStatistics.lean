/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ForTauCeti.Topology.Berge
import ForTauCeti.Analysis.InnerProductSpace.Singular.Values

/-!
# Roadmap bridge: `MatrixSpectralStatistics`

**What this file is for.** `submodules/TauCetiRoadmap/**/Suggested.lean` states the signatures the
roadmap proposes, against `Mathlib` alone, with `sorry` bodies.  `ForTauCeti` proves the
mathematics.  Nothing connected the two: `scripts/check_roadmap_delivered.py` compares
*declaration names* between the two trees, and its own output says so --

> Name matches are an internal diagnostic only; they do not establish statement
> equivalence or roadmap completion.

This file supplies the missing link for one topic.  Each entry **restates the roadmap's
signature verbatim** -- same explicit hypotheses, same instance binders, same conclusion --
and discharges it with the delivered declaration.  If it elaborates, the delivered theorem
really does imply the proposed one, checked by the compiler rather than by string equality.

**Why this is not bookkeeping.** Name matching is wrong in *both* directions, and one
instance of each is recorded below:

* **It under-counts.** `singularValues_toLinearMap` is reported outstanding; the identical
  statement is delivered as `ContinuousLinearMap.toLinearMap_singularValues`, `rfl` on both
  sides, differing only in the order of the two words in the name.
* **It over-counts, which is the dangerous direction.** `upperHemicontinuousAt_isMinOn` is
  reported *delivered* because a declaration of that name exists -- but the delivered one
  assumes `[FirstCountableTopology X]` and the roadmap's does not.  The roadmap is explicit
  that this is unacceptable rather than incidental: the extra hypothesis is "a proof
  artifact -- it goes through the sequential characterization -- so if both versions coexist
  it is the *restricted* one that should be qualified (`..._of_firstCountable`) or kept
  private, not this one."  A name-equality check cannot see that, and scores it as done.

So the bridge entries below are stated so that **failure to elaborate is the finding**.
Where the roadmap's statement is genuinely stronger than what is proved, there is no entry
and the reason is recorded in `Gaps` at the bottom, not silently omitted.

## The part that makes name matching unfixable, rather than merely inaccurate

The submitted roadmap introduces **81 definitions and structures of its own** across the six
topics, and states its theorems about those.  A theorem name shared between the two trees
therefore certifies nothing until the *definitions underneath it* are known to agree, and
they agree for two quite different reasons that look identical from outside:

* **Definitionally, via a shared Mathlib notion.**  The roadmap's `singularValues` is
  `T.toLinearMap.singularValues` and so is `ForTauCeti`'s -- both thin wrappers on Mathlib's
  `LinearMap.singularValues` -- so the entry below is discharged by the delivered lemma and
  is faithful to the roadmap's statement.
* **Not at all, until someone proves it.**  The roadmap defines its own
  `hilbertSchmidtEnergy` (`OperatorIdeals/Suggested.lean:165`).  `ForTauCeti` has a
  `hilbertSchmidtEnergy` too.  Nothing relates them, so
  `tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy` cannot be bridged by supplying the
  delivered theorem -- the two statements are about different functions that happen to share
  a name.  Attempting it directly does not fail cleanly either: the unifier runs to a
  `isDefEq` heartbeat timeout, still there at 2,000,000 heartbeats.

**Consequence, and the reason to build the bridge definition-first**: the unit of roadmap
delivery is not the theorem, it is the *definition plus the theorems about it*.  A bridge
that discharges theorems while leaving the definitions unrelated reproduces the defect it
was built to remove, one level down.
-/

namespace RoadmapBridge.MatrixSpectralStatistics

open Filter Topology Set

/-! ## Delivered, under a different name

These discharge the roadmap's statement with a delivered declaration whose name differs.
The gate reports them outstanding; the compiler reports them proved. -/

section SingularValues

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Roadmap `HilbertSpaceOperatorFoundations.singularValues_toLinearMap`, discharged by the
delivered `ContinuousLinearMap.toLinearMap_singularValues`.

The two statements are literally the same equation; the delivered name orders the words the
other way and its docstring gives the reason ("oriented towards the continuous form, so that
`simp` removes the coercion from statements rather than introducing it").  **The roadmap
should adopt the delivered name**: the orientation is a deliberate `simp`-normal-form choice
and the roadmap's spelling would reverse it. -/
theorem singularValues_toLinearMap (T : E →L[𝕜] F) :
    (T : E →ₗ[𝕜] F).singularValues = T.singularValues :=
  ContinuousLinearMap.toLinearMap_singularValues T

end SingularValues

/-! ## Gaps -- stated, not bridged, with the obstruction named

Nothing below elaborates against the current library, and each is a *different* kind of
miss.  They are written out rather than left implicit because "no entry" and "no gap" must
not look the same in this file. -/

section Gaps

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
variable {K : Set X} {g : P → X → ℝ}

/-
**`upperHemicontinuousAt_isMinOn` -- reported delivered, and it is not.**

The roadmap asks for, with only `[TopologicalSpace P] [TopologicalSpace X]` in scope:

    theorem upperHemicontinuousAt_isMinOn [T2Space X]
        (hK : IsCompact K) (hg : Continuous (Function.uncurry g))
        (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
        UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀

`ForTauCeti.Topology.Berge` proves a theorem of exactly this name that additionally assumes
`[FirstCountableTopology X]`.  So `check_roadmap_delivered` counts it, and the count is
wrong: the delivered theorem does not imply the proposed one.  Discharging this needs the
first-countability removed from the proof -- Mathlib's `UpperHemicontinuousAt.of_sequences`
is the sequential route that forces it, so the general proof cannot go through that lemma.

**`continuous_iInf_of_hemicontinuous` and `upperHemicontinuousAt_isMinOn_of_hemicontinuous`
-- reported outstanding, and genuinely so, but not for the reason the name suggests.**

Both are delivered under the names `continuous_iInf_of_hemicontinuousAt` and
`upperHemicontinuousAt_isMinOn_of_hemicontinuousAt` -- the explicit hypotheses match one for
one (`hKcompact`, `hKne`, `hKu`, `hKl`, `hg`).  The `At` suffix is the *better* name, since
the hypotheses really are the pointwise `UpperHemicontinuousAt`/`LowerHemicontinuousAt`.
**But the instance binders do not match**: the delivered pair carries
`[FirstCountableTopology P] [RegularSpace X] [T2Space X] [FirstCountableTopology X]
[WeaklyLocallyCompactSpace X]`, none of which the roadmap's section assumes.  So these are
neither renames nor missing -- they are delivered under strictly stronger hypotheses, the
same defect as the entry above, and a rename alone would convert a real gap into a false
"delivered".  That is precisely the trap this file exists to make visible.
-/

end Gaps

end RoadmapBridge.MatrixSpectralStatistics
