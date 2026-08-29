/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ForTauCeti.Topology.Berge
import ForTauCeti.Analysis.InnerProductSpace.Singular.Values

/-!
# Roadmap bridge: `MatrixSpectralStatistics`

**What this file is for.** The roadmap checkout's `**/Suggested.lean` states the signatures the
roadmap proposes, against `Mathlib` alone, with unproved bodies.  `ForTauCeti` proves the
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
* **It over-counts, which is the dangerous direction.** `upperHemicontinuousAt_isMinOn` was
  reported *delivered* while the delivered one assumed `[FirstCountableTopology X]` and the
  roadmap's did not -- a gap a name-equality check cannot see, and scores as done.  The
  roadmap was right that the hypothesis was a proof artifact of the sequential route:
  `ForTauCeti.Topology.Berge` now proves it from the tube lemma
  `IsCompact.eventually_forall_of_forall_eventually` instead, and the delivered signature
  carries neither `[FirstCountableTopology X]`, `[T2Space X]`, nor
  `[(𝓝 p₀).IsCountablyGenerated]`.  The example is kept because the *failure mode* is the
  point, not this instance of it.

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

/-- Roadmap `PolarDecomposition.singularValues_toLinearMap`, discharged by the
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
**`upperHemicontinuousAt_isMinOn` -- the gap recorded here has since been closed.**

The roadmap asks for, with only `[TopologicalSpace P] [TopologicalSpace X]` in scope:

    theorem upperHemicontinuousAt_isMinOn [T2Space X]
        (hK : IsCompact K) (hg : Continuous (Function.uncurry g))
        (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
        UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀

This paragraph used to say that `ForTauCeti.Topology.Berge` proved a theorem of that name
which *additionally* assumed `[FirstCountableTopology X]`, so the delivered statement did
not imply the proposed one and the delivered count was wrong.  **That is no longer true**,
and the fix went the direction the paragraph predicted it would have to: the sequential
route through `UpperHemicontinuousAt.of_sequences` was abandoned for the classical
open-cover argument, in `upperHemicontinuousAt_isMinOn_of_isCompact`.

Measured 2026-08-05 by elaborating `#check @TauCeti.upperHemicontinuousAt_isMinOn`, the
delivered binders are exactly

    {P} [TopologicalSpace P] {X} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) (p₀ : P)

-- no `[T2Space X]`, no `[FirstCountableTopology X]`, no `[(𝓝 p₀).IsCountablyGenerated]`.
So the delivered theorem is **strictly more general** than the proposed one, which it
implies by discarding the two instances the roadmap offers it.  The countability-free
statement is the one to advertise.

The *value-function* half is a different matter and is still genuinely restricted:
`continuous_iInf_of_isCompact` carries `[FirstCountableTopology X] [FirstCountableTopology P]`
together with `K.Nonempty`.  Berge's theorem should therefore not be advertised as
hypothesis-free across the board -- only its upper-hemicontinuity half is.

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
