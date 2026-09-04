# Scalar-generic Section 2 endpoints: what each family still needs

Status: **partly superseded, 2026-09-04.**  The tracing below is still the record
of how the three families were blocked, and the `tan Θ` and `tan 2Θ` analysis is
unchanged.  Its central recommendation is not: it tells the reader to settle
whether to build a scalar-generic projection-valued spectral measure *before*
starting any family, and that is no longer the right next step.  Read
"What the scalar transport settled" immediately below before acting on anything
in this file.  Declaration names here also predate the `paperUINorm` →
`symmetricNorming` rename; resolve a name against the tree before citing it.

## What the scalar transport settled (2026-09-01 .. 2026-09-04)

Four things this document treats as open or as costed obstacles are now facts in
the tree.

1. **The dispatch exists and is used.**  `ForTauCeti/Analysis/RCLike/`
   `ScalarTransport.lean` carries a Hilbert space, its operators, its
   `LinearPMap`s, its subspaces and its adjoints across an isomorphism of `RCLike`
   fields.  The "second complexification-scale layer" the last section prices is
   built, and it is about 550 lines, not a campaign.

2. **The real continuous functional calculus is an instance at every `RCLike`
   field**, not something behind a capability binder:
   `ContinuousLinearMap.continuousFunctionalCalculusReal`
   (`ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean`), obtained
   by transporting the `ℝ` and `ℂ` constructions.  Every sentence below about the
   angle vocabulary being available "behind a capability binder with instances at
   `ℝ` and `ℂ`" should be read as: available, full stop.

3. **The angle objects are written.**  `TauCeti.DavisKahan.Angle.sinAngleOperator`,
   `.angleOperator`, `.sinTwoAngleOperator` and the directed
   `.directedSinAngleOperator` / `.directedCosAngleOperator` /
   `.directedSinTwoAngleOperator` are single definitions at arbitrary `[RCLike 𝕜]`
   which *are* the `...C` objects over `ℂ` and complexify to the `...R` / `...RC`
   ones over `ℝ`.  The ideal block and the directed `sin 2Θ` have the same gauge in
   every `SymmetricNormingFunction` at every field
   (`DoubleAngle/DirectedAngleGeneric.lean`).

4. **The ambient `sin 2Θ` clause is proved at arbitrary `RCLike`**:
   `sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike`, on the
   angle operator rather than on a projector-difference representative.

### The spectral-selection question is not the blocker it is described as

This file says the remaining obstacle is that the conclusion "names the angle
operators **and the spectral selection**", and recommends deciding about a generic
projection-valued measure first.  Do not start there.

The ambient clause was closed without any generic spectral measure, by taking the
hypotheses the *proof* actually needs -- a reducing subspace and a reflected pair --
rather than the spectral subspaces the fixed-field wrappers construct from
measurable sets.  The directed clause looks the same: the accepted fixed-field
theorem `sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_`
`symmetricNorming_complex` already quantifies over an **arbitrary reducing
subspace**, and so does the old Palomar directed proof.

So the open question is a **source-correspondence** one -- whether the paper's
standing hypotheses are faithfully expressed by "a reducing subspace with
separated blocks" -- and it should be settled by reading the source, not by
building operator theory.  Only if the answer is no does a generic spectral
measure become the next task.

### What the directed clause actually needs

Transport of the unbounded-ideal proof data: `ReducesSubspace`,
`LinearPMap.reducingRestriction`, the trial residual, and
`SymmetricNormingFunction` membership and gauge.  `formBoundedSylvesterGap_pmap`,
`kyFanApproximationGauge_clm`, `reducesSubspace_pmap_iff` and
`approximationNumber_clm` are written; `reducingRestriction` is not, and its known
snag is that `ScalarTransport e ↥U` and `↥(submodule U)` are the same type with
the same norm and inner product but present `Submodule 𝕂` with different
`AddCommMonoid` / `Module` instance paths, so `rw` needs bridging lemmas.

Then the estimate lands on `sinTwoThetaIdealBlock` and the correspondence in (3)
carries it to `Angle.directedSinTwoAngleOperator`, which is the object
`SectionTwo.sinTwoTheta` may be bound to and nothing weaker.

---

*The original document follows, unedited except for this header.*


## Two different questions, kept apart

This document answers exactly one of them.

**(1) Scalar-generic `RCLike` endpoint construction** — can the Section 2 result
be *stated and proved once* over an arbitrary `RCLike` field, so that
`SectionTwo.{tanTheta, sinTwoTheta, tanTwoTheta}` can be bound?  That is what the
rest of this file traces.  It is an architecture question about this library, not
about Davis and Kahan.

**(2) Fixed-field exact source-scope completion** — does the `ℂ` endpoint, and
does the `ℝ` endpoint, cover the scope the paper prints?  That is a source-fidelity
question, it is owned by
`dev/davis-kahan-1970-formalization-result-inventory.json`, and it is **not**
answered here.

Confusing the two is a live failure mode.  On 2026-08-31 `S2-sin-two-theta` was
reopened for a question of kind (2): both `ℂ` endpoints took a *bounded*
separating interval while the source allows half-infinite ones, and only the real
endpoints carried `FormBoundedSylvesterGap`.  That had nothing to do with `RCLike`
genericity, and was fixed without touching it — by giving the complex track the
real track's proof architecture (`sinTheta_unbounded_complex_block` →
`sinTheta_addBounded_gauge_complex_block_of_formGap` →
`sinTwoTheta_reflectionResidual_block_gauge_of_formGap`).  `sin 2Θ` therefore
appears below as still open for (1) and closed for (2).

`sin Θ` is done for both; this records the traced dependency frontier for the
other three on question (1), from the **accepted fixed-field endpoint proof**
downward, not extrapolated from the weaker `RCLike` wrappers.

## `sin Θ` — complete

`DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`, bound as
`SectionTwo.sinTheta`.  Conformance to both fixed fields is compiled
(`..._complex_ofRCLike`, `..._real_ofRCLike`), with no adapter.

## `tan Θ` — generic infrastructure, **not** an API bridge

Target: `tanTheta_ambient_unboundedRitz_paperUINorm_rclike`, the scalar
abstraction of `tanTheta_ambient_unboundedRitz_paperUINorm_complex`.

**Correction, 2026-08-31.**  An earlier revision of this document classified
`tan Θ` as an API bridge and estimated a ~290-site angle genericization.  That
was wrong on both the reasoning and the recommendation, and the sweep should not
be started on it.  Two field-specific layers were missed.

The part that was right: every *structural input* is already scalar-generic.
`DavisKahan.UnboundedRitzPair`, `DavisKahan.ReducingComplement`
(`DavisKahan/TanTheta/RitzPair.lean`), `DavisKahan.CrossedDefectsEquivalent`
(`DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean`), `SemiboundedAbove`
and the residual identity all carry `[RCLike 𝕜]`.  The blockers are elsewhere.

### Layer 1: the ambient angle, and the functional calculus under it

`tanAngleOperatorC` exists only over `ℂ`, and `tanAngleOperatorR` is
defined by transport rather than as the `ℝ` instance of one definition:

```
tanAngleOperatorR U V
  = realPartOperator (tanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))
```

The chain is `cfc Real.tan (cfc Real.arcsin (ContinuousLinearMap.modulus (P_U - P_V)))`.
**`modulus` is not unconditionally `RCLike`.**  Its module carries

```
variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
```

and says of the third that Mathlib "declines to register [it] as an instance only
because its hypothesis is unavailable outside `ℂ`".

**Correction, 2026-08-31.**  That instance is no longer unavailable for `ℝ`.
`ForTauCeti/Analysis/InnerProductSpace/RealContinuousFunctionalCalculus.lean`
registers `ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint` for **every**
real Hilbert space at unrestricted dimension, and

```lean
example : ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint := inferInstance
noncomputable example (T : E →L[ℝ] E) : E →L[ℝ] E := ContinuousLinearMap.modulus T
noncomputable example (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : E →L[ℝ] E :=
  cfc Real.sin (cfc Real.arcsin
    (ContinuousLinearMap.modulus (U.starProjection - V.starProjection)))
```

all elaborate.  So the angle chain is generic behind a capability binder that has
instances at **both** of the paper's fields -- exactly the situation of
`HasMinMaxLowerBoundEverywhere` in the sine theorem, and not a blocker of its own.
`tanAngleOperatorR` is defined by transport for historical reasons, not
because a direct real definition is unavailable.

Layer 1 is therefore no longer where `tan Θ` is stuck.  Layer 2 is.

### Layer 2: the Appendix cutoff, which is where the real content is

The accepted endpoint reaches its estimate through
`UnboundedCompressionTrialData.all_kyFan_core`, the Appendix spectral truncation
and release.  `DavisKahan/TanTheta/Theorem63UnboundedCompression.lean`
deliberately separates two layers: the structure and its algebra are `[RCLike 𝕜]`
(from line 86), and **the truncation layer is pinned to `[InnerProductSpace ℂ H]`
from line 213**, because it uses the projection-valued measure.  `all_kyFan_core`
is in the pinned section.

`TanThetaUnboundedAmbientReal.lean` confirms the architecture in its own words:
the real route complexifies `UnboundedCompressionTrialData`, runs "the existing
complex Appendix cutoff/Ky-Fan argument", and descends.

### Classification: GENERIC INFRASTRUCTURE (category B)

Two seams, and the second is the same projection-valued-measure dependency that
blocks `sin 2Θ` and `tan 2Θ`.  Genericizing the angle chain alone would not
produce the endpoint; it would produce a statement that cannot be proved.

**The seam to trace first is `UnboundedCompressionTrialData.all_kyFan_core`**, not
the angle definitions -- and after the 2026-08-31 correction above, that is the
*only* seam for `tan Θ`.

## `sin 2Θ` and `tan 2Θ` — blocked on the spectral-selection layer

*(Question (1) only.  `sin 2Θ` is closed on question (2) as of 2026-08-31: both
fixed-field endpoints now take `FormBoundedSylvesterGap`, and
`SectionTwoUsage.sinTwoTheta_from_halfInfinite_separation` is the compiled witness
that the half-infinite branch can be called.  `tan 2Θ` question (2) status is in
the result inventory, not here.)*

Targets: `sinTwoTheta_directed_unbounded_addBounded_paperUINorm_rclike` and
`tanTwoTheta_ambient_unbounded_paperUINorm_rclike`.

Their accepted endpoints do not name subspaces abstractly.  They name spectral
subspaces *selected* from measurable spectral sets —
`DavisKahan.selfAdjointSpectralSubspace A hA B hB` for `sin 2Θ`, and
`TauCeti.LinearPMap.specRange hA (Set.Iic c)` for `tan 2Θ`.  That selection is
part of the source shape and must not be replaced by an arbitrary subspace with a
`Reduces` hypothesis.

**First field-specific dependency: the selection itself.**

| object | complex | real |
| --- | --- | --- |
| `specRange` | `ForTauCeti/.../LinearPMap/SpectralMeasure/Construction.lean`, ambient `[InnerProductSpace ℂ H]`, `{A : H →ₗ.[ℂ] H}` | `realSpecRange`, `ForTauCeti/.../LinearPMap/Complexification/SpectralDescent.lean` |
| `selfAdjointSpectralSubspace` | `DavisKahan/SpectralTheory/SpectralRestriction.lean`, ambient `[InnerProductSpace ℂ H]` | `realSelfAdjointSpectralSubspace`, `DavisKahan/SpectralTheory/Real/SpectralRestriction.lean` |

This is the projection-valued spectral measure of an unbounded self-adjoint
operator.  Unlike the angle chain, the real case is not a notational restatement:
it is *defined* by descent through the complexification, because that is how a
real self-adjoint operator acquires a spectral measure.

**Classification: GENERIC INFRASTRUCTURE, and possibly not the right goal.**  It
is not new Davis--Kahan mathematics — both fields already have the construction —
but a `𝕜`-generic spectral measure is a substantial piece of operator theory, and
it is not obvious that a generic construction is even the right shape when the
`ℝ` instance would have to reduce to the descent by a theorem.

**Recommended order.**  All three now bottom out on the same thing: a
projection-valued spectral measure that exists over `ℂ` and reaches `ℝ` by
descent.  `tan Θ` additionally needs the real functional-calculus instance for the
angle chain.  So the question is not which family is cheapest but whether that
one operator-theory layer is worth making scalar-generic at all, given that the
`ℝ` instance would have to reduce to the descent by theorem anyway.  Answer that
before starting any of the three.

## What Mathlib's `RCLike` dispatch API does and does not buy (checked 2026-08-31)

The obvious idea for removing the capability classes is to **dispatch**: given
`[RCLike 𝕜]`, split into the real and the complex case and call the fixed-field
theorem.  Current Mathlib does support the scalar half of that:

* `RCLike.I_eq_zero_or_im_I_eq_one : (I : K) = 0 ∨ im (I : K) = 1`;
* `RCLike.realRingEquiv` / `RCLike.realLinearIsometryEquiv` on the first branch
  (`Mathlib/Analysis/RCLike/Basic.lean`);
* `RCLike.complexRingEquiv` / `RCLike.complexLinearIsometryEquiv` on the second
  (`Mathlib/Analysis/Complex/Basic.lean`).

So the earlier reading -- "`RCLike` is open, therefore no dispatch exists" -- was
wrong about Mathlib, and it is recorded here so it is not repeated.  It is,
however, **not** what unblocks the three families, for two reasons.

*The blocker is in the statement, not the proof.*  Dispatch would let a proof
branch, but the theorem has to be **stated** over `𝕜` first, and its conclusion
names the angle operators and the spectral selection.  The **angle** half of that
is no longer blocked: with the real calculus registered (see the `tan Θ`
correction above), `modulus` and the `cfc` chain are available at both fields, so
a `𝕜`-generic angle vocabulary is writable behind a capability binder with
instances at `ℝ` and `ℂ`.  The **spectral-selection** half is still blocked, and
it is the harder one: `specRange` and `selfAdjointSpectralSubspace` exist over
`ℂ` and reach `ℝ` by descent through the complexification.  `sin Θ` is generic
without any of this precisely because its conclusion is a scalar-generic operator
expression, `(I - F₀F₀⋆)E₀`, naming no angle and no selection.

*The transport is a development, not a facade.*  Even with a
`𝕜 ≃ₗᵢ[ℝ] ℂ`, using it means carrying an `InnerProductSpace 𝕜 E` structure, its
`LinearPMap`s, its spectral subspaces, its `PaperUnitaryInvariantNorm` membership
and gauge, and its `FormBoundedSylvesterGap` across a scalar-field isomorphism.
That is a second complexification-scale layer, alongside the `ℝ → ℂ` one this
repository already has -- and the `ℝ` branch would then reach the fixed-field
theorem through *two* transports rather than one.

Neither observation says the generic endpoints are impossible.  Both say the
recommended order above is unchanged: settle whether one scalar-generic
projection-valued spectral measure is worth building, before starting any of the
three.

## Not established

That the *analysis* generalizes once the objects do.  These are the first
blockers, found by tracing the accepted proofs; each family may have more behind
them.  Nothing here says the fixed-field proofs resist generalization, and
`tanTwoTheta_branchFree_bounded_paperUINorm_complex` — the arbitrary-trial-subspace
form at one field — is evidence in the other direction.
