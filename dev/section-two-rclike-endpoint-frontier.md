# Scalar-generic Section 2 endpoints: what each family still needs

Status: current as of the `sin 2Θ` full-gap closure (2026-08-31).

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

`paperTanAngleOperatorC` exists only over `ℂ`, and `paperTanAngleOperatorR` is
defined by transport rather than as the `ℝ` instance of one definition:

```
paperTanAngleOperatorR U V
  = realPartOperator (paperTanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))
```

The chain is `cfc Real.tan (cfc Real.arcsin (ContinuousLinearMap.modulus (P_U - P_V)))`.
**`modulus` is not unconditionally `RCLike`.**  Its module carries

```
variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
```

and says of the third that Mathlib "declines to register [it] as an instance only
because its hypothesis is unavailable outside `ℂ`".  So the angle chain is generic
*given a functional-calculus instance that does not exist for `ℝ`* -- which is a
capability-class problem of the same kind as the sine theorem's, not a free
restatement.

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
the angle definitions.

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

## Not established

That the *analysis* generalizes once the objects do.  These are the first
blockers, found by tracing the accepted proofs; each family may have more behind
them.  Nothing here says the fixed-field proofs resist generalization, and
`tanTwoTheta_branchFree_bounded_paperUINorm_complex` — the arbitrary-trial-subspace
form at one field — is evidence in the other direction.
