# Scalar-generic Section 2 endpoints: what each family still needs

Status at `cb3b330b`.  `sin Θ` is done; this records the traced dependency
frontier for the other three, from the **accepted fixed-field endpoint proof**
downward, not extrapolated from the weaker `RCLike` wrappers.

## `sin Θ` — complete

`DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`, bound as
`SectionTwo.sinTheta`.  Conformance to both fixed fields is compiled
(`..._complex_ofRCLike`, `..._real_ofRCLike`), with no adapter.

## `tan Θ` — API bridge

Target: `tanTheta_ambient_unboundedRitz_paperUINorm_rclike`, the scalar
abstraction of `tanTheta_ambient_unboundedRitz_paperUINorm_complex`.

**Every structural input is already scalar-generic.**  `DavisKahan.UnboundedRitzPair`,
`DavisKahan.ReducingComplement` (`DavisKahan/TanTheta/RitzPair.lean`) and
`DavisKahan.CrossedDefectsEquivalent`
(`DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean`) all carry
`{𝕜 : Type u} [RCLike 𝕜]`.  So do `SemiboundedAbove` and the residual identity.

**First field-specific dependency: the angle object in the conclusion.**
`paperTanAngleOperatorC` exists only over `ℂ`, and `paperTanAngleOperatorR` is
defined by transport, not as the `ℝ` instance of one definition:

```
paperTanAngleOperatorR U V
  = realPartOperator (paperTanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))
```

so the generic statement cannot presently be written.

**Smallest missing generic construction.**  The chain bottoms out generic:

| definition | built from | already generic? |
| --- | --- | --- |
| `paperTanAngleOperatorC` | `cfc Real.tan (paperAngleOperatorC U V)` | `cfc` is Mathlib-generic |
| `paperAngleOperatorC` | `cfc Real.arcsin (sinAngleOperatorC U V)` | same |
| `sinAngleOperatorC` | `ContinuousLinearMap.modulus (U.starProjection - V.starProjection)` | **yes** — `modulus` is `[RCLike 𝕜]` in `ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean` |

Nothing in the chain needs `ℂ`; the definitions are over `ℂ` because their files
fix `ℂ`.  `Geometry/Angle/Proposition35*.lean` already carry `[RCLike 𝕜]` in the
same directory.

**Classification: API BRIDGE.**  Surface: three definitions to restate generically
plus the theorems named after them — 13 for `sinAngleOperatorC`, 10 for
`paperAngleOperatorC`, 4 for `paperTanAngleOperatorC` — across
`Geometry/Angle/{OperatorAngleComplex,PaperOperatorAngle,PaperTanAngle}.lean`,
with about 290 use sites, most inside that directory.

**The obligation that comes with it**, and it is not optional: a generic
definition owes a theorem that its `ℝ` instance equals the transport-defined
`...R`, or every existing real theorem stops applying to the new object.  Do this
before migrating consumers, not after.

## `sin 2Θ` and `tan 2Θ` — blocked on the spectral-selection layer

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

**Recommended order.**  Do `tan Θ` first: it is a bridge, it exercises the
"generic definition plus an `ℝ`-agreement theorem" pattern on the smaller angle
chain, and that pattern is exactly what the spectral layer would need.  Decide
`sin 2Θ` / `tan 2Θ` after seeing what `tan Θ` costs.

## Not established

That the *analysis* generalizes once the objects do.  These are the first
blockers, found by tracing the accepted proofs; each family may have more behind
them.  Nothing here says the fixed-field proofs resist generalization, and
`tanTwoTheta_branchFree_bounded_paperUINorm_complex` — the arbitrary-trial-subspace
form at one field — is evidence in the other direction.
