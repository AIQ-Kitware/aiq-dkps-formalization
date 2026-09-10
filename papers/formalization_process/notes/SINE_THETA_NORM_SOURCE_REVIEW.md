# Sine-theta source comparison and norm notation

## Review basis

This note records the review against snapshot
`8a8218ab9e2f03ad00e14e523211bc51b245fdb4`. It is an audit note, not manuscript
prose. The mathematical source is the supplied modernized transcription of
Davis and Kahan (1970), particularly Section 1, the Section 2 sine-theta
statement, and the Appendix to Section 6. The review concerns theorem
statements and the definitions appearing in them. Agreement with the source
does not require following its proof argument.

The current declaration is
`TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike` in
`DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`.
The historical declaration in Formalization 1 is extracted from commit
`489c01c2cc992a20d38415b5f827cdc046fe7236`, rather than from the later theorem
with the same name.

No omitted Davis--Kahan gap or domain case was identified in the current
statement. Its decoded hypotheses and conclusion match the source setting
examined here, with the norm laws and where-defined Fan comparison explicitly
packaged in `NormalizedSymmetricOperatorIdealFamily`. This review does not
establish an independent representation theorem from bare unitary invariance,
and does not re-review all 29 project targets. No executable Lean changes
were needed for this revision.

## The operator in the norm

Let `Q = F0 F0*` and `S = (I - Q) E0`. The isometric trial coordinate map
`E0` embeds trial vectors into the ambient Hilbert space. The projection
`I - Q` removes their component in the desired exact subspace. Thus `S`
is a rectangular map from trial coordinates to the ambient space.

The source's positive operator `sin Theta0` acts on trial coordinates.
It is not literally the rectangular map `S`. The identities are

```text
S* S = E0* (I - Q) E0 = I - E0* Q E0
C = (E0* Q E0)^(1/2)
Theta0 = arccos C
sin Theta0 = (I - C^2)^(1/2) = (S* S)^(1/2) = |S|.
```

These are the coordinate form of DK equation (1.16) and the norm identity
stated later in its Section 1. In finite dimensions, the eigenvalues of
`|S|` are the singular values of `S`, hence the sines of the principal angles.
The positive-square-root description also applies in infinite dimension.

Polar decomposition gives `S = U |S|` and `|S| = U* S`. Both `U` and `U*`
are contractions. The two-sided ideal law therefore gives both inequalities
between the norms of `S` and `|S|`, and preserves ideal membership in both
directions. This proves

```text
N(S) = N(|S|) = N(sin Theta0).
```

The argument does not require compactness, a discrete singular-value list,
or extending the partial isometry to a unitary. It uses the source's
contraction compatibility. The supplied transcription states this compatibility
at lines 531--533 and the sine-angle identification at lines 635--650.

Formalization 1's `hSinTheta0` fixes the parameter `sinTheta0` to `S`.
It is an equality naming the rectangular representative, not an assumption of
the target norm inequality. It can be supplied reflexively after choosing that
representative. The norm identification follows from the mathematical
argument above; it does not follow from the parameter's name alone.
Formalization 2 substitutes `S` directly into its conclusion.

Existing formal support includes the polar identities in
`ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean` and the ideal
laws in `ForTauCeti/Analysis/OperatorIdeal/Family/Basic.lean`. The explicit
`source_gauge_modulus_eq_rectangular` theorem in
`DavisKahan/Explorations/SourceUnitaryInvariantNormFanDominance.lean` proves
the gauge equality for the normalized family over the complex field. That
particular theorem is complex-specific; it is not evidence by itself of a
scalar-generic theorem. This revision adds the mathematical explanation to the
paper, without claiming a new compiled bridge theorem.

## What `N.gaugeReal` and its premises mean

The norm record is defined in
`DavisKahan/OperatorIdeal/NormalizedUnitaryInvariantNorm.lean`.
Its underlying ideal gauge is extended nonnegative-real-valued. `N.Mem T`
means that the gauge is finite. `N.gaugeReal T` obtains the real value of
that gauge. The `Real` suffix describes the output, not the scalar field of
`T`.

The two premises in Formalization 2 assert finiteness for `S` and `R`.
Under those premises its conclusion is exactly

```text
delta * N(S) <= N(R)
```

and the norm identity above turns this into the source's
`delta * N(sin Theta0) <= N(R)`. No factor of two occurs in this theorem.

The record stores rank-one normalization, the symmetric ideal laws, and the
where-defined Ky Fan comparison. The sine-theta proof uses that comparison;
it does not derive Fan dominance from unitary invariance alone. DK Section 1
also invokes the Ky Fan comparison as background. The manuscript now states
this boundary explicitly. It makes no unconditional ideal-membership-transfer
claim for arbitrary partial-domain norms.

## Gap and operator scope

The finite interval/exterior branch allows either block to occupy
`[beta, alpha]`; the other stays outside the open interval
`(beta - delta, alpha + delta)`. This agrees with the alternatives in the
Section 2 statement (transcription lines 719--727).

`FormBoundedSylvesterGap` in `DavisKahan/Sylvester/Gap.lean` also has both
ordered half-infinite configurations. Those cases permit both blocks to be
unbounded and cover the unbounded appendix's separating intervals. For
self-adjoint operators the spectral half-line assumptions imply the
quadratic-form bounds. The explicit
`formBoundedSylvesterGap_of_spectral` theorem in
`DavisKahan/Sylvester/Unbounded/FormBoundedGap.lean` is over the complex field;
the mathematical implication used in the explanation is valid over real
Hilbert spaces as well. No claim is made that this individual bridge theorem
has a generic signature.

A source instance distinguishing the historical finite-gap statement is
`A = (-D) direct_sum D` on two copies of `l2`, with `D` the self-adjoint
diagonal operator having entries `1, 2, 3, ...`. Take trial and desired exact
subspaces to be the first summand. Then `A0 = -D`, `Lambda1 = D`,
`delta = 2`, and `R = S = 0`. Both spectra are unbounded, so neither can
occupy a finite interval. The half-infinite branch covers the example.

The current declaration is scalar-generic over `RCLike`, with separable
ambient Hilbert space, self-adjoint partial operators `A`, `A0`, `Lambda1`,
and bounded coordinate maps and residual. It does not require finite
dimension, a bounded trial operator, or a bounded ambient perturbation.
The ambient `A` in this Lean signature denotes DK's `A + H`; the manuscript
now records that notational change before defining the residual.

## Common domains and the removed strictness claim

The source's common-domain condition is represented by `HasCommonDomain` in
`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomain.lean`:

```text
{x : E0 x belongs to dom A} = dom A0.
```

Its `maps_domain` theorem gives the forward inclusion required by
`IsTrialResidual`. Self-adjointness supplies density, and the residual
equation is imposed on that domain. Thus the source condition supplies the
formal hypothesis without requiring every trial vector to lie in `dom A`.

The manuscript had inferred strict extra generality from using only this
forward inclusion. That inference is unwarranted when the other hypotheses
are retained. In fact, a mathematical adjoint-domain argument supplies the
reverse inclusion in the present setting. If `E0 y` belongs to `dom A`, then
for every `x` in `dom A0`, the isometry, residual relation, and self-adjointness
of `A` give

```text
<A0 x, y> = <x, E0* A E0 y - R* E0 y>.
```

The expression on the right is bounded as a functional of `x`. Hence `y`
belongs to `dom A0*`, which equals `dom A0` by self-adjointness. This argument
is recorded here as mathematics, not as a newly compiled Lean lemma. The
manuscript uses only the already sufficient source-to-formal implication and
makes no strictness claim.

## Editorial changes

Section 3 now describes the formalization process and Section 4 introduces
the objects and worked theorem comparison. The skeptical-review paragraph
reports the scalar-family inconsistency directly, without an account of the
prompts that motivated it. The main text gives the norm identity, while the
appendix derives it from a one-dimensional example, the Gram operator, and
polar decomposition. Formalization 2's caption explicitly points to
Formalization 1's `hSinTheta0`.

The historical and current Lean signatures are preserved verbatim in their
exact generated sidecars. Module and theorem comments explain the same
objects. The paper-writing instructions no longer prescribe the superseded
sine-two-theta example or describe the current norm parameter by the stronger
record's name. The supplied workflow image is unchanged and the optional
dashboard image is not regenerated.

## Validation

Both anonymous and public PDFs build. Each has six main-text pages, with
references beginning on page 7, and 21 pages in total including references,
appendix, and the unchanged checklist. The repository's `check-prose` and
`check-layout` pass. Page images were inspected, including both complete
formalizations and the norm derivation. Natural page-bottom spacing prevents
equation and heading skips from stretching to fill gaps left by indivisible
code displays; the supplied workshop style file is unchanged.

A comment-aware comparison against the base commit confirms that the entire
modified Lean module has unchanged non-comment code, allowing only whitespace
normalization. Its SHA-256 is
`180defbfc6296225aac09e19690e6aa8e940b9f41e1d4dee88d72b100a472df6`.
The current theorem signature is byte-for-byte unchanged, and both exact
signature sidecars match their intended source versions.

Lean and Lake were not installed in the review environment. No fresh kernel
check is claimed. The overlay preserves the supplied proof code and changes
only its comments. Running the existing module build in the pinned project
environment remains the appropriate independent confirmation:

```bash
lake build DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
make -C papers/formalization_process paper public check-prose check-layout
```

The resource-accounting publisher ran and reported nothing to publish. No
resource measurements were invented or added.
