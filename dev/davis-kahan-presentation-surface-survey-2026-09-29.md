# Davis--Kahan presentation-surface survey — 2026-09-29

## Question

Which publication-facing Davis--Kahan theorems still expose a proof representative
when the repository already has, or is close to having, the mathematical object named
in the source?

The criterion used here is narrow.  An implementation theorem may use blocks,
projector differences, polar representatives, or singular-value representatives.
A theorem presented as the source result should prefer the source object when a
stable definition and a proved bridge already exist.  The implementation theorem
should remain available under a name that advertises its representation.

This is a static API survey.  It does not claim compiler validation of the changes in
this overlay.

## Updated in this overlay

### Section 2: `sin Theta_0`

**Status before:** presentation inversion.

The ledger-selected theorem
`sinTheta_unbounded_formGap_whereDefinedUIN_rclike` originally concluded directly
on the rectangular complementary-projection block

`(I - F0 F0*) E0 : F -> E`.

The first presentation overlay improved the theorem statement by replacing that block
with its positive modulus, but that still defined the source object by the proof
representative.  This revision moves the API one level higher and expresses the angle
itself.

The source-facing layer now contains:

- `sourceDirectedSineBlock E0 F0`, the rectangular analytic block;
- `sourceDirectedSineModulus E0 F0 = |sourceDirectedSineBlock E0 F0|`;
- `sourceDirectedThetaOperator E0 F0 = cfc Real.arcsin sourceDirectedSineModulus`;
- `sourceDirectedSinThetaOperator E0 F0 = cfc Real.sin sourceDirectedThetaOperator`.

For isometric trial and exact coordinate maps,
`sourceDirectedSinThetaOperator_eq_modulus` proves that this literal functional-
calculus `sin Theta_0` equals the modulus of the rectangular block.  Thus the public
result is now genuinely stated on `sin Theta_0`, while the Sylvester proof remains on
the representation best suited to the analytic argument.

This convention matches `SineTheta/OperatorAngleBridge.lean`, where the literal
directed angle is reconstructed from the positive sine on `[0, pi/2]`.  The canonical
subspace development in `SineTheta/AngleIdentity.lean` proves that this sine-defined
angle is exactly the cosine-defined `arccos |C0|` angle used by Davis and Kahan.

**Compiler status (2026-09-30).**  The overlay above now compiles: the whole
`DavisKahan` and `ForTauCeti` default build is green with the file building in
about 11 s at the default heartbeat, with no `set_option maxHeartbeats` bump.  The
earlier build failure (a kernel `whnf` timeout above 1,000,000 heartbeats on the
`spectrum` containment theorem) was diagnosed as an instance-search explosion:
the spectrum theorems need a `NormedAlgebra ℝ (F →L[𝕜] F)` instance, which
Mathlib does not provide for operator endomorphisms; synthesizing the missing
instance forced the search to normalize the whole instance database, including
the heavy functional-calculus constants.  The fix is the local
`realNormedAlgebra` instance in the file (the established `Proposition35`
pattern), plus a lighter Pythagorean proof of the contraction bound
`‖sourceDirectedSineModulus E₀ F₀‖ ≤ 1`.  All public names and statements in
this section of the survey are unchanged.

The overlay also retains the generic symmetric-ideal transport lemmas
`gauge_modulus_eq`, `modulus_mem_iff`, and `gaugeReal_modulus_eq`, and preserves the
raw analytic endpoint as
`sinTheta_unbounded_formGap_rectangular_whereDefinedUIN_rclike`.

The fixed real and complex public specializations inherit the literal source-facing
conclusion.  `SectionTwo.sinTheta` therefore names `cfc sin Theta_0`, not a renamed
rectangular representative.

## Already in the preferred presentation form

### Section 2: directed and ambient `sin 2 Theta`

**No action recommended.**

The scalar-generic public API already concludes on
`Angle.directedSinTwoAngleOperator` for the directed clause and on the corresponding
ambient angle object for the ambient clause.  The block-representative theorems are
separately named as such.  This is the pattern the Section 2 `sin Theta` change now
follows.

### Section 2: ambient `tan Theta`

**No action recommended.**

`tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_rclike` exposes
`Angle.HasDefinedTangent` and concludes on `Angle.tanAngleOperator`.  Pole/definedness
is part of the mathematical statement rather than hidden in a block representation.

### Section 2: ambient `tan 2 Theta`

**No action recommended.**

`tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike` concludes on the
generic branch-free `Angle.absTanTwoAngleOperator`.  The representation used in the
proof is not exposed as the source object.

### Section 4: direct-rotation source surface

**No analogous wrapper problem found in the sampled public surface.**

The source-oriented declarations in `Section4DirectRotationSource.lean` are already
stated in terms of the direct rotation / source quantities they certify.  The lower
level singular-value and compact-operator lemmas remain visibly implementation
oriented.  Proposition 4.4's repaired statement is also intentionally a different
mathematical claim, not a representative of the false printed inequality.

### Section 8: canonical branch selection

**No analogous wrapper problem found.**

The publication-facing API explicitly names the canonical branch and its uniqueness
property.  Internal block/eigenvalue constructions are supporting theorems rather
than the object exposed as the paper theorem.

## Presentation candidates for follow-up

### High priority: Proposition 6.1 over `R`

`proposition6_1_complex` already concludes on the paper's literal ambient sine,
`sinAngleOperatorC U V`.

`proposition6_1_real`, however, still concludes on

`V.starProjection - U.starProjection`.

That was a reasonable representation while the real development lacked the relevant
functional-calculus surface.  The generic angle API now defines

`Angle.sinAngleOperator U V = |P_U - P_V|`

for arbitrary `RCLike`, including `R`.  This makes the real Proposition 6.1 theorem a
close analogue of the Section 2 issue repaired here.  A source-facing real theorem
should be stated on `Angle.sinAngleOperator U V`, with the projector-difference
estimate retained as an explicitly named implementation/transport theorem.  The
modulus gauge lemmas added by this overlay should make that transport short.

A stronger cleanup would make both fixed-field Proposition 6.1 statements thin
specializations of one scalar-generic source theorem on `Angle.sinAngleOperator`.

### Medium priority: directed `tan Theta_0`

`tanTheta_directed_unboundedRitz_symmetricNorming_exists_rclike` constructs an
existential operator `tanTheta0 : Z -> E` and characterizes it only through
`HasDirectedTangentApproximationNumbers`.

This is mathematically stronger than accepting an arbitrary caller-supplied
representative, but the publication-facing conclusion still lacks a named canonical
directed tangent object.  The ambient tangent side already has such an object.

Recommended follow-up: determine whether the pole-exclusion hypotheses support a
scalar-generic canonical directed tangent operator on trial coordinates.  If so,
state the public theorem on that operator and retain the approximation-number
existence theorem as the construction/transport layer.  This needs a design pass;
it is not only a renaming exercise.

### Medium priority: directed `tan 2 Theta_0`

`tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike` similarly
constructs an existential corner `T : U -> U^perp` satisfying
`HasDirectedDoubleTangentApproximationNumbers`.

The directed `sin 2 Theta_0` API already has a canonical angle object, so the tangent
surface is now the asymmetric member of the pair.  A future presentation theorem
should prefer a named directed double-tangent object if its pole/branch semantics can
be encoded canonically.  Keep the current existential theorem as the construction
engine.

### Low priority / ergonomic, not a fidelity defect: Theorems 6.1 and 6.2

The component-level generalized sine theorem accepts a
`SinThetaRepresentativeAcross` whose complete singular-value sequence agrees with the
canonical directed sine construction.  This is intentional: the source's UIN
statement is invariant under the choice of Hilbert coordinate realization, and the
representative structure records exactly that freedom.  Its `.canonical` constructor
already gives a preferred realization.

For publication ergonomics, a thin theorem that chooses `.canonical` automatically
could make the common statement easier to read.  The existing representative theorem
should remain because it captures genuine source-level invariance and is useful for
transport across coordinate spaces.  This is not the same source-fidelity problem as
the former Section 2 `sin Theta` headline.

## Recommended order

1. Compile-test the Section 2 `sin Theta` overlay and keep the public name on the
   positive source operator.
2. Apply the same source-object/representation-bridge pattern to real Proposition 6.1,
   preferably through one scalar-generic `Angle.sinAngleOperator` theorem.
3. Design canonical directed tangent objects before changing either directed tangent
   public theorem.
4. Add optional canonical convenience wrappers for Theorems 6.1/6.2 only if they
   materially improve the paper-facing signatures.

The recurring design rule is simple: the source theorem should name the mathematical
object the paper names; representation-changing equalities and singular-value
transport belong immediately below that surface, and the analytic proof may continue
to use whichever block is most convenient.
