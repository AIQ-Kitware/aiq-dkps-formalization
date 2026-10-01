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

The overlay also retains the generic symmetric-ideal transport lemmas
`gauge_modulus_eq`, `modulus_mem_iff`, and `gaugeReal_modulus_eq`, and preserves the
raw analytic endpoint as
`sinTheta_unbounded_formGap_rectangular_whereDefinedUIN_rclike`.

The fixed real and complex public specializations inherit the literal source-facing
conclusion.  `SectionTwo.sinTheta` therefore names `cfc sin Theta_0`, not a renamed
rectangular representative.

### Cleanup after the compile-fix pass

The compile-fix pass briefly produced a standalone
`ForTauCeti/Analysis/InnerProductSpace/SelfAdjointIdempotent.lean` theorem asserting that a
self-adjoint idempotent is contractive.  That file is not retained: the repository already
has the generic abstraction `IsStarProjection.norm_le`, and no consumer used the new theorem.
The useful part of the compile fix is the direct Pythagorean contraction proof for the
complementary block in `SineTheta/Presentation.lean`; keeping that proof local avoids
introducing closed-range/projection machinery into the downstream functional-calculus term.

The presentation module also imports the scalar-transport functional-calculus foundation
directly.  It does not depend on `OperatorAngleGeneric` merely to obtain local real-algebra
and functional-calculus instances.

## Trigonometric presentation status after the follow-up campaign

The stricter audit standard is now explicit: if the source theorem is written on
`f(Theta)`, the publication-facing Lean theorem should expose a literal functional-calculus
`f(Theta)` object.  Equality of norms, singular values, or approximation-number sequences is
not a substitute for that statement; it is the bridge by which the proof result is
transported to the source object.

### Section 2: `sin Theta`

**Presentation complete.**

`SectionTwo.sinTheta` is stated on `sourceDirectedSinThetaOperator`, literally `cfc sin` of
the trial-coordinate angle.  The rectangular cross-projection remains the analytic engine,
with an exact sine/modulus bridge.

### Section 2: directed `tan Theta_0`

**Presentation complete.**

`SectionTwo.tanTheta_directed` and its fixed-field specializations are stated on
`sourceDirectedTanThetaOperator = cfc tan Theta_0`.  The older existential rectangular
tangent remains the proof engine.  Equality of the complete approximation-number sequence is
proved and used to transport symmetric-norming membership and gauge.

### Section 2: directed and ambient `sin 2 Theta`

**Presentation complete.**

The ambient object was already literal functional calculus.  The directed public surface now
uses `sourceDirectedSinTwoThetaOperator = cfc (fun t => sin (2*t)) Theta_0`; an exact operator
identity connects it to the positive `2 sin Theta_0 cos Theta_0` object used by the analytic
proof.  Explicitly named block-representative theorems remain available as proof APIs.

### Section 2: directed `tan 2 Theta_0`

**Presentation complete.**

The public directed endpoint is now on the trial-side literal
`sourceDirectedTanTwoThetaOperator V U = cfc (fun t => tan (2*t)) Theta_0`.  The proof-facing
corner has the opposite block orientation `(U,V)`; the trial-side correspondence is proved by
complete approximation-number transport rather than treated as a rewrite.

### Section 2: ambient `tan Theta`

**Presentation complete.**

The existing scalar-generic theorem already exposed `Angle.HasDefinedTangent` and literal
`Angle.tanAngleOperator = cfc tan Theta`, so no representation change was needed.

### Section 2: ambient `tan 2 Theta`

**Presentation complete.**

The analytic endpoint remains on the positive branch-free `Angle.absTanTwoAngleOperator`.
The public endpoint is now on signed literal
`Angle.tanTwoAngleOperator = cfc (fun t => tan (2*t)) Theta`.  A proved exact identity
`absTanTwoAngleOperator = |tanTwoAngleOperator|` and modulus invariance transport ideal
membership and every symmetric-norming gauge.

### Proposition 6.1: ambient `sin Theta`

**Presentation complete.**

Both complex and real canonical Proposition 6.1 declarations, including the Appendix
common-domain presentations, now conclude on literal
`cfc Real.sin (Angle.angleOperator U V)`.  The complex positive sine and the real
projector-difference/cross-sine objects remain proof-facing representations.  The generic
identity `Angle.cfc_sin_angleOperator` plus complete approximation-number transport makes the
correspondence explicit.

### Section 4: direct-rotation source surface

**No analogous wrapper problem found in the sampled public surface.**

The source-oriented declarations in `Section4DirectRotationSource.lean` are stated in terms
of the direct rotation / source quantities they certify.  Proposition 4.4's repaired
statement is intentionally a different mathematical claim, not a representative of the
false printed inequality.

### Section 8: angle-order statements

**Presentation complete.**

The source's ambient angle is now exposed through the literal block-diagonal object
`fullAngleBlockC U V = diag(Theta_0, Theta_1)` over `C`, and `sourceFullAngleR U V` over
`R`.  The presentation layer states the paper's comparisons directly on those operators:

* `sourceFullAngleLeC U V c` means the real spectrum of the literal source `Theta` lies in
  `(-infinity, c]`, i.e. the spectral-order reading of `Theta <= c`;
* `sourceFullAngleLtC U V c` means every spectral angle of that same literal `Theta` is
  strictly below `c`;
* `sourceFullAngleLeR` / `sourceFullAngleLtR` are the real-source complexification forms.

`SineTheta/FullAnglePresentation.lean` proves, rather than assumes, that these direct source
conditions are equivalent to the norm bounds on the positive source angle and then to the
scalar proof representation `maximalAngle`.  In particular it proves

`‖fullAngleBlockC U V‖ = maximalAngle U V`

and the real analogue.  It also proves that the literal source full angle and the modern
intrinsic `Angle.angleOperator` have the same exact maximal-angle norm.  More strongly, for
every nonnegative threshold `c`, `sourceFullAngleLeC U V c` is equivalent to the intrinsic
angle's spectrum lying in `(-infinity, c]`, with the analogous theorem for strict `< c`.
The two operators live on different coordinate Hilbert spaces, so raw equality is not a
well-typed statement; these threshold-equivalence theorems make the correspondence used by
Section 8 explicit instead of identifying them by notation.

The canonical Theorem 8.1 characterization and uniqueness façades now use
`sourceFullAngleLeC ... (pi/4)` directly.  The Theorem 8.1 existence conclusions carry
`sourceFullAngleLtC` / `sourceFullAngleLtR` alongside the scalar proof representative.  The
canonical complex and real Theorem 8.2 statements likewise conclude with the direct strict
source-angle predicates.  Named `maximalAngle`, norm, and directed-gap results remain
available underneath as proof-facing APIs.

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

## Remaining presentation work

No further proxy-versus-source-object defect remains among the public surfaces surveyed here.
The trigonometric campaign and the Section 8 quarter-angle campaign are both closed.  The
generalized Section 6 representative freedom remains intentional because the source itself
permits singular-value representatives.

A future audit may still find ordinary naming or ergonomics improvements, but those should not
be conflated with the semantic defect targeted here.  The recurring design rule is: the source
theorem names the mathematical object the paper names; representation-changing equalities and
singular-value transport belong immediately below that surface, and the analytic proof may
continue to use whichever block is most convenient.
