# Full Part III Experimental closure — 2026-07-21

Base commit: `cb1d6ab1b3db43ccc26823677be5969bec0498ab`

## Decision

The executable development no longer carries an active/parked split.  The
finite coordinate mathematics is retained and completed.  The old
infinite-dimensional scalar-generic facade is retired because its central
operator-square-root signature is not validly constructible on an arbitrary
possibly incomplete `RCLike` inner-product space.

This is not a deletion of the supported ambient theory.  The repository already
contains the canonical replacements:

* complete complex operator angles in
  `DavisKahan/Geometry/Angle/OperatorAngleComplex.lean`;
* real operator angles through complexification in
  `DavisKahan/Geometry/Angle/OperatorAngleReal.lean`;
* literal paper angle operators in
  `DavisKahan/Geometry/Angle/PaperOperatorAngle.lean`;
* finite coordinate sine, cosine, tangent, and double-angle maps in
  `DavisKahan/FiniteDimensional/Residual/AngleEmbedding.lean` and
  `DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean`;
* complex bounded PVM and contour identification through the vendored Spectra
  continuation modules;
* real spectral projections and restrictions in
  `DavisKahan/SpectralTheory/Real/SpectralRestriction.lean`;
* the accepted unbounded sine-theta chain in the production Spectra route;
* bounded complex tan-two-theta and Riccati theory under
  `DavisKahan/TanTwoTheta/` and `DavisKahan/Riccati/`.

## Mathematical corrections

### Incomplete scalar-generic positive square roots

A bounded positive square root on `E →L[𝕜] E` requires a complete ambient
operator algebra.  The pinned continuous functional calculus supplies the
needed C-star-algebra structure for complete complex Hilbert spaces, not for an
arbitrary incomplete `RCLike` space.  Completion does not automatically give an
operator preserving the original dense incomplete subspace.  The old generic
signature therefore could not be implemented by a canonical restriction.

The correct architecture keeps separate complete-complex and
real-complexification implementations.

### Finite tangent perturbation

The historical graph proof mixed four incompatible spaces:

* ambient endomorphisms of `E`;
* subtype graph maps `U → Uᗮ`;
* trial-coordinate maps `F → E`;
* square and rectangular unitarily invariant norms.

The active theorem is now the rectangular coordinate result

`δ N(S |C|⁺) ≤ N(AX - XM)`,

under the ordered gap between the Ritz operator `M` and the unwanted exact
spectrum.  It is backed by the proved singular-value identification of the
coordinate tangent.

### Finite tan two theta

The removed historical family mixed finite block algebra with contour branch
selection and asserted arbitrary-UI identities between one-sided coordinate
maps and full-space positive angle operators.  Those identities are false in
general because the full-space operator duplicates nonzero principal-plane
multiplicities.  The canonical coordinate definition

`(2 S |C|) (C⋆C - S⋆S)⁺`

is retained.  Supported bounded complex operator-norm tan-two-theta theorems
remain in the production tree.

## Preservation

The complete pre-retirement contents of every rewritten compatibility file are
stored byte-for-byte in deterministic gzip archives under
`dev/retired-full-part-iii-ambient-route-2026-07-21/`.  They remain available
for theorem archaeology without participating in the executable Lean import
graph.

## Executable contract

The guarded compiler contract now covers the 39 completed finite declarations
that remain part of the math-ahead batch.  Rewritten compatibility and aggregate
modules are listed as additional compilation modules.  The Experimental root
registry contains zero active and zero parked roots.

The reduction from 173 guarded declarations is intentional: the removed entries
were not accepted theorems.  They belonged to an unsupported or mathematically
incorrect historical route.  Counting them as guarded proof debt would continue
to misrepresent the state of the executable development.
