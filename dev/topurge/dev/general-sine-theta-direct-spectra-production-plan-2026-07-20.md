# Direct-Spectra production closure and remaining reorganization

Base state: `54dfcb877deefd10e7740e48538ed7aa1f66fe98`, after the compiler agent
made the full source audit clean at 43 exact axiom reports and made
`DavisKahan.All` green.

This note supersedes the final "structural check 2 is blocked on mathematics"
conclusion in `dev/sine-theta-move-manifest-2026-07-20.md`.

The generic legacy truncation API is indeed unproved.  However, the production
source route does not need to use that API.  The repository already contains a
complete direct proof from the vendored Spectra calculus.  Its declarations are
module-tainted by coarse historical imports, not logically dependent on the
admitted truncation declarations.  The remaining task is declaration
extraction and import cleanup, not proving all 31 obligations in
`Core/UnboundedSpectral.lean`.

## Immutable baseline

Do not regress any of these:

1. `lake env lean DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean`
2. `lake env lean DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean`
3. `lake build DavisKahan.All`
4. `python3 scripts/audit_full_paper_sine_theta.py`

The audit must continue to produce exactly the allowed axiom set for all 43
reports.  Do not weaken its parser, target count, output-exhaustiveness check,
or negative tests.

## Batch completed by this overlay

Twenty-two modules whose whole import closures were already admission-free are
moved out of `Experimental` with `git mv`:

- approximation-number infrastructure into
  `DavisKahan/OperatorIdeal/ApproximationNumbers/`;
- source norm transport and literal-angle modules into
  `DavisKahan/Sources/DavisKahan1970/SineTheta/`;
- frame factorization into `DavisKahan/SinTheta/`;
- Spectra adapters into `DavisKahan/Interop/Spectra/`;
- bounded and pairwise-homogeneous Sylvester results into
  `DavisKahan/Sylvester/`.

The corresponding production aggregates are updated.  Structural check 3 must
remain green from this point forward.

The ordinary Lake build now targets `DavisKahan.All`.  The explicit nondefault
`DavisKahan.Experimental` root is the admission quarantine/API test bed.

## Correct dependency direction

The intended native dependency order is:

```text
Mathlib
  -> ForMathlib
  -> vendor/Spectra
  -> DavisKahan/Interop/Spectra
  -> DavisKahan mathematical theory
  -> DavisKahan/Sources
```

`ForMathlib` may never import `vendor/Spectra` or `DavisKahan`.  If a locally
improved Spectra result is genuinely general and can be made Mathlib-only, move
it to `ForMathlib` and preserve its Spectra provenance in the file comments.
Otherwise retain it as vendored or interoperability code.

For the future Lean Pool export, preserve the transparent paths:

```text
LeanPool/DavisKahan/Vendor/Spectra/...
LeanPool/DavisKahan/ForMathlib/...
```

## The direct proof path already present

The following proof-complete modules form the replacement for the legacy
admitted interval/exterior path:

1. `SpectraBridge/BoundedFromSpectrum.lean`
   proves `exists_boundedRealization_of_spectrum_subset_Icc` directly from the
   Spectra PVM and generator calculus.
2. `SpectraBridge/GapResolvent.lean`
   constructs the sharp bounded shifted inverse directly from a Spectra
   spectrum gap.
3. `SpectraBridge/UnboundedIntervalExterior.lean`
   proves both interval/exterior orientations of the ideal-gauge Sylvester
   estimate.
4. `Sylvester/GenuineAllGap.lean`
   combines interval/exterior and ordered gaps.
5. `Sylvester/LegacyGapCompletion.lean`
   translates the old `realSpectrum` statement through
   `Interop/Spectra/RealSpectrumBridge.lean` and invokes the direct engine.
6. `SinTheta/LegacyGapCompletion.lean`
   exposes the source-shaped complex theorem from that engine.

Do not replace these proofs with calls to the admitted declarations in
`Core/UnboundedSpectral.lean`.

## Ordered extraction

Compile after every numbered item.  Use one canonical declaration throughout:
move or extract and delete the old declaration; do not maintain duplicate
copies under production and Experimental paths.

### 1. Extract the clean closed-operator spectral data

Move these proof-free or proof-complete declarations out of
`Core/UnboundedSpectral.lean`:

- `BoundedRealization` ->
  `DavisKahan/SpectralTheory/ClosedOperator/BoundedRealization.lean`;
- `UnboundedIntervalExteriorGap` -> `DavisKahan/Sylvester/Gap.lean`;
- `HasUnboundedBoundedSylvesterEquation` ->
  `DavisKahan/Sylvester/Unbounded/Equation.lean`;
- `sylvester_mem_and_gauge_le_of_unbounded_bound_inverse`,
  `closedSylvesterEquation_boundedRealization`, and
  `mem_and_gauge_le_of_boundedLeft_exteriorRight` ->
  `DavisKahan/Sylvester/Unbounded/Neumann.lean`.

These three long proofs are complete.  Their present module is tainted only
because admitted spectral declarations occur earlier in the same file.

Leave `spectralCutoff`, `boundedSpectralTruncation`,
`boundedRealization_of_spectrumIn_Icc`, and
`boundedInverse_of_spectrumOutside` in Experimental.  They remain a useful API
test bed but are not the production implementation.

### 2. Extract the gap statement

Move `UnboundedSylvesterGap` from `Sylvester/Unbounded.lean` to
`DavisKahan/Sylvester/Gap.lean`.  Keep the old theorem wrappers that invoke the
admitted generic truncation implementation in Experimental.

### 3. Split bounded and unbounded sine-theta cores

`SinTheta/Bounded.lean` mixes clean problem data and angle-identification
lemmas with endpoint theorems that call the admitted legacy estimate.  Move the
clean declarations into production modules, including:

- `generalResidual`;
- `adjoint_residual_block_identity`;
- `complementary_sylvester_equation`;
- `OrthogonalExactDecomposition`;
- `directedSinThetaOperator` and its isometry/ideal transport lemmas.

Leave `complementaryBlock_mem_and_gauge_le`, `sinTheta_bounded`, and every
wrapper whose proof calls the admitted legacy theorem in Experimental until it
is repointed to the direct engine.

Likewise extract from `SinTheta/Unbounded.lean`:

- `UnboundedSinThetaData`;
- `unbounded_adjoint_residual_block_identity`;
- `adjointResidualBlock_mem_and_gauge_le` if its closure is clean after the
  previous splits.

Suggested destinations:

```text
DavisKahan/SinTheta/Bounded/Core.lean
DavisKahan/SinTheta/Unbounded/Core.lean
```

### 4. Promote the direct Spectra implementation

After steps 1-3 remove their coarse imports, then move:

```text
Experimental/.../SpectraBridge/BoundedFromSpectrum.lean
  -> DavisKahan/Interop/Spectra/BoundedFromSpectrum.lean
Experimental/.../SpectraBridge/GapResolvent.lean
  -> DavisKahan/Interop/Spectra/GapResolvent.lean
Experimental/.../SpectraBridge/UnboundedIntervalExterior.lean
  -> DavisKahan/Sylvester/Unbounded/IntervalExterior.lean
Experimental/.../Sylvester/GenuineAllGap.lean
  -> DavisKahan/Sylvester/Unbounded/AllGap.lean
Experimental/.../Sylvester/LegacyGapCompletion.lean
  -> DavisKahan/Sylvester/Unbounded/LegacyGap.lean
Experimental/.../SinTheta/LegacyGapCompletion.lean
  -> DavisKahan/SinTheta/Unbounded/LegacyGap.lean
```

`GapResolvent.lean` currently imports `GenuineUnbounded` and
`GenuineUnboundedGauge` only to obtain clean shifted-inverse predicates and
endpoint wrappers.  Split those modules as needed:

- shifted-inverse predicates and form-bound lemmas belong in
  `DavisKahan/Sylvester/ShiftedInverse.lean`;
- source-independent sine-theta endpoints belong under
  `DavisKahan/SinTheta/Unbounded/`;
- no production module may import the admitted generic truncation files.

### 5. Repoint generalized source facades

Only after the preceding closures are clean, move/repoint the clean complex,
real, natural-input, specialization, and reducing-subspace modules currently
reached by:

- `Sources/DavisKahan1970/GeneralSinTheta.lean`;
- `Sources/DavisKahan1970/GeneralSinThetaExtensions.lean`.

If a source file contains both clean aliases and aliases whose declarations
still depend on admissions, split it.  The admission-dependent aliases remain
under `DavisKahan.Experimental`; the clean source facade remains production.
Do not solve structural check 2 by hiding a genuine dependency or adding an
exemption.

### 6. Move the rest of the literal paper layer

The 43 audited endpoints are declaration-level clean, but several enclosing
files remain module-tainted.  After the core extraction, move the remaining
`Paper*.lean` modules to:

```text
DavisKahan/Sources/DavisKahan1970/SineTheta/
```

Update the audit paths only.  Preserve all 43 targets and exact axiom checks.
`FullSineTheta.lean` must then import only production modules.

### 7. Split the overbroad FullPartIII facade

`FullPartIII.lean` currently imports three entire Experimental aggregates and
therefore cannot be a production facade.  Replace aggregate imports with the
specific admission-free modules actually required by each alias.  Move any
remaining aliases whose declarations depend on admissions into an explicit
Experimental extension facade.  Do not import `Experimental.*.All` from a
source-facing production module.

### 8. Finish indexes and correspondence matrix

Every production directory containing Lean modules should have an import-only
`All.lean`.  Update `DavisKahan.All`, `DavisKahan`, and the source indexes.
Create a source correspondence matrix covering Lemmas 6.1/6.2, Theorem 6.1,
Proposition 6.1, Theorem 6.2, common-domain/core forms, equality, optimality,
finite multiplicity, and the counterexample.  Every row now has a compiled and
audited declaration; record exact names and hypotheses rather than qualitative
claims.

## Required final commands

```bash
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/check_library_structure.py
```

Acceptance requires:

- ordinary `lake build` builds every claimed production module;
- `DavisKahan.All` is green;
- the explicit Experimental target compiles with its admitted APIs but is not a
  default target;
- the full-paper audit remains CLEAN with at least all 43 reports and the exact
  allowed axiom set;
- all five structural checks are green;
- no production module imports Experimental;
- every Experimental module contains an admission in its closure;
- no theorem statement is weakened and no audit check is exempted.
