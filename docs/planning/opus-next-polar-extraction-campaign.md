# Opus next campaign: bounded polar extraction and nonacute Section 3

**Baseline:** `dfd9d37ebc86`  
**Owner:** Jon's agent, expected to resume with Opus  
**Parallel work:** Edward may continue Fable work on nonoverlapping lanes

## Mission

Build a Spectra-free, Tau Ceti-shaped bounded polar-decomposition foundation,
then use it to close the blocked nonacute direct-rotation mathematics in
Davis--Kahan Section 3.

This is both an extraction campaign and a mathematics campaign. Opus should
write and prove new reusable theorems when Spectra does not contain enough
infrastructure.

## Why this is the next campaign

The current nonacute Section 3 construction is close to completion but blocked
on a small number of genuinely foundational operator-theory facts:

- the adjoint/equivariance behavior of the polar partial isometry;
- positivity of canonical diagonal compressions;
- the reflection relation giving skew-adjoint crossed blocks;
- mapping of crossed defect spaces by an arbitrary paper direct rotation.

Spectra supplies a useful base construction but not all of these results. Its
polar files have a small enough dependency closure to be a realistic first
Tau Ceti extraction pilot.

## Source material and attribution

Primary donor files at Spectra commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`:

```text
Spectra/QuantumMechanics/Channels/PolarDecomp.lean
Spectra/QuantumMechanics/Channels/TraceClass/PartialIsometry.lean
Spectra/QuantumMechanics/Channels/TraceClass/Basic.lean
```

Original file author: Adam Bornemann.  
Original project copyright: Spectra Formalization Project.  
License: Apache-2.0.

Use the declaration mapping in:

```text
dev/upstream-extraction/polar-decomposition-provenance-dfd9d37.json
```

Update that ledger as declarations are renamed, generalized, or redesigned.

## Required output architecture

Create a separate reusable library boundary:

```text
TauCetiCandidates/
  Analysis/
    InnerProductSpace/
      PolarDecomposition/
        Basic.lean
        PartialIsometry.lean
        Equivariance.lean
        Compression.lean
        All.lean

DavisKahan/
  Interop/
    TauCeti/
      PolarDecomposition.lean
```

The exact split may change if compilation suggests a better boundary, but:

- candidate files must not import `Spectra`;
- candidate files must not import `DavisKahan`;
- paper-specific projection-pair facts stay in DavisKahan;
- each substantially adapted candidate file keeps an attribution header.

Add a `TauCetiCandidates` Lean library to `lakefile.toml` when the first module
is created. Do not make `external/TauCeti` a build dependency merely to compile
Mathlib-only candidate code.

## Phase 0: claim and certify the baseline

Before mathematical edits:

1. pull or inspect the latest branch state;
2. read `dev/LANES.md`;
3. ensure the polar campaign remains assigned to Jon;
4. run the default build;
5. run the relevant experimental builds;
6. record the exact baseline in a short journal entry.

Minimum commands:

```bash
lake build
lake build DavisKahan.Experimental.MathAhead.HiddenFoundations.PolarIsometryFinal
lake build DavisKahan.Experimental.MathAhead.HiddenFoundations.Section3Nonacute
lake build DavisKahan.Experimental.InfiniteDimensional.DirectRotation
```

The last targets may fail only at known proof leaves, not from unrelated import
breakage.

## Phase 1: extract the Spectra-free polar core

Adapt the minimal reusable mathematics from Spectra into candidate modules.
Expected initial surface:

- operator absolute value through `CFC.abs`;
- nonnegativity and self-adjointness of the absolute value;
- `|T|^2 = T^* T`;
- `norm (|T| x) = norm (T x)`;
- initial polar space as closure of the range of `|T|`;
- dense corestriction of `|T|`;
- partial isometry on the initial space;
- total polar partial isometry;
- `U |T| = T`;
- isometry on the initial space;
- contraction bounds;
- `U^* U` equals the initial projection;
- `U^* T = |T|`.

Do not import trace-class modules merely because the donor theorem currently
lives there. Move general polar mathematics to general operator-theory files.

Compile each candidate file independently before adapting DKPS consumers.

## Phase 2: complete reusable polar identities

Port or prove the following reusable results:

### Final space

- final polar space as closure of the range of `T`;
- the partial isometry has dense and then surjective range onto the final
  space;
- the initial-to-final linear isometric equivalence;
- `U U^*` equals the final projection.

The current DKPS proof in
`MathAhead/HiddenFoundations/PolarIsometryFinal.lean` is a source candidate,
but it must be moved out of the `Spectra` namespace and audited for general
placement.

### Adjoint and equivariance

Prove a robust theorem relating the polar factor of `T^*` to `U^*`. A valid
route may use uniqueness of the polar decomposition together with the initial
and final projection identities.

Also prove unitary/conjugation equivariance if it simplifies downstream
reflection arguments.

### Regularized polar factors

Develop the reusable approximation

```text
U_epsilon = T (|T| + epsilon I)^(-1), epsilon > 0.
```

Prove enough convergence to recover the polar partial isometry on its initial
support. Strong or pointwise norm convergence is sufficient for quadratic-form
applications; do not demand operator-norm convergence when zero is an
accumulation point.

This replaces the earlier invalid assumption that `|T|` always has a bounded
inverse on its support.

## Phase 3: canonical projection-pair algebra

In a DavisKahan-specific file, work with

```text
S = Q P + Q_perp P_perp
J_P = 2 P - I
J_Q = 2 Q - I.
```

Prove the algebraic identities before invoking functional calculus:

- `S = (I + J_Q J_P) / 2`;
- `S^* = J_P S J_P` and the analogous target-reflection identity;
- `S^* S` commutes with `P` and `J_P`;
- `|S|` commutes with `P` and `J_P`;
- the polar factor inherits the required reflection relation.

Use these results to prove the canonical crossed-block identity.

## Phase 4: prove diagonal compression positivity honestly

Do not introduce an unconditional bounded `positiveSupportInverse`.

Preferred route:

1. define regularized polar factors for `S`;
2. use commutation with `P` to identify the source diagonal compression;
3. show each regularized compression is positive;
4. pass to the polar factor using pointwise quadratic-form convergence;
5. repeat for the complementary compression by symmetry.

A different route is acceptable if it handles nonclosed range and spectrum
accumulating at zero.

Useful target identity to investigate:

```text
P U P = sqrt(P Q P)
```

interpreted on the source subspace or through a full-space compression. If this
is proved, positivity is immediate. Do not assert it without checking the exact
subspace/coercion formulation.

## Phase 5: audit `IsPaperDirectRotation`

Before constructing the converse crossed-defect equivalence, test whether the
current structure fields are strong enough.

Current diagonal fields state only:

```text
0 <= re <x, P T P x>
```

rather than a bundled positive-operator condition. Determine whether unitarity,
intertwining, and the crossed-block relation force the diagonal blocks to be
self-adjoint and positive.

Required behavior:

- a source-defect vector is mapped into the target defect;
- the adjoint maps the target defect back to the source defect.

If the current structure is too weak:

1. exhibit or outline a finite-dimensional counterexample;
2. strengthen the structure to the mathematically intended condition;
3. repair downstream constructors and statements explicitly;
4. record the statement change in the frontier census.

Do not bury the strengthening as a local hypothesis in the converse proof.

## Phase 6: close the nonacute Section 3 campaign

Target current leaves:

```text
adjoint_polarIsometry
canonicalPolarFactor_sourceCompression_nonnegative
canonicalPolarFactor_crossed_blocks_general
crossedDefectEquivOfPaperDirectRotation membership obligations
```

Then compile and certify:

```text
nonacuteDirectRotation_isPaperDirectRotation
exists_paperDirectRotation_of_crossedDefectsEquivalent
crossedDefectsEquivalent_of_exists_paperDirectRotation
proposition3_2_completed
proposition3_2_parameterization_completed
```

Migrate these files from direct Spectra imports to the candidate/adapter layer.

## Phase 7: acute direct-rotation follow-through

After the nonacute theorem is green, use the extracted polar core to close the
early isolated leaves in `InfiniteDimensional/DirectRotation.lean` where
reasonable:

- square and self-adjointness of the operator absolute value;
- canonical-intertwiner and absolute-value units for acute pairs;
- commutation with the source projection.

Treat these as follow-through, not as permission to start the separate Halmos
extremal campaign.

The following remain out of scope:

```text
directRotation_sq
directRotation_minimal
```

unless every preceding milestone is complete and the lane ledger remains free.

## Commit discipline

Use small commits with a green relevant build after each:

1. claim and baseline journal;
2. candidate `Basic` extraction;
3. candidate partial-isometry identities;
4. final-space and adjoint identities;
5. regularization/compression mathematics;
6. DKPS adapter;
7. Section 3 closure;
8. provenance and upstream-readiness cleanup.

Do not combine the full extraction and all downstream rewrites into one commit.

## Required verification

For each candidate module:

```bash
lake env lean TauCetiCandidates/.../File.lean
```

For the integrated campaign:

```bash
lake build TauCetiCandidates
lake build DavisKahan.Experimental.MathAhead.HiddenFoundations.Section3Nonacute
lake build DavisKahan.Experimental.InfiniteDimensional.DirectRotation
lake build DavisKahan.Experimental.GeometryAll
lake build
```

Run the frontier checker after source-facing promotion:

```bash
python3 scripts/check_davis_kahan_frontier.py --write-report
```

Inspect the axioms of every promoted headline declaration.

## Stop conditions

Stop and report rather than guessing when:

- a current statement is false or too weak;
- the required inverse is unbounded;
- a claimed Tau Ceti equivalent does not actually exist;
- a proof requires a major unrelated spectral theorem;
- another agent has claimed an overlapping declaration.

A useful stop report contains the smallest mathematically correct missing
lemma, its exact intended signature, and the evidence that the existing route
cannot work.

## Definition of success

This campaign is complete when:

- the reusable polar core compiles with no Spectra imports;
- its provenance is complete;
- the nonacute Proposition 3.2 construction and converse are grounded;
- the relevant DKPS files use the candidate/adapter layer;
- the retired polar Spectra imports are removed from those consumers;
- the normal build remains green;
- the candidate modules are organized for a future Tau Ceti contribution.
