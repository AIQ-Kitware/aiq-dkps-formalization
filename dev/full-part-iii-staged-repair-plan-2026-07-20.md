# Corrected staged repair plan for full Davis--Kahan Part III

Base: `3c26fd2bfe18083f104880b209a74fb7470e694b`.

## Correction to the previous batch

The historical bodies preserved exact theorem statements, but absence of an
unfinished proof token did not imply compilation.  Twenty-seven of the twenty-
eight changed modules fail to build, with hundreds of surfaced errors and more
hidden behind failed prerequisites.  The previous static checker therefore
certified only syntax-level properties while using the word `CLEAN` too
strongly.

The checker now has two modes:

- default: preserve all signatures **and compile** the restored modules;
- `--static-only`: preserve signatures and scan proof markers, reporting
  `STATIC CLEAN` and explicitly saying compilation was not checked.

Use exit status.  Never summarize the batch as complete from the static mode or
from the textual debt inventory.

## Decision

Proceed with **compiler-gated repair plus new infrastructure**, in staged
batches.

The former instruction against creating parallel APIs is replaced by this
rule:

1. Search current Mathlib, production Davis--Kahan, and vendored Spectra first.
2. If a canonical equivalent exists, rewrite the historical proof to it.
3. If no equivalent exists and the construction is mathematically general or
   required by a source-paper theorem, build the smallest reusable API in a
   canonical module.
4. Do not create a private compatibility shim whose only purpose is to make one
   stale body elaborate.
5. If a proposed abstraction is neither paper-required nor independently
   useful, remove the dependent speculative declaration only after a recorded
   reference and source-correspondence audit.

This explicitly authorizes real new mathematics where the library is genuinely
missing it.

## Classification of never-existing APIs

### Build as general reusable infrastructure

#### Finite-dimensional self-adjoint functional calculus

Needed by `FiniteDimensional/Core/AngleOperators.lean` for `arcsin`, tangent,
and double-tangent angle operators.  The correct construction is diagonal
functional calculus from `LinearMap.IsSymmetric.eigenvectorBasis` and
`eigenvalues`.  It should support at least:

- application to an arbitrary real scalar function;
- action on eigenvectors;
- linearity in vectors;
- preservation of symmetry for real-valued functions;
- composition and pointwise-equality lemmas needed for angle identities.

Place it under `ForMathlib/Analysis/InnerProductSpace/`, not inside the
Davis--Kahan angle file.

#### Finite-dimensional Moore--Penrose inverse

Needed by tangent maps and residual embeddings.  Define it coordinate-free:
restrict a map to the orthogonal complement of its kernel, identify that
restriction with its range, invert it, project the input onto the range, and
extend by zero.  Required endpoints include:

- kernel and range behavior;
- `A A⁺ A = A` and `A⁺ A A⁺ = A⁺`;
- self-adjoint projection identities for `A A⁺` and `A⁺ A`;
- equality with the true inverse on the injective/surjective branch;
- the existing `inverseOnRange` bridge used by tangent proofs.

This is broadly Mathlib-worthy and may reuse the restriction/inversion pattern
already used in `ForMathlib.Analysis.InnerProductSpace.PolarDecomposition`.

### Rewrite onto existing canonical infrastructure

- `RCLikeUnboundedSpectralTheorem.*`: use the production Spectra PVM,
  functional-calculus, bounded-realization, and spectral-restriction bridges.
  Do not implement a second unbounded spectral theorem.
- `HilbertSchmidt` and `SchattenClass` placeholder types: use the production
  approximation-number, paper Hilbert--Schmidt, Frobenius, and rectangular
  symmetric-ideal APIs.  Introduce a Schatten family only if a source theorem
  or independent roadmap target actually requires it.
- `Contour.Rectifiable`: use the completed proof-carrying continuation contour,
  transport, spectral-identification, subdivision, and rotation-chain stack.
- `RiccatiEquation`: use or minimally generalize the current bounded/unbounded
  Riccati structures and graph-reduction APIs.

### Build only if full-paper correspondence requires it

- `ForMathlib.DavisKahanExt.ClosedForm.*` and the KLMN/first-representation
  layer are major independent developments.  Before implementing, map every
  dependent endpoint to the paper.  Build the layer if it is needed for an
  exact unbounded/form theorem or is accepted as a separate Tau Ceti roadmap
  target; otherwise keep those declarations explicitly unfinished rather than
  creating an isolated form library opportunistically.

## Staged compile order

### Stage 0 -- contract repair

Run:

```bash
python3 scripts/check_full_part_iii_math_ahead.py --static-only
python3 scripts/check_full_part_iii_math_ahead.py
```

The first must report `STATIC CLEAN`; the second is expected to fail until the
modules actually compile.  This verifies that the false-clean mode is gone.

### Stage 1 -- finite-dimensional foundations

1. self-adjoint functional calculus;
2. Moore--Penrose inverse and inverse-on-range bridge;
3. `FiniteDimensional/Core/AngleOperators.lean`;
4. `FiniteDimensional/Norms/Rectangular.lean`;
5. `FiniteDimensional/Residual/AngleEmbeddings.lean`.

Then repair the finite dependents in topological order: double angle, graph
tangent, sharpness, direct rotation, and generalized theorem files.

### Stage 2 -- clean rewrites over production spectral infrastructure

Repair `AbstractSpectrum`, `OperatorAngle`, and `SpectralProjection` by replacing
historical fictional namespaces with production Spectra bridges.  Do not start
from `UnboundedSpectral.lean`; it is a legacy API test bed and must not become a
new foundation.

### Stage 3 -- operator ideals

Rebase `Rectangular`, `Symmetric`, and `CompactAndSingular` onto the production
approximation-number and rectangular ideal family.  Separate actual Schatten
mathematics from placeholder type names.

### Stage 4 -- Sylvester, double angle, direct rotation, continuation

Repair by consuming the now-green foundations.  Reuse the completed source
Section 6 path and the completed continuation stack.  Keep alternative proofs
only when they are mathematically independent and non-circular.

### Stage 5 -- forms and remaining unbounded extensions

Perform a paper-correspondence audit first.  Implement the closed-form/KLMN
layer only for endpoints retained by that audit or as an explicitly approved
independent contribution.

### Stage 6 -- promotion

After each module compiles and its entire import closure is trusted:

- move it out of Experimental;
- split mixed files rather than leaving complete declarations quarantined;
- regenerate aggregates;
- require the structural checker to return CLEAN, 5/5.

## Per-module acceptance

For a module under repair:

```bash
python3 scripts/check_full_part_iii_math_ahead.py \
  --module DavisKahan/Experimental/.../Target.lean
```

This preserves all 174 statements and invokes Lean on the named module.  A
successful static-only run is never sufficient.

## Global acceptance

```bash
python3 scripts/check_full_part_iii_math_ahead.py
python3 scripts/generate_all_aggregates.py --check
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/inventory_davis_kahan_debt.py --json
python3 scripts/check_library_structure.py
```

The textual inventory must be reported only as an admission count.  The
compiler contract and Lake builds determine whether the proof debt is actually
closed.
