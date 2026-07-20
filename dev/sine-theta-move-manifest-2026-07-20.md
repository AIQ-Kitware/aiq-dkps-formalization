# Move manifest for the sine-theta reorganization

Written for step 8 of `dev/flawless-sine-theta-reorganization-overnight-plan-2026-07-20.md`,
which requires an inventory and a written manifest *before* any bulk move.

Measured at commit `cc7a7fc`, after the full-paper sine-theta audit first
reported CLEAN. Reproduce with `scripts/inventory_admission_closure.py`.

## Measured state

| quantity | value |
| --- | --- |
| local modules (`DavisKahan/` + `ForMathlib/`) | 362 |
| modules carrying their own admission | 28 |
| modules in the module-level admission closure | 235 |
| modules reachable from the curated roots `DavisKahan.lean` + `ForMathlib.lean` | 88 |
| modules **not** reachable from those roots | 274 |
| Experimental modules built by an ordinary `lake build` | **0** |
| import closure of the audited facade | 141 modules |
| admission-bearing modules inside that closure | 13 (108 admissions) |

## Finding 1: the ordinary build does not cover the audited surface

`lake build` runs 8828 jobs and builds **zero** Experimental modules. The
`[[lean_lib]]` entries in `lakefile.toml` carry no `globs`, so each library
builds only its root module and that root's transitive imports.

Consequently the entire audited paper surface — Lemma 6.1, Lemma 6.2,
Theorem 6.1, Proposition 6.1, Theorem 6.2, the common-domain and graph-core
appendix forms, the sharpness results and the printed counterexample — is
**not** covered by an ordinary build. Only `scripts/audit_full_paper_sine_theta.py`
builds it, via an explicit `lake build DavisKahan.Sources.DavisKahan1970.FullSineTheta`.

`DavisKahan/All.lean` already exists and already documents the intended
"everything claimed" role, but it is not a default target either, so nothing
builds it.

This is exactly the condition plan item 11 exists to fix.

## Finding 2: the paper layer cannot be moved with `git mv`

All 20 paper-layer modules are inside the module-level admission closure, while
all 38 audited declarations are axiom-clean (`propext`, `Classical.choice`,
`Quot.sound` only).

That gap is the whole problem. Declaration-level cleanliness is what the audit
certifies; module-level cleanliness is what structural checks 2 and 3 require.
Moving the paper layer to `DavisKahan/Sources/DavisKahan1970/SineTheta/` as a
pure rename would import Experimental from the production tree.

The taint enters through 13 modules in the facade's import closure:

| admissions | module |
| ---: | --- |
| 31 | `Experimental/InfiniteDimensional/Core/UnboundedSpectral` |
| 15 | `Experimental/InfiniteDimensional/Core/SpectralProjection` |
| 14 | `Experimental/InfiniteDimensional/Core/OperatorAngle` |
| 8 | `Experimental/InfiniteDimensional/Ideals/Symmetric` |
| 6 | `Experimental/InfiniteDimensional/DirectRotation` |
| 6 | `Experimental/InfiniteDimensional/Core/Unbounded` |
| 5 | `Experimental/InfiniteDimensional/Sylvester/Resolvent` |
| 5 | `Experimental/InfiniteDimensional/SinTheta/General` |
| 5 | `Experimental/InfiniteDimensional/Ideals/Rectangular` |
| 4 | `Experimental/InfiniteDimensional/Sylvester/Basic` |
| 4 | `Experimental/InfiniteDimensional/SinTheta/SpectralBridge` |
| 4 | `Experimental/InfiniteDimensional/DoubleAngle` |
| 1 | `Experimental/InfiniteDimensional/Core/AbstractSpectrum` |

Three foundational modules carry 60 of the 108. Because they sit near the base
of the import graph, they taint nearly everything above them.

## Finding 3: the admissions are interleaved, not tails

A textual "cut the admitted tail" split does not work. Position of the first
and last admission within each file:

| module | lines | adm | first | last |
| --- | ---: | ---: | ---: | ---: |
| `UnboundedSpectral` | 1122 | 31 | 22% | 54% |
| `SpectralProjection` | 434 | 15 | 21% | 99% |
| `OperatorAngle` | 349 | 14 | 22% | 99% |
| `Ideals/Symmetric` | 217 | 8 | 57% | 98% |
| `DirectRotation` | 199 | 6 | 34% | 98% |
| `Core/Unbounded` | 720 | 6 | 43% | 99% |
| `Sylvester/Resolvent` | 601 | 5 | 82% | 99% |
| `SinTheta/General` | 387 | 5 | 13% | 99% |
| `Ideals/Rectangular` | 523 | 5 | 83% | 98% |
| `Sylvester/Basic` | 334 | 4 | 44% | 89% |
| `SinTheta/SpectralBridge` | 114 | 4 | 50% | 95% |
| `DoubleAngle` | 246 | 4 | 54% | 98% |
| `Core/AbstractSpectrum` | 314 | 1 | 98% | 98% |

Only `AbstractSpectrum` has a genuine tail. `Resolvent` and `Rectangular` are
tail-heavy. The rest interleave admitted and clean declarations throughout, so
no textual cut splits them and each needs a declaration-level partition.

That was the picture from file positions alone, and taken by itself it makes
the split look like the dominant cost of the reorganization. Measuring which
declarations the audited surface *actually reaches* shows otherwise; see
batch 4. Do not size this work from the table above.

## Ordered move manifest

Each batch compiles before the next begins. Batches 1–3 are independent of the
split and can land first.

### Batch 1 — promote the 13 already-clean Experimental modules

No admission anywhere in their closure, so these move without any split:

```
Experimental/InfiniteDimensional/Core/Complexification
Experimental/InfiniteDimensional/Core/ComplexificationFunctionalCalculus
Experimental/InfiniteDimensional/Core/RealContinuousFunctionalCalculus
Experimental/InfiniteDimensional/Core/RealSpectralBridge
Experimental/InfiniteDimensional/SpectraBridge/ApproximationNumberMinMax
Experimental/InfiniteDimensional/SpectraBridge/Basic
Experimental/InfiniteDimensional/SpectraBridge/DirectRotation
Experimental/InfiniteDimensional/SpectraBridge/DirectRotationSquare
Experimental/InfiniteDimensional/SpectraBridge/HalmosTwoProjections
Experimental/InfiniteDimensional/SpectraBridge/OperatorAbsoluteValue
Experimental/InfiniteDimensional/SpectraBridge/PVMSubspace
Experimental/InfiniteDimensional/SpectraBridge/SinAngle
Experimental/InfiniteDimensional/TanTheta/Vector
```

Destinations: `Core/Complexification*` and `Core/Real*` to
`DavisKahan/SpectralTheory/Complexification/` and
`DavisKahan/SpectralTheory/Real/`; the `SpectraBridge/*` set to
`DavisKahan/Interop/Spectra/`; `TanTheta/Vector` to `DavisKahan/TanTheta/`.

Note the name shadowing recorded in project memory: a legacy placeholder
shadows the real `SpectraBridge` projection. Qualify projection references
during this batch.

### Batch 2 — build topology

1. Give the `DavisKahan` and `ForMathlib` libraries explicit `globs` so the
   ordinary build covers the production tree rather than one root's imports.
2. Add `DavisKahan.All` to the default targets.
3. Create a distinct nondefault library for admission-dependent work with its
   own physical source root, keeping the `DavisKahan.Experimental` namespace.

Step 3 cannot land before the split, because `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean`
(production) imports `PaperAll` (Experimental) today.

### Batch 3 — structural checks

Add `scripts/check_library_structure.py` covering the plan's five checks. It is
expected to report violations until the split lands; that is its purpose.

### Batch 4 — the split

**This batch is far smaller than the module-level counts suggest.** Measuring
the *declaration* closure instead of the import closure changes the job.

A Lean traversal of the constants reachable from every `ForMathlib.DavisKahan1970`
facade declaration (7438 constants) shows the audited surface needs exactly
**11 declarations** from the 13 admission-bearing modules:

| module | declarations actually needed |
| --- | --- |
| `Core/Unbounded` | `ClosedOperator`, `.mk`, `.domain`, `.toLinearMap`, `.toLinearPMap`, `.IsSelfAdjoint`, `.realResolventSet`, `.realSpectrum` |
| `Ideals/Rectangular` | `RectangularSymmetricIdealFamily`, `.Mem`, `.gauge` |
| the other 11 modules | **none** |

All three large ones — `UnboundedSpectral` (31 admissions),
`SpectralProjection` (15), `OperatorAngle` (14) — contribute nothing. They are
in the closure only because something imports them, not because anything uses
them. Both needed structures are declared at the top of their files
(`Unbounded.lean:73`, `Rectangular.lean:35`), well before the first admission
(line 311 and line 439).

Shortest import paths from the facade show a single chokepoint. Eight of the
thirteen are reached only through `Core/Unbounded`:

```
PaperSymmetric
  -> Core.ReducingRestrictionExtras -> Core.ReducingRestriction -> Core.Unbounded
       -> DirectRotation -> DoubleAngle -> SinTheta.General -> Sylvester.Basic
            -> Ideals.Symmetric
            -> Sylvester.Resolvent -> Core.SpectralProjection
       -> DirectRotation -> GraphSubspace -> Core.OperatorAngle
```

`Core/Unbounded.lean` imports only `DirectRotation` and Mathlib's `LinearPMap`,
and its clean prefix never references `DirectRotation`. Extracting
`ClosedOperator` into a base module that imports Mathlib only therefore severs
nine of the thirteen at once.

Ordered plan, highest leverage first:

1. Extract `ClosedOperator` and its clean API into
   `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean`, importing Mathlib
   only. `Core/Unbounded.lean` then imports it and keeps the admitted `adjoint`
   plus the five later admitted declarations. `IsSelfAdjoint` sits *after* the
   admitted `adjoint` but, as its own docstring states, does not depend on it,
   so this is not a plain prefix slice.
   Severs: `Unbounded`, `DirectRotation`, `DoubleAngle`, `SinTheta/General`,
   `Sylvester/Basic`, `Ideals/Symmetric`, `Sylvester/Resolvent`,
   `Core/SpectralProjection`, `Core/OperatorAngle`.
2. Extract `RectangularSymmetricIdealFamily` into
   `DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`
   (clean prefix cut at `Rectangular.lean:439`). Severs `Ideals/Rectangular`.
3. `Core/AbstractSpectrum` reaches the facade through `Core/Compatibility`; its
   single admission is a true tail at 98%.
4. `Core/UnboundedSpectral` reaches it through `Ideals/ApproximationNumbersCore`.
5. `SinTheta/SpectralBridge` reaches it through the `GeneralSinTheta` chain, not
   through the paper layer.

Keep one canonical declaration throughout: extract and repoint imports, never
copy.

Reproduce the declaration-closure measurement with the traversal described
above; it is the measurement that decides this batch's true size.

### Batch 5 — the literal paper layer

Only after batch 4. Move the 20 `Paper*.lean` modules to
`DavisKahan/Sources/DavisKahan1970/SineTheta/` under the filenames the plan
lists, then update `scripts/audit_full_paper_sine_theta.py` paths only and
require the identical semantic checks.

## Known-broken retained work, outside the audit closure

| module | state |
| --- | --- |
| `Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean` | 10 errors: written against a `HilbertTensor` namespace and a `HilbertBasis.norm_apply` that the vendored Spectra snapshot does not provide |
| `Experimental/InfiniteDimensional/Sylvester/PaperHilbertSchmidt.lean` | 18 errors, pre-existing (15 before the universe work), outside the audit closure |

Both are retained-value work, neither blocks the audit. `ColumnExpansion` is
the first test case for the plan's alternative-proof policy and currently
prevents `DavisKahan.All` from building, so it gates batch 2 step 2.

## Open mathematical obligation

Checklist item 14, a genuine finite-multiplicity extremal construction, remains
open. The former `paperFiniteMultiplicity_equality` has been renamed to
`paperFiniteDimensional_scalar_homogeneity` and now documents exactly what it
proves. The correspondence matrix must carry this as an explicitly open row
until the direct-sum extremizer is built.


## Structural check 2 is blocked on mathematics, not on layout

Measured after the `RectangularFamily`, `ClosedSylvesterEquation` and
`SpectralBridge` splits.

Every remaining route from the audited facade to an admitted module runs
through one chain:

```
FullSineTheta -> GeneralSinTheta -> SinTheta.LegacyGapCompletion
  -> SinTheta.Unbounded -> SinTheta.Bounded   -> SinTheta.SpectralBridge
  -> SinTheta.Unbounded -> Sylvester.Unbounded -> Core.UnboundedSpectral
```

Both ends are genuine uses, not stale imports:

- `SinTheta.Bounded` uses `sylvester_mem_and_gauge_le_of_intervalExteriorGap`,
  which is unproved;
- `Sylvester.Unbounded` uses `spectralCutoff`, `boundedSpectralTruncation`,
  `boundedRealization_of_spectrumIn_Icc` and `boundedInverse_of_spectrumOutside`,
  all unproved.

`GeneralSinTheta` is a source facade and therefore production, so structural
check 2 -- no production module imports Experimental -- cannot be satisfied by
moving files. It requires one of:

1. proving the interval/exterior Sylvester estimate and the unbounded spectral
   truncation theory, which is the remaining hard mathematics of this
   development; or
2. reclassifying `GeneralSinTheta` as Experimental, which contradicts its being
   a source facade.

Do not resolve this by weakening the check or by exempting the facade. The
check is correctly reporting that a production facade rests on unproved
results. It should stay red until that is no longer true.

Note that this does not affect the audited surface: all 43 endpoints of
`FullSineTheta` are axiom-clean. The facade's *other* declarations, inherited
from `GeneralSinTheta`, are what still reach the admissions.
