# Review — production `DavisKahan` (all 18 groups)

**FILE PASS COMPLETE — 314 files, ~65,000 lines**, every production group
outside `Experimental/`. 2026-07-29, `edward (aiq-gpu)`, lane `AUDIT`.

| group | files | lines | verdict |
|---|---|---|---|
| `Sources/DavisKahan1970` | 77 | 15,059 | clean; the paper library, and it reads like one |
| `SpectralTheory` | 35 | 7,964 | clean |
| `FiniteDimensional` | 34 | 9,572 | clean; 1 oversize |
| **`Interop`** | 30 | 7,765 | **the donor is retired, DK-INTEROP** |
| `SinTheta` | 31 | 5,627 | **three frame factorizations, DK-FRAME** |
| `Sylvester` | 24 | 5,595 | clean; `GenuineSpectrum` (`DK-NAME`) |
| `Geometry` | 16 | 4,095 | clean; 2 oversize |
| `Riccati` | 15 | 2,951 | clean; 1 oversize |
| `OperatorIdeal` | 14 | 3,958 | clean |
| `Alternative` | 8 | 1,286 | clean, and correctly labelled |
| `DoubleAngle` | 6 | 1,744 | clean |
| `Analysis` | 6 | 849 | clean |
| `TanTheta` | 7 | 2,473 | `GenuineSpectrum` ×2 (`DK-NAME`) |
| `BoundedOperator`, `TanTwoTheta`, `Sources/Davis1963`, `Sources`, `Specialized`, root | 21 | ~1,600 | clean |

## The headline positive

**Zero proof escapes in all 314 production files**, and **every mathematical
file declares into `namespace TauCeti`** — one namespace across 65,000 lines.

That is worth stating plainly because it is the opposite of what the audit found
in `ForTauCeti`, where four files had drifted into core Mathlib namespaces
(`NS-SPREAD`). **The paper library is more namespace-disciplined than the
library being prepared for submission.** Whatever process produced that
consistency here should be applied there.

## Finding DK-INTEROP — 7,765 lines of bridge to a retired donor `{lane:DK-INTEROP}`

`DavisKahan/Interop/Spectra/` is **26 files and 7,534 lines**. The Spectra
dependency is retired: `import Spectra` in these files is **0**.

But all 26 still discuss Spectra in prose, and the directory is still named for
it. Two of the three largest files in production `DavisKahan` are here —
`DirectRotationSquare.lean` (1,409 lines) and `DirectRotation.lean` (1,181).

**The question for every file is the one the audit README poses for this group:
should it still exist?** Three possible answers per file, and they are different
work:

1. **It was a bridge and the far side is gone** → delete.
2. **It holds DKPS mathematics that was written here because Spectra was the
   available foundation** → move it to its real home; the `Interop/` name is now
   actively misleading about ownership.
3. **It is genuinely interop with something still live** → rename, because
   `Interop/Spectra/` names a dependency that no longer exists.

Answer (2) is the likely majority, and it matters for attribution: `AGENTS.md`
is emphatic that DKPS theorems must not read as donor material. A directory
called `Interop/Spectra` full of our own mathematics is that failure mode by
directory name rather than by namespace.

**Eight modules outside `Interop/` still import it**, including three in
production (`DoubleAngle/Unbounded.lean`, `DoubleAngle/UnboundedIdeal.lean`) —
so this is not dead code that can simply be dropped.

## Finding DK-FRAME — three frame factorizations in one group `{lane:DK-FRAME}`

`DavisKahan/SinTheta/` contains:

- `FrameFactorization.lean` (461 lines, 23 declarations)
- `Real/FrameFactorization.lean` (330 lines, 7 declarations)
- `FrameFactorizationGeneric.lean` (248 lines, 11 declarations)

Three files, one concept, and the third is named "Generic" — which tells a
reader there is a general one and a specific one, but not which of the other two
is which. The same group also carries `Core.lean` twice (`SinTheta/Core.lean`
438L and `Bounded/Core.lean` 293L).

This is the `ForTauCeti` T02 finding (three polar factors) repeated in a
different library: the mathematics is plausibly right, the *relationship between
the three* is nowhere stated, and the names actively mislead. Same fix — one
paragraph in each naming the others and the hypothesis that separates them, or a
merge if two turn out to be the same.

## Finding DK-1K — six more files over the 1,000-line limit `{lane:SPLIT-1K}`

`SPLIT-1K` was scoped to `ForTauCeti` only. Production `DavisKahan` has six more:

| lines | file |
|---|---|
| 1,409 | `Interop/Spectra/DirectRotationSquare.lean` |
| 1,181 | `Interop/Spectra/DirectRotation.lean` |
| 1,078 | `Geometry/Polar/Section3Nonacute.lean` |
| 1,063 | `Geometry/Angle/OperatorAngleComplex.lean` |
| 1,035 | `FiniteDimensional/Sharpness.lean` |
| 1,018 | `Riccati/UnboundedAdjointRiccati.lean` |

**Two caveats that keep this honest.** First, the 1,000-line limit is stated in
`ForTauCeti/README.md` §4 as a *Tau Ceti submission* constraint — production
`DavisKahan` is the paper library and is not submitted, so the limit does not
formally bind here. Second, the top two are in `Interop/` and may be deleted by
`DK-INTEROP` anyway.

Recorded because four of the six *are* candidates for eventual extraction, and a
1,000-line file is hard to review wherever it lives. `SPLIT-1K`'s scope note is
updated rather than a new lane being opened.

## What is good

- **`Sources/DavisKahan1970/` reads like a paper library**, which is exactly
  what it should be: `Theorem61`, `Theorem62`, `Lemma61`, `Section8RieszCircle`,
  `Section9/`, with an `Audits/` subdirectory holding the correspondence checks.
  A reviewer can find the formalization of a numbered result by its number. That
  is the right organizing principle for source-fidelity work and it is executed
  consistently across 77 files.
- **`Alternative/` is correctly labelled.** It holds `ProseLike` and
  `ClassicalProseLike` API variants and an `EigenbasisFrobenius` alternative
  proof — and its directory name says so. Alternative formulations kept
  deliberately, and signposted, are a feature.
- **`Riccati/` splits bounded from unbounded consistently** (`Bounded*` /
  `Unbounded*` prefixes across 15 files), so the representation boundary the U1
  migration cares about is visible from the file listing.
- **`OperatorIdeal/ApproximationNumbers/Real/`** separates the real-valued
  conversion into its own subtree rather than threading a scalar parameter
  through everything.

## Group verdict

**Production `DavisKahan` is in better shape than `ForTauCeti`** on every
mechanical measure: one namespace, no escapes, consistent file organization, and
a paper library that a reviewer can navigate by theorem number.

Its two real problems are both *legacy shapes that outlived their cause*:
`Interop/Spectra/` names a dependency that no longer exists, and the frame
factorization / genuine-spectrum families accumulated variants without anyone
recording how they relate.
