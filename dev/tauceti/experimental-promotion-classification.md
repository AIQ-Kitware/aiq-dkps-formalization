# Classifying the 53 stranded `Experimental` modules

**Measured 2026-07-29 (edward, aiq-gpu), by three parallel read-only classifiers.**

`experimental-promotable-inventory.md` established *which* modules are stranded —
proved, with nothing admission-bearing depending on them — and closed by saying that
whether each *"duplicates a production result is a per-block judgement"*. This file
makes that judgement.

**Why it was needed.** `convergence-matrix.md` is the artifact designed to classify
duplication (`exact-duplicate` / `wrapper-duplicate` / `parallel-formulation`). It
mentions `Experimental` twice and carries none of those classifications, so for this
tree it was empty. A cheap name-collision scan is not a substitute: 49 collisions
across 1476 Experimental declarations, and the six against `ForTauCeti` (`ext`,
`norm_def`, `resolvent`, `kyFan`, `spectralCutoff`, `spectralProjection`) are all
spurious — generic names in distinct namespaces. The real risk is a **parallel
formulation**: the same theorem proved twice under different names, which name
matching cannot see.

## Result

| block | modules | PROMOTE | DUPLICATE | LEAVE | AGGREGATE |
|---|---:|---:|---:|---:|---:|
| `MathAhead/HiddenFoundations/FreeBeam/**` | 21 | 14 | 0 | 5 | 2 |
| `MathAhead/**` (rest) | 11 | 2 | 3 | 3 | 3 |
| `Scratch/**` | 18 | *(pending)* | | | |
| aggregate roots | 3 | — | — | — | 3 |

## The finding that matters most: proved ≠ proves anything

Several stranded modules are sorry-free **because their mathematical content sits in
`structure` fields rather than in proofs** — they are hypothesis records, and their
theorems are one-line projections out of assumed fields.
`SchattenApproximationFoundation` (14 fields), `SpectralMultiplicityFoundation`, and
`FreeBeamAnalyticFoundation` (~20 fields, including `selfAdjoint`, `graph_compact`,
`positive_spectrum_characterization`) each have **zero instances anywhere in the
repository**. Promoting them would import three large axiom-shaped records into
production and buy nothing.

Rule 3 counts these as stranded, and they are — but the right disposition is
*delete or leave*, not *promote*. **A promotion lane driven by the rule-3 count alone
would have moved them.**

## Duplicates found

- `MathAhead.Lemma63` — a re-export shim; `lemma6_3_approximationNumber_leakage_completed`
  is already production at `Sources/DavisKahan1970/Section6AppendixLeakage.lean:219`.
- `HiddenFoundations.HilbertSchmidtComplexFamily` — restates `ForTauCeti`'s
  `hilbertSchmidtIdealFamily` in the legacy 14-field shape. **One salvageable residue:**
  its `paperHilbertSchmidt_complete` has no production counterpart; extract it as an
  `IsComplete` instance rather than promoting the module.
- `HiddenFoundations.OrthogonalSummandCoordinates` — rebuilds Mathlib's
  `Submodule.orthogonalDecomposition` **from a file it already imports**
  (`Mathlib/Analysis/InnerProductSpace/ProdL2.lean:89`). Same type, different
  construction, so replacing it is a rewrite rather than a rename.

## Traps recorded for the promoter

1. **Bundled vs raw representation.** Everything in the FreeBeam abstract cluster from
   `BoundedInverseRealization` onward is written against the bundled
   `DavisKahanExt.ClosedOperator`, not raw `LinearPMap`. Promoting into `ForTauCeti`
   therefore means a bundled→unbundled rewrite (that is the U1 lane's job); promoting
   into `DavisKahan/` production is path-only and defers it. **Choose DavisKahan.**
2. **`CoerciveFormData.resolvent` is not a resolvent** at a spectral parameter — it is
   `A⁻¹`. It will read as, but does not duplicate, `TauCeti.LinearPMap.resolvent`.
   Rename before promotion.
3. **Bespoke compactness.** `SequentiallyCompactOperator` /
   `SequentiallyCompactGraphEmbedding` are hand-rolled sequential surrogates. Promoting
   them verbatim installs a private compactness notion where production has none;
   restate over `IsCompactOperator`.
4. **Real/complex parallel pair.** `SmoothGreenIdentity` and `ComplexGreenIdentity` are
   the same identity twice; only the complex one is used downstream.

## What production genuinely lacks

The FreeBeam abstract cluster is **orthogonal to** `ForTauCeti/**/LinearPMap/**`, not
parallel to it. That tree covers adjoints/closedness, resolvent/spectrum, spectral
measure, Stone/Yosida and Sylvester — and contains **no form method, no compactness
API, and no bounded→unbounded inverse construction**. A Lax–Milgram/Friedrichs form
realization producing a self-adjoint operator with compact resolvent is the real prize
in this lane.

`FreeBeamCharacteristic` is the other: it proves
`boundaryDet β = 2(1 - cos β cosh β)`, and `Real.cosh` appears **nowhere** in
production. Production currently *assumes* the conclusion, as the
`third_eigenvalue_gt_five_hundred` field of a certificate at
`Sources/DavisKahan1970/Section9/ExactData.lean:249`.
