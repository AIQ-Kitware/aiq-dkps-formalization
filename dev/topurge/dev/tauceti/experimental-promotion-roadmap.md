# Promotion roadmap — grounded proofs out of Experimental

Goal: polish the major reusable proofs for adversarial Tau Ceti review and
**promote grounded proofs out of `DavisKahan/Experimental/` into polished
production homes**, in small green-preserving moves. This doc is the overnight
worklist; each step keeps `lake build`, the source census, the frontier audit,
`check_library_structure.py`, and `check_dependency_layers.py` green.

## The invariant that makes it safe

Rename **nothing** unless necessary. A move that only changes a module's *file
path* (not its declaration namespace) is trivially audit-safe: the census
`lean_declarations` and the frontier node `declaration` fields keep resolving;
only the frontier node `module` field and the `import` lines of consumers change.
**De-experimentalizing the namespace (`…Experimental.…` → production) is a
SEPARATE, later batched pass** — do the file-tree graduation first.

Hard rule: a production module may not import an Experimental module
(`check_library_structure.py` check 2). So a module can graduate only once its
Experimental dependency closure has graduated (or it has none). Promote
**dependency-closed clusters, leaves first.**

## Worklist: 33 grounded declarations in 8 Experimental modules

| Module | grounded nodes | sorries | Experimental imports | graduation status |
| --- | --- | --- | --- | --- |
| `Experimental/InfiniteDimensional/Core/SpectralProjection` | 1 | 0 | **none (leaf)** | **READY** (pilot) |
| `Experimental/Frontier/Core` | 5 | **2** | (foundation) | needs SPLIT (grounded S3 predicates out, 2 sorry decls stay) |
| `Experimental/Frontier/Lemma63` | 3 | 0 | Frontier/Core | blocked on Core split |
| `Experimental/Frontier/RemainingSourceSurface` | 7 | 0 | Frontier/Lemma63 | blocked on Core→Lemma63 chain |
| `Experimental/Frontier/RieszCircle` | 6 | 0 | Frontier/Core, …/SpectralProjection, …/CayleySelectorBridge | blocked on Core + CayleySelectorBridge |
| `Experimental/Frontier/Section3` | 9 | **4** | (uses Frontier/Core) | needs SPLIT + Core |
| `Experimental/Frontier/Section4` | 2 | **2** | — | needs SPLIT |
| `Experimental/InfiniteDimensional/Core/SpectralProjection` | (above) | | | |

The whole grounded-Frontier subgraph funnels through `Frontier/Core`, which is
**mixed** (5 grounded + 2 sorry). So the unblocking move is **splitting
`Frontier/Core`**: lift its 5 grounded Section-3 predicates
(`IsPaperDirectRotation`, `CrossedDefectsEquivalent`, `genericHalmosCosineSq`,
`genericHalmosSineSq`, `genericHalmosCosineSq_add_sineSq`) into a production
module, leaving the 2 sorry-bearing declarations behind in an Experimental
frontier file. Once Core's grounded core is production, Lemma63 →
RemainingSourceSurface → Section3/4 (after their own splits) → RieszCircle can
graduate.

## Ordered plan

1. **[READY] Pilot: graduate `SpectralProjection`** (leaf, grounded, Spectra-backed)
   → `DavisKahan/SpectralTheory/BoundedSelfAdjointSpectralProjection.lean`
   (it imports `Interop.Spectra.*` + `Spectra.*`, so it is a Spectra bridge; keep
   namespace `ForMathlib.DavisKahanExt`). Update its 6 Experimental importers +
   the `Core/All` aggregate + the frontier `base-spectral-projection` module field.
2. **Split `Frontier/Core`**: grounded Section-3 predicates → a production
   `DavisKahan/Geometry/…` (or `DavisKahan/Halmos/…`) module; sorry decls stay in
   a slimmed Experimental frontier module. Repoint the 5 frontier nodes' module
   field; repoint the 6 importers.
3. **Graduate `Frontier/Lemma63`** (Section-6 appendix leakage) → `DavisKahan/Sources/DavisKahan1970/Section6/…` or `DavisKahan/OperatorIdeal/…`.
   - **REFINEMENT (verified):** Lemma63's `import DavisKahan.Experimental.Frontier.Core` is **vestigial** — it references zero Core declarations. Its real deps are `ForMathlib.…ApproximationNumberSingularValues` + `DavisKahan.Sources.DavisKahan1970.Ideals.*` (all non-Experimental). So: **drop the vestigial Core import** → Lemma63 has 0 Experimental deps → graduate immediately (independent of the Core split). Clean next win after the split lands.
   - RieszCircle, by contrast, genuinely uses Core's grounded helpers `circleRieszProjection` (17×) and `CircleSeparatesRealSpectrum` (5×) (Core lines 160–175, sorry-free). To unblock RieszCircle, those two grounded helpers must ALSO be split out of Core (a second Core split), or RieszCircle graduation is deferred.
4. **Split `Frontier/Section3`** (9 grounded + 4 sorry) and **`Frontier/Section4`**
   (2 grounded + 2 sorry): grounded propositions → `DavisKahan/Sources/DavisKahan1970/Section3` / `Section4`.
5. **Graduate `Frontier/RemainingSourceSurface`** (Section 5/6/7 source theorems)
   once its chain is clear.
6. **Graduate `Frontier/RieszCircle`** once Core + CayleySelectorBridge are clear
   (or split CayleySelectorBridge).

## Per-step procedure (repeatable, green-preserving)

1. `git mv` the file (or the split-out declarations into a new production file).
2. `sed` every importer's `import` line to the new module path.
3. Update the aggregate(s): remove from the Experimental `…/All.lean`, add to the
   production aggregate if the file is now production-reachable.
4. Update `dev/davis-kahan-1970-frontier.json`: the affected nodes' `module` field
   (and `declaration` only if a namespace actually changed).
5. Rebuild the moved module + its importers; then `DavisKahan.Experimental.Frontier.All`.
6. Re-audit: `check_davis_kahan_frontier.py --write-report`,
   `check_davis_kahan_1970_source_census.py` (+ regenerate `.md` if it complains),
   `check_library_structure.py`, `check_dependency_layers.py`. All must stay green
   (frontier exits nonzero only for still-open Section 8/9 nodes — that's expected).
7. Commit with `--no-gpg-sign`.

## Reusable-for-Tau-Ceti thread (separate from DK-internal graduation)

The genuinely GENERIC grounded proofs (approximation numbers — done; Courant–Fischer;
singular-value/frame layer; rectangular ideals) are the ForTauCeti-bound "major
reusable proofs." Those follow the ForTauCeti extraction (manifest + export tool),
NOT the DavisKahan-internal graduation above. NOTE (owner): this will eventually
require **bringing the needed Spectra pieces into Tau Ceti** and **adopting Tau
Ceti's data structures** rather than the local/Spectra ones — a deep migration
that comes after the DK-internal graduation and the roadmap acceptance.

## Reality check: most clusters need whole-subgraph promotion

Verified dependency closures show the frontier is a tightly connected Experimental
subgraph. **Clean single-module graduations are limited to true leaves:**

- `SpectralProjection` — DONE (leaf).
- `Lemma63` — clean after dropping its **vestigial** Core import (uses no Core decl).
- `RemainingSourceSurface` — its ONLY Experimental import is `Frontier/Lemma63`, and
  it is **vestigial** (uses no Lemma63 decl; real deps are all production:
  `TanTheta.GenuineSpectrum`, `UnboundedGraphAngle`, `FiniteDimensional.TanTheta.RitzResidual`,
  `TanTheta.Theorem63FiniteSource`). Drop it → 0 Experimental deps → graduate its
  **7 grounded nodes** (theorem5_1, section7 sin2/tan2, trialResidual, the two
  theorem6_3 source specializations, compatible-cross-norm).

**Vestigial-import insight:** several grounded frontier modules carry stale
Experimental imports they no longer use. Dropping those (verify by build) is the
cheapest graduation lever — the real coupling is looser than the import lines suggest.
Clean-win tally so far: SpectralProjection (1) + Core-predicate split (5) +
Lemma63 (3) + RemainingSourceSurface (7) = **16 of 33 grounded nodes** graduate
cleanly; the remaining 17 are in the deep clusters below.

**Deep clusters (defer; promote the whole dependency-closed subgraph together):**

- `Frontier/Section3` (9 grounded props) imports **four** Experimental modules:
  `Frontier/Core`, `InfiniteDimensional/DoubleAngle`,
  `MathAhead/HiddenFoundations/Section3Nonacute`,
  `MathAhead/HiddenFoundations/HalmosClassification`. Its 4 sorries are clustered
  at the end (`twoProjection_operator_classification`,
  `theorem3_1_spectralMultiplicity_classification`, `compactAngleEigenvalueList`,
  `corollary3_1_compact_angleList_classification`) — split those off, but the
  grounded head still needs all four Experimental deps promoted first.
- `Frontier/RieszCircle` needs Core's grounded helpers `circleRieszProjection` +
  `CircleSeparatesRealSpectrum` (a second Core split) AND `CayleySelectorBridge`.

So the campaign is **not** mostly quick file moves — the bulk is promoting
dependency-closed subgraphs (DoubleAngle, HiddenFoundations, Core-helpers,
CayleySelectorBridge) out of Experimental, each of which pulls its own closure.
That is the overnight body of work; the leaf graduations above are the quick wins.

**Deep-cluster dependencies verified real (NOT vestigial):** Section3 uses genuine
declarations from all four of its Experimental imports (Core 3, DoubleAngle 2,
Section3Nonacute 3, HalmosClassification 1); RieszCircle uses Core (2) +
CayleySelectorBridge (4). So the overnight sequence is: promote each of
`InfiniteDimensional/DoubleAngle`, `MathAhead/HiddenFoundations/Section3Nonacute`,
`MathAhead/HiddenFoundations/HalmosClassification`,
`InfiniteDimensional/SinTheta/CayleySelectorBridge`, and Core's remaining grounded
helpers (`circleRieszProjection`, `CircleSeparatesRealSpectrum`) — each with its own
dependency closure and sorry-split where needed — THEN Section3/Section4/RieszCircle
graduate. Check each candidate's imports for vestigial ones first (cheapest lever).

## Progress ledger (this session)

Graduated out of the Experimental file tree, green each step:
- `SpectralProjection` → `Interop/Spectra/BoundedSelfAdjointSpectralProjection` (1 node).
- Core Section-3 predicates → `Geometry/Halmos/GenericRotationPredicates` (5 nodes).
- `Lemma63` → `Sources/DavisKahan1970/Section6AppendixLeakage` (3 nodes; vestigial Core import dropped).
- `RemainingSourceSurface` → `Sources/DavisKahan1970/RemainingSourceSurface` (7 nodes; vestigial Lemma63 import dropped).

= 16 of 33 grounded nodes graduated. Remaining 17 are the deep clusters above.

Additionally, `Frontier/Core` is now a **pure 2-sorry stub**: its 9 grounded
declarations were split into production —
`Geometry/Halmos/GenericRotationPredicates` (5 S3 predicates),
`Geometry/Halmos/UnitaryEquivalence` (`PairOfSubspacesUnitaryEquivalent`,
`BoundedOperatorsUnitaryEquivalent`), and
`Interop/Spectra/CircleRieszProjection` (`CircleSeparatesRealSpectrum`,
`circleRieszProjection`). Core retains only `SameSpectralMultiplicity` /
`sameSpectralMultiplicity_iff_unitarilyEquivalent` (the ungrounded
`s3-spectral-multiplicity-*` nodes) and re-exports the production helpers.

**Now unblocked for the next pass** (their only Experimental dep was Core's
grounded helpers, now production): `MathAhead/HiddenFoundations/HalmosClassification`
(repoint its `Frontier.Core` import → `Geometry/Halmos/UnitaryEquivalence`, then it
has 0 Experimental deps → graduate); and RieszCircle's Core dependency is now on
production `Interop/Spectra/CircleRieszProjection` (its remaining blocker is
`CayleySelectorBridge` → `Sylvester/Resolvent`).

Next-session order: HalmosClassification (clean) → DoubleAngle (sorry-split first)
→ Section3Nonacute chain → then Section3/Section4 grounded heads → RieszCircle
after CayleySelectorBridge/Resolvent.

## Session close state (this session, all committed + green)

Graduated out of `Experimental/` (all verbatim, namespaces kept, green each step):
SpectralProjection; Core split into GenericRotationPredicates + UnitaryEquivalence
+ CircleRieszProjection (Core now a pure 2-sorry stub); Lemma63; RemainingSourceSurface;
HalmosClassification; Resolvent→CayleySelectorBridge→RieszCircle (6 s8 nodes);
PolarIsometry/Section3Nonacute subgraph (4 modules). **22 of 33 grounded frontier
declarations + the Core hub + the PolarIsometry infrastructure now live in production.**

## What remains — needs judgment or open math, NOT blind mechanical batching

1. **~15 sorry-free Experimental leaves remain**, but they split into two kinds that
   must NOT be treated identically:
   - **Genuine reusable foundations** (graduate when confirmed frontier/production-used):
     `InfiniteDimensional/Core/{AbstractSpectrum,OperatorAngle}`,
     `InfiniteDimensional/Sylvester/SelfAdjointBorelCalculus`,
     `FiniteDimensional/DoubleAngle/SinTheta` (already production-imported — highest priority),
     `MathAhead/HiddenFoundations/{HilbertSchmidtComplexFamily,SchattenApproximationFoundation,OrthogonalSummandCoordinates}`.
   - **Ahead-of-frontier EXPERIMENTS** (do NOT force into production — Section 9 is still open):
     `MathAhead/HiddenFoundations/FreeBeam/*`, `MathAhead/Section4/InfiniteIdealDominance`,
     `MathAhead/Lemma63` (thin re-export stub). These stay in `MathAhead` until their
     frontier endpoint is proved and they are source-integrated.
2. **Section3 (9 grounded props) needs an intricate PARTIAL split**: prop3_4 and its
   helpers (lines ~486–589) genuinely use `DoubleAngle.reflectedSubspace` /
   `starProjection_reflectedSubspace`; prop3_1/3_2/3_3/3_5/cor3_2 appear DoubleAngle-free
   and could be extracted to production, but they interleave with the DoubleAngle-using
   props and the 4 sorry props (non-contiguous extraction). Careful, deliberate work.
3. **Section4 (2 grounded props)** import Section3 → blocked on Section3.
4. **`InfiniteDimensional/DoubleAngle` has 8 real sorries** — this is open **paper-completion
   math** (per owner framing, the "pivot back to finishing DK proofs" work), NOT polish.
   It gates the Section3 prop3_4 area and Section3/Section4 heads.

So: the clean, unambiguous "grounded proof out of Experimental" graduations are DONE.
The remainder is (a) per-module readiness judgment on the reusable-vs-ahead-of-frontier
leaves, (b) intricate Section3 partial split, and (c) genuinely-open DoubleAngle math.

5. ~~**`Experimental/FiniteDimensional/DoubleAngle/SinTheta` is a name-colliding twin.**~~
   **DONE.** It was actually a sorry-free *downstream extension* (imports the production
   SinTheta, adds the 3 `sinTwoTheta_residual_*` theorems). Graduated to
   `DavisKahan/FiniteDimensional/DoubleAngle/SinTwoThetaResidual.lean` (descriptive name
   avoids the file collision); Generalized repointed. **`check_library_structure` #2 is now
   green — zero production→Experimental imports.** Original note retained below for history:
   
   A production `DavisKahan/FiniteDimensional/DoubleAngle/SinTheta.lean` ALREADY exists
   (same `ForMathlib` namespace), and production `FiniteDimensional/Generalized` imports
   the **experimental** twin — that is the standing `check_library_structure` #2 violation
   (production → Experimental). Fixing it is not a move: it needs the two same-namespace
   SinTheta files RECONCILED (diff them; fold the experimental additions into the
   production file, or point Generalized at the production file if it already suffices),
   then delete the experimental twin. Careful reconciliation, not a `git mv`. This is the
   single highest-value cleanup (it clears the one production→Experimental violation) — do
   it deliberately, first, next session.

## Blockers named explicitly

- `Frontier/Core` (2 sorries) blocks Lemma63, RemainingSourceSurface, Section3, RieszCircle.
- `RieszCircle` also blocked on `InfiniteDimensional/SinTheta/CayleySelectorBridge` (Experimental).
- Section 8/9 frontier nodes are genuinely open (not grounded) — not part of this
  promotion; they stay in the frontier until proved.
