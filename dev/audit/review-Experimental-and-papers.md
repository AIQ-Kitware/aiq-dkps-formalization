# Review — `DavisKahan/Experimental` and the paper libraries

**FILE PASS COMPLETE for 28 groups — 249 files, ~57,000 lines.** 2026-07-29,
`edward (aiq-gpu)`, lane `AUDIT`. Covers all six `Experimental` groups and every
paper library (`Acharyya2024`, `Acharyya2025`, `Helm2025`, `DkpsQuench2026`,
`FinishTanTwoTheta`, `FinishYuWangSamworth`) with their documentation and
tooling subgroups.

## `DavisKahan/Experimental` — 151 files, ~27,700 lines

| group | files | lines | escapes |
|---|---|---|---|
| `InfiniteDimensional` | 94 | 20,483 | 22 |
| `MathAhead` | 15 | 2,253 | 0 |
| `Scratch` | 15 | 1,750 | 0 |
| `Sources` | 8 | 515 | 0 |
| `Frontier` | 7 | 2,664 | **28** |
| root + `FiniteDimensional` | 3 | 47 | 0 |

**All 50 escapes are in 8 files**, and 28 of them in `Frontier/` alone — 21 in
`Section9Analytic.lean`, which `AGENTS.md` records as needing interval
Sobolev/Rellich theory absent from the pinned Mathlib. That is a research
blocker, not proof-engineering debt, and it is correctly parked.

**The tree is correctly outside `defaultTargets` and correctly labelled.**
`Scratch/` holds proof sketches per the `AGENTS.md` overlay rule; `MathAhead/`
holds mathematics ahead of the frontier; `Frontier/` holds the open obligations.
The three-way split is real and a reader can navigate it.

**Findings are already covered by existing lanes**, and the audit adds no new
ones here — which is itself the finding:

- 28 modules are promotable now (`EXP-PROMOTE-{HF,SYL,T2T,MISC}`).
- The 8 escape-bearing files gate 86 others (`EXP-UNBLOCK`), with
  `InfiniteDimensional/DoubleAngle.lean` carrying **one** escape and gating 75.
- `InfiniteDimensional/` at 94 files and 20,483 lines is **larger than most
  production groups** and is the single biggest unreviewed body of mathematics
  in the repository. Its `SinTheta/Continuation*` family alone is ~25 files.

**One observation the lanes do not cover.** `InfiniteDimensional/SinTheta/`
contains twenty-five files prefixed `Continuation*`
(`ContinuationAssembly`, `ContinuationContour`, `ContinuationCore`,
`ContinuationEndpoints`, `ContinuationQuarterAcute`, `ContinuationRieszIntegral`,
`ContinuationRoadmap`, …). A prefix repeated 25 times is a directory that was
never made. If any of this is promoted, it should become
`SinTheta/Continuation/` first — the same flat-file-beside-family pattern as
`PLACE-SYLV`, at larger scale.

## The paper libraries — 98 files, ~29,000 lines, **0 escapes**

| library | Lean files | lines | verdict |
|---|---|---|---|
| `FinishTanTwoTheta` | 21 | 6,705 | **naming, `FTT-PROMOTE`** |
| `Acharyya2025` | 20 | 6,001 | clean |
| `DkpsQuench2026` | 32 | 12,712 | clean |
| `FinishYuWangSamworth` | 11 | 1,203 | clean |
| `Acharyya2024` | 7 | 2,638 | clean |
| `Helm2025` | 4 | 1,993 | clean |

**Every paper library is proof-complete.** That is a stronger result than it
sounds: five papers formalized end to end with no escapes, and only
`FinishTanTwoTheta` and `FinishYuWangSamworth` sit outside `defaultTargets`
(both already covered by `FTT-PROMOTE`).

### Finding PAPERS-1 — two libraries carry claim documents nothing checks `{lane:CLAIM-DOC}`

`FinishTanTwoTheta` and `FinishYuWangSamworth` each ship `GROUNDING.md`,
`PROOF_OBLIGATIONS.md` and a `scripts/verify_grounding.py`; `FinishYuWangSamworth`
adds `ELEGANCE_AUDIT.md`. These are **documents that assert the library's own
completeness**, plus a tool that asserts the assertion.

They are not wired into any repository gate. `scripts/` at the top level holds
the checked gates; these two live inside their libraries and are invoked by
nothing in CI or in `dev/README.md`'s gate list. So a reader gets a
completeness claim with no evidence that anything still verifies it.

**This is the highest-leverage documentation finding in the audit** for the
reason recorded in the audit README: a false claim in a document like this is
more damaging than a weak proof, because it is what a reader trusts *instead of*
checking. The lane is to run both `verify_grounding.py` scripts, record whether
they still pass, and either wire them into the gate list or mark the documents
as historical.

### What is good

- **`DkpsQuench2026` is the best-organized paper library** — `Core/`,
  `Geometry/`, `Paper/`, `Probability/`, `QueryEfficiency/`, `Rates/`,
  `Response/`, `Spectral/`, so the formalization mirrors the paper's structure
  rather than the order things were proved in.
- **`Acharyya2024/2025` ship their source transcriptions** as
  `*_transcription.md` next to the Lean, which is how source-fidelity work
  should be shipped.
- **`Helm2025/AcharyyaBridge.lean`** does the right thing with cross-paper
  dependence: it is a named bridge module rather than `Helm2025` reaching into
  `Acharyya2025` internals.

## Method correction, recorded because it recurred

The first profile run for this batch reported **0 escapes in `Experimental`**.
That was wrong — the correct count is 50. The cause: my ad-hoc profiler stripped
`--` line comments *before* `/- … -/` block comments, and this repository writes
**"Davis--Kahan" with a double hyphen inside docstrings**, so the line-comment
pass truncated docstring lines, destroyed their `-/` closers, and the
block-comment pass then swallowed real code — including the escapes.

`scripts/check_tauceti_readiness.py` already has a tested, comment-order-correct
`strip_comments`/`has_escape` pair, and using it gives 50 across 8 files,
matching the independent measurement made for lane `EXP-UNBLOCK`.

**This is the third time in this audit that a re-implemented checker disagreed
with the tested one** (docstring coverage in `audit_profile.py`, the escape
regex in `check_tauceti_readiness.py` itself, and now this). The rule that
follows: **the audit's profilers must call the gates, never re-implement them.**
