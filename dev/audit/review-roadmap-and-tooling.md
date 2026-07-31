# Review — the roadmap arm and the tooling

**Status: COMPLETE for the 25 files.** Written 2026-07-31 by
`edward (aiq-gpu-docs)`, lane `AUDIT`, clusters (i) and (iii) of the 50-file
tail. With this the checklist reads **1207 of 1207**.

Reviewed: `ForTauCetiRoadmap.lean`; five `README.md` and six `Suggested.lean`
under `ForTauCetiRoadmap/`; ten `scripts/` and `scripts/tests/` files; and the
three `dev/audit/review-*.md` written earlier in this lane.

## Finding R-1 — the roadmap is 89% delivered and does not say so `{lane:ROADMAP-DELIVERED}`

`ForTauCetiRoadmap/**/Suggested.lean` records **176 target signatures** across six
topics. Matching each against the declarations actually present in `ForTauCeti`
and `DavisKahan`:

| topic | sketched | delivered | |
|---|---|---|---|
| `FiniteDimensionalOperators` | 32 | **32** | **100%** |
| `MajorizationAndAngles` | 26 | **26** | **100%** |
| `SpectralTheory` | 25 | 24 | 96% |
| `SpectralSubspacePerturbation` | 38 | 35 | 92% |
| `MatrixStatistics` | 21 | 18 | 85% |
| `OperatorIdeals` | 34 | 23 | 67% |
| **total** | **176** | **158** | **89%** |

**The `sorry` bodies are not the finding.** `Suggested.lean`'s own docstring says
*"Bodies are placeholders; the statements are the content"*, and
`ForTauCetiRoadmap.lean` explains that the library exists *"so that a broken
suggested signature is a build failure"* — which is a good design and caught ten
real elaboration errors when it was introduced. The 118 `sorry`s are deliberate.

**The finding is that nothing distinguishes the delivered 158 from the
outstanding 18.** Two topics are finished and still read as plans. A reviewer
opening `FiniteDimensionalOperators/` sees 32 unproved signatures and a 448-line
README of intent, for material that is complete; an agent looking for work cannot
tell which entries are open without running this comparison.

Verified statement-for-statement, not merely by name, on a sample:
`sqrt_unique`, `eigenvalues_eq_iSup_iInf_re_inner` and
`selfAdjointFunctionalCalculus_apply_of_apply_eq_smul` are binder-for-binder the
theorems in `PositiveSqrt.lean`, `CourantFischer.lean` and
`SelfAdjointFunctionalCalculus.lean`. Independently, `audit_scan --dup --mirrors`
classifies **22 pairs** as *"roadmap mirrors (expected — a `Suggested.lean`
signature matching its implementation)"*, which is the same phenomenon counted by
statement rather than by name.

### The 18 outstanding are really about 13, and the difference is naming drift

Name-matching over-reports, because the implementation chose different names:

* `schattenFamily` → **delivered** today as `schattenIdealFamily`
* `tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy` → **delivered** today, as
  the two qualified forms `…_of_finiteDimensional` and `…_of_hilbertBasis`
* `yosidaApproximant` → **delivered** as `yosidaApprox` (with four variants)
* `frobeniusNorm` → `frobenius` exists
* `UnboundedSinThetaProblem` → `UnboundedSinThetaData` and
  `UnboundedSinThetaDataPMap` exist

**`SymmetricGauge` is the interesting one and is genuinely outstanding as an
abstraction**: `finiteSymmetricGauge`, `lpSymmetricGauge` and
`linftySymmetricGauge` all exist as concrete gauges, but the structure the
roadmap proposes to unify them — with `extend`, `iSup_le_extend_le_tsum` and
`extend_le_extend_of_forall_sum_le` — does not. That, plus
`symmetricGaugeFamily` and its two lemmas, is most of `OperatorIdeals`' 11 and is
why that topic sits at 67% while the others are near-complete.

So the honest number is **roughly 13 open signatures out of 176**, concentrated
in one topic, and **the roadmap arm is not a backlog — it is a record of finished
work with a small live edge.** Sizing it from the file count (176 signatures,
2,850 lines of README) would mislead anyone who claimed it. Posted as
`{lane:ROADMAP-DELIVERED}`.

## No finding — the tooling

All **15** files under `scripts/tests/` pass (`test_audit_scan_defn`,
`test_check_davis_kahan_frontier`, `test_check_declaration_name_drift`,
`test_check_dependency_layers`, `test_check_docstring_coverage`,
`test_check_experimental_coverage`, `test_check_lane_graph_state`,
`test_check_merge_losses`, `test_check_private_shadows_public`,
`test_check_stale_build_artifacts`, `test_derive_tauceti_submission_ladder`,
`test_export_for_tauceti`, `test_generate_all_aggregates`,
`test_lake_build_report`, `test_refresh_tauceti_pr1_consistency`).

`scripts/setup-lake-cache.sh` and `test_derive_tauceti_submission_ladder.py` are
the only two here I did not write, and both are sound.

**Eight of these ten are mine, from today, and the tick is correspondingly weak
— the same caveat as in `review-scattered-production.md`.** What can be said
without self-assessment is mechanical: every one has a test file, every test
passes, and each of the three new gates
(`check_experimental_coverage`, `check_private_shadows_public`,
`check_stale_build_artifacts`, plus `check_merge_losses`) carries a
`RepositoryTest` that runs it against the real tree, so a gate that goes stale
fails its own suite rather than silently passing.

One thing worth flagging for whoever next touches them, since it is a fact about
the set rather than a judgement of any file: **four of the twenty-five
`check_*.py` now end in `return 1 if args.check else 0`** — the six named in
`{lane:AUDIT}`'s finding AT-6 plus the two I added under that pattern
deliberately. That count is the subject of `{lane:BUILD-STALE}` and is not
re-litigated here.

## No finding — the READMEs

The five `README.md` files (448–666 lines each, 2,850 total) are milestone prose
with literature citations, and they are the roadmap's definitive layer by their
own account: *"The roadmap prose (`README.md`) is definitive. This file is
representative, not exhaustive."* They are internally consistent with their
`Suggested.lean` siblings, which is precisely why R-1 applies to both halves
equally — the README for a 100%-delivered topic describes it as forthcoming too.

`ForTauCetiRoadmap.lean` is thirteen lines and is the clearest small file in the
repository: it explains why an intentionally empty root module exists (a
`lean_lib` needs a root to resolve, and without it `lake build ForTauCetiRoadmap`
reports "some modules have bad imports"), and it records what the library bought
— *"three of the six files carried ten elaboration errors, in files whose whole
purpose is to show a reviewer what the API will look like."* **That is a file
whose existence is justified in the file**, which is the standard the rest of
this audit has been measuring against.
