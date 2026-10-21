# DKPS -> TauCeti: contribution and mathematical-lineage census

**Status: initial, intentionally incomplete audit (2026-10-21).** This is a
maintained *provenance and results* record, not a PR action queue, a theorem
census, or a claim of exclusive mathematical authorship. Its purpose is to make
it possible to say exactly which results in TauCeti benefited from the Kitware
DKPS formalization, what the relationship was, and which connections remain
uninvestigated. The census is about mathematics and formal proofs, not just the
person who opened a PR.

## Evidence and attribution rules

A contribution may be **ported** (proof/declaration adapted from this repository),
**developed from** (a new upstream proof built on a construction or result first
formalized here), **campaign-associated** (submitted in the DKPS port effort but
exact derivation not established), or **independently developed** (the same
roadmap topic was solved without using the donor implementation). Do not collapse
these relationships into one number. In particular:

- An explicit donor path or provenance statement in a PR body is evidence of a
  *claimed source relationship*, not proof of line-by-line identity. Check its
  final accepted diff against the original source before classifying an exact
  proof as copied, adapted, specialized, generalized, or newly proved.
- A roadmap node shared by DKPS and TauCeti is **not** evidence of proof descent.
  An independent author may prove the same mathematical result or build a
  stronger abstraction. Do not retroactively attribute independent work to DKPS.
- Keep layered ancestry: some DKPS PVM results were themselves adapted from
  Adam Bornemann's Spectra development. Preserve that contribution, license,
  and the precise transformation as the result moves upstream.
- Distinguish **submitted**, **Bors-marked closed**, and **verified on main**.
  TauCeti's Bors workflow can leave GitHub API fields `merged=false` even when
  the PR has a `[Merged by Bors]` title. A Bors title is evidence of integration;
  inspect the accepted main commit/file when making a definitive on-main claim.
  Conversely, ordinary `closed` does not imply accepted.
- Record the precise statement and hypothesis scope, not an entire roadmap
  milestone if the PR delivered only one piece. A replacement that cites DKPS
  but is deliberately re-proved against new abstractions is not an unchanged port.

**Evidence codes in the tables:** `D` = the PR text explicitly attributes a
port/adaptation or donor source; `C` = campaign/roadmap relationship is recorded,
but mathematical descent is not independently audited; `I` = independent or
explicitly not adapted from DKPS. `M13` = the main-file integration was checked
in the October 13 campaign audit; `B` = presently Bors-marked closed, but the
accepted diff has not yet been compared declaration-by-declaration in this
census. Evidence is as of 2026-10-21 unless a dated source is given.

## A. PRs with explicit DKPS origin and Bors integration evidence

These are **contributions we can reasonably describe as originating in or
adapted from the DKPS formalization**, subject to the scope and proof-diff audit
still needed. The PR links contain the first layer of provenance. `M13` is
historical evidence of main-file presence, not a claim that today's source is
byte-identical.

| TauCeti PR | Result or roadmap slice actually contributed | Donor/source relationship in PR | Evidence |
| --- | --- | --- | --- |
| [#13329](https://github.com/TauCetiProject/TauCeti/pull/13329) | PD-A08/A09: square-root displacement estimates | `ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`; proof origins specified | D, M13 |
| [#13331](https://github.com/TauCetiProject/TauCeti/pull/13331) | MSS-B03: matrix entrywise/operator bound | DKPS matrix and `PiL2` estimates, with source named | D, M13 |
| [#13333](https://github.com/TauCetiProject/TauCeti/pull/13333) | PD-A02–A06: orthonormal subfamily spans | `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean` | D, M13 |
| [#13475](https://github.com/TauCetiProject/TauCeti/pull/13475) | MSS-A08: exact-rank factorization uniqueness | `ForTauCeti/LinearAlgebra/Matrix/RankFactorization.lean` | D, B |
| [#13599](https://github.com/TauCetiProject/TauCeti/pull/13599) | PD-A50–A53: Courant–Fischer and Weyl | `ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean` | D, M13 |
| [#13866](https://github.com/TauCetiProject/TauCeti/pull/13866) | OI: approximation-number equivalence/isometric invariance | DKPS approximation-number results; cites an exact donor commit/path | D, B |
| [#13869](https://github.com/TauCetiProject/TauCeti/pull/13869) | SA: Stone generator/commutant with C0-groups | Adapted Kitware DKPS partial-operator/group infrastructure | D, B |
| [#13871](https://github.com/TauCetiProject/TauCeti/pull/13871) | SA: closed partial operators, graphs and form bounds | Adapted DKPS `LinearPMap` foundations; some Spectra ancestry | D, B |
| [#13872](https://github.com/TauCetiProject/TauCeti/pull/13872) | SA-D30: C-star spectral-gap inverse **only** | Adapted DKPS `ForMathlib/.../SelfAdjointGapInverse.lean`, not full unbounded resolvents | D, M13 |
| [#13874](https://github.com/TauCetiProject/TauCeti/pull/13874) | SSP-C25/C26/C30: per-eigenvector double-angle estimates | `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Vector.lean` | D, B |
| [#13875](https://github.com/TauCetiProject/TauCeti/pull/13875) | MSS-B16–B19: probability/convergence-in-measure support | DKPS measure-theory support; not the full matrix spectral-statistics topic | D, M13 |
| [#17527](https://github.com/TauCetiProject/TauCeti/pull/17527) | SA-B14–B23: abstract projection-valued measures | DKPS `ProjValMeasure/Basic.lean`, itself adapted from Spectra | D, B |
| [#18895](https://github.com/TauCetiProject/TauCeti/pull/18895) | SA-B24: countable orthogonal PVM splitting | Generalized DKPS proof from real Borel sets to arbitrary measurable spaces | D, B |
| [#18904](https://github.com/TauCetiProject/TauCeti/pull/18904) | SA-B04: polarized diagonal spectral pairing | DKPS `BorelCalculus/Polarization.lean` | D, B |
| [#18907](https://github.com/TauCetiProject/TauCeti/pull/18907) | SA-B02: simultaneous continuous approximation | DKPS `BorelCalculus/Polarization.lean` / related approximation infrastructure | D, B |
| [#18915](https://github.com/TauCetiProject/TauCeti/pull/18915) | SA-E28: self-adjoint `LinearPMap` maximality | DKPS `LinearPMap/SelfAdjointMaximal.lean` | D, B |
| [#18917](https://github.com/TauCetiProject/TauCeti/pull/18917) | SA-C66–C72: domain-aware Sylvester | DKPS `LinearPMap/Sylvester.lean` | D, B |
| [#18918](https://github.com/TauCetiProject/TauCeti/pull/18918) | SA-C62–C65: real spectral-set separation | DKPS `LinearPMap/Closed.lean`, adapted to canonical spectrum | D, B |
| [#18935](https://github.com/TauCetiProject/TauCeti/pull/18935) | SA-E41: reassembly of block lower bounds | DKPS block lower-bound mathematics, refactored for upstream | D, B |
| [#18937](https://github.com/TauCetiProject/TauCeti/pull/18937) | SA-D13: closed/measurable real spectrum | DKPS `LinearPMap/ResolventOpen.lean`; canonical upstream spectrum reused | D, B |
| [#18946](https://github.com/TauCetiProject/TauCeti/pull/18946) | SSP-D06: Hermitian dilation | Adapted from DKPS rectangular-operator formalization | D, B |
| [#18947](https://github.com/TauCetiProject/TauCeti/pull/18947) | SSP-S01: internal point-spectrum gap | Adapted from DKPS point-spectral-gap result | D, B |
| [#18985](https://github.com/TauCetiProject/TauCeti/pull/18985) | SSP-D02: directed Frobenius sine | DKPS `SinTheta/Frobenius.lean` | D, B |
| [#18991](https://github.com/TauCetiProject/TauCeti/pull/18991) | SSP-D04/D05: left/right singular subspaces | Adapted from DKPS singular-subspace results | D, B |
| [#19000](https://github.com/TauCetiProject/TauCeti/pull/19000) | SA-B40/B41: polarized PVM complex measures | Adapted from DKPS polarized PVM development | D, B |
| [#19005](https://github.com/TauCetiProject/TauCeti/pull/19005) | SA-B49: PVM almost-everywhere/null-set filter | Adapted from Kitware DKPS PVM measure theory | D, B |
| [#19229](https://github.com/TauCetiProject/TauCeti/pull/19229) | SSP-D12: singular-subspace Gram perturbation | Adapted from DKPS singular-subspace perturbation theory | D, B |
| [#19252](https://github.com/TauCetiProject/TauCeti/pull/19252) | SSP-C20: equal-rank spectral projector bound | Based on maintained DKPS projection/perturbation proof | D, B |

*This table is not a claim that all 28 PRs merged through GitHub's native merge
API or that all their final declarations have been rechecked on current main.*
The October 13 source audit independently established the six `M13` cases;
other rows currently rely on the PR provenance text and Bors integration label.

## B. DKPS-origin submissions without established upstream integration

These are relevant to the contribution history, but are **not** counted as
accepted results. State was checked against the TauCeti PR pages on 2026-10-21,
not copied from the older October 13/19 campaign snapshots. Closed-without-Bors
includes proposals later superseded by independent upstream mathematics or
closed for roadmap scope; such a proposal is still a historical contribution
attempt, not an accepted TauCeti theorem.

| PRs | Topic / disposition to investigate | 2026-10-21 status |
| --- | --- | --- |
| [#13861](https://github.com/TauCetiProject/TauCeti/pull/13861), [#13862](https://github.com/TauCetiProject/TauCeti/pull/13862), [#13863](https://github.com/TauCetiProject/TauCeti/pull/13863) | Polar functional calculus, partial isometries, singular-system proposal; independent/canonical implementations overtook portions | Closed, no Bors label |
| [#13864](https://github.com/TauCetiProject/TauCeti/pull/13864) | Orthogonal geometry and reducing subspaces; check which local declarations were subsequently accepted elsewhere | Closed, no Bors label |
| [#13865](https://github.com/TauCetiProject/TauCeti/pull/13865) | Local majorization/gauges; overlaps independently integrated #14102/#14197/#14662 | Closed, no Bors label |
| [#13867](https://github.com/TauCetiProject/TauCeti/pull/13867) | Operator ideals and Schatten family proposal | Closed, no Bors label |
| [#13868](https://github.com/TauCetiProject/TauCeti/pull/13868) | Haagerup–Zsidó Fourier/Sylvester kernel proposal | Closed, no Bors label |
| [#13870](https://github.com/TauCetiProject/TauCeti/pull/13870) | Borel calculus / PVM proposal; compare with later smaller accepted PVM ports | Closed, no Bors label |
| [#13873](https://github.com/TauCetiProject/TauCeti/pull/13873) | Sylvester / Rosenblum operator proposal | Closed, no Bors label |
| [#13876](https://github.com/TauCetiProject/TauCeti/pull/13876) | Matrix moments, centered scatter, concentration support | Closed, no Bors label |
| [#13877](https://github.com/TauCetiProject/TauCeti/pull/13877), [#13878](https://github.com/TauCetiProject/TauCeti/pull/13878) | Berge approximation / RCLike transport (outside original issue #776 scope) | Closed, no Bors label; `#13878` precise proof descent unverified |
| [#13879](https://github.com/TauCetiProject/TauCeti/pull/13879), [#13880](https://github.com/TauCetiProject/TauCeti/pull/13880), [#13881](https://github.com/TauCetiProject/TauCeti/pull/13881), [#13882](https://github.com/TauCetiProject/TauCeti/pull/13882) | Compact-spectrum classification, L2 transport, separable spectral multiplicity, fourth-order/PDE work; all need new roadmap/declaration audit | Closed, no Bors label |
| [#16156](https://github.com/TauCetiProject/TauCeti/pull/16156) | PD-B41/B43 Gram-defect near-isometry proposal; refactored to consume independent #16127 | Closed, no Bors label |
| [#16293](https://github.com/TauCetiProject/TauCeti/pull/16293) | MSS-B11–B13 Hermitian threshold-projector proposal citing DKPS source | Closed, no Bors label; acceptance not established |
| [#19009](https://github.com/TauCetiProject/TauCeti/pull/19009) | SA-B42 older variation attempt; explicitly replaced by #19145 | Closed, no Bors label |
| [#18927](https://github.com/TauCetiProject/TauCeti/pull/18927), [#18942](https://github.com/TauCetiProject/TauCeti/pull/18942) | SA-E32–E34 spectral grid and SSP-D01 ordered eigenframes | Open |
| [#19242](https://github.com/TauCetiProject/TauCeti/pull/19242), [#19268](https://github.com/TauCetiProject/TauCeti/pull/19268), [#19277](https://github.com/TauCetiProject/TauCeti/pull/19277) | SSP-C23 pairwise pi/2; SSP-C19 spectral residual; SSP-C09/C10 reduced extensions | Open |
| [#19299](https://github.com/TauCetiProject/TauCeti/pull/19299), [#19329](https://github.com/TauCetiProject/TauCeti/pull/19329), [#19338](https://github.com/TauCetiProject/TauCeti/pull/19338) | SSP-C27 Gram transfer; SSP-C28/C29 sine-to-tangent; SSP-D19 right singular-vector gap | Open |

The first-wave campaign's `manifest.json` and `roadmap_port_index.json`
record additional target-node detail. An old prepared branch, an unmerged PR,
or a local verification is not evidence that TauCeti accepted the result.

## C. Related or independently implemented results: **do not claim as DKPS ports**

These PRs must appear in the census so an eventual narrative can explain
*why* some donor files disappeared and how the mathematical theory developed,
without assigning donor provenance to independent work.

| Upstream PR | Result / relationship | Current provenance judgment |
| --- | --- | --- |
| [#13247](https://github.com/TauCetiProject/TauCeti/pull/13247) | OG-01–OG-08 Gram rigidity | Independently submitted by `sqrt-of-2`; not a DKPS code port |
| [#13380](https://github.com/TauCetiProject/TauCeti/pull/13380) | PD-A07 eigenvector cross term | Independently submitted by `roed-math`; not a DKPS port |
| [#14102](https://github.com/TauCetiProject/TauCeti/pull/14102) | MAJ-A weak majorization/transfer descent | Independently developed by `tauceti-ai-for-science` |
| [#14197](https://github.com/TauCetiProject/TauCeti/pull/14197) | MAJ-A singular-value majorization/factor domination | Independently developed by `tauceti-ai-for-science` |
| [#14662](https://github.com/TauCetiProject/TauCeti/pull/14662) | MAJ-B unitarily invariant seminorm gauge representation | Independently developed by `tauceti-ai-for-science` |
| [#16127](https://github.com/TauCetiProject/TauCeti/pull/16127) | PD-B21/B41–B43 unitary polar decomposition/near-isometry | PR explicitly mentions the DKPS implementation **but says its proof was independently written**, not copied or adapted. Important negative provenance evidence |
| [#16691](https://github.com/TauCetiProject/TauCeti/pull/16691) | SSP-C21/C22 Frobenius/Ky Fan sine corollaries | Specializes accepted TauCeti sin-theta API; no direct donor-source claim found in PR body. Investigate indirect proof-lineage relationship |
| [#18982](https://github.com/TauCetiProject/TauCeti/pull/18982) | SA-B25 measurable PVM reindexing | Builds on accepted PVM foundation; no direct donor-source claim in PR body; relationship still to audit |
| [#19010](https://github.com/TauCetiProject/TauCeti/pull/19010) | SSP-D13 dilation perturbation isometry | Builds on accepted DKPS-derived #18946; conceptual descendant possible, but direct source reuse unverified |
| [#19145](https://github.com/TauCetiProject/TauCeti/pull/19145) | SA-B42 sharp polarized PVM variation | Follows accepted DKPS-related PVM infrastructure and supersedes #19009; direct donor lineage not yet demonstrated |

Do not convert *"depends on a library whose earlier theorem came from DKPS"*
into *"this entire new proof originated in DKPS"*. A transitive dependency and
an actual proof or mathematical idea lineage are distinct relationships.

## D. Incomplete Hilbert-space roadmap audit: remaining research

The census is **not exhaustive**. The attached `tauceti-dkps-campaign`
repository (snapshot of 2026-10-21, historical records last refreshed around
2026-10-13/19) covers a first wave and a newer SA/SSP wave, not all external
PRs, all roadmap items, or the final source of every upstream theorem. A
follow-up should cross-reference **every** Hilbert/operator-theory roadmap
milestone against the actual DKPS formalization at its historical proof commits,
including developments submitted by other contributors and results that were
reformulated before integration.

Priority comparison families:

1. `PolarDecomposition`, `OrthogonalGeometry`, `PrincipalAngles`, and
   `Majorization`: independent Gram, polar, angle and gauge implementations;
   determine overlap at the level of theorem statements, proof arguments and
   prerequisite lemmas.
2. `OperatorIdeals` and `SpectralSubspacePerturbation`: singular/approximation
   numbers, symmetric-gauge families, Sylvester/Rosenblum estimates, projection
   gaps, Frobenius/Ky Fan bounds, double-angle/tangent results. Distinguish
   directly ported proof steps from independently rebuilt reductions.
3. `SelfAdjointSpectralTheory`: closed/unbounded partial operators, resolvents,
   spectral sets, PVMs, Borel calculus, spectral grids, domain-sensitive
   restrictions. Track whether an upstream replacement actually removes donor
   implementation and whether hypotheses retain the original scope.
4. `MatrixSpectralStatistics`: rank factorization, eigenframe/threshold
   projectors, concentration, and population-gap results. Distinguish accepted
   narrow support lemmas from a complete theorem chain.
5. Related scopes outside intention #776 (Berge, compact-spectrum
   classification, spectral multiplicity, L2 transport, fourth-order examples):
   record whether the contribution originated here without claiming it landed
   under an unrelated roadmap.

For each accepted PR, capture: PR link and current integration commit; original
DKPS file/declaration and *historical* commit; exact accepted declaration;
comparison of statements (scalar field, dimension, domains, constants, ideal
classes); proof origin (`copied`, `adapted`, `generalized`, `independently
re-proved`, `enabling dependency`, or `unknown`); pre-DKPS ancestry (including
Spectra where applicable); and the downstream donor definitions and bridges
actually retired. The proposed evidence chain is:

`original proof commit -> donor declaration -> campaign extraction -> PR final
diff -> accepted TauCeti declaration -> DKPS consumer migration`.

**Reproducibility anchors:**

- Maintained DKPS proof before upstream-first migration:
  [`acac427e5a34`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/commit/acac427e5a34b769bfe52359216acfc6b6dd5582).
- Canonical-spectrum pause point:
  [`2bca6ddd1558`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/commit/2bca6ddd155878315acdcef2e93049d218d524b3).
- Beginning of the Oct 21 upstream-consumption overlays: DKPS `7cd3d7a11b91`;
  TauCeti dependency `87dad819828705ed8329ff53b9bc53634a064b1a`.
- Earlier campaign donor archive commit: `caf638a3b494b6cf77b26a6b5dc7c9df4653cd49`
  from `tauceti-dkps-campaign/manifest.json` (not the latest DKPS checkout).
- Companion historical records: `tauceti-dkps-campaign/{manifest.json,
  roadmap_port_index.json,port_wave.json,CURRENT_PORT_WAVE.md}`.
- Original Spectra contribution record:
  [`spectra-provenance-map.md`](spectra-provenance-map.md) and
  `retired/Spectra.UPSTREAM.md` in this repository.
- Roadmap intention: [TauCetiRoadmap #776](https://github.com/TauCetiProject/TauCetiRoadmap/issues/776).

This is a **manually curated starting point**. Revisit the status and source
classification when a PR changes or a new historical proof comparison is
performed; do not silently convert a hypothesis of influence into an accepted
attribution claim. There is no need for a new polling script or checker.
