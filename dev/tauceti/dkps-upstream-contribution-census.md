# DKPS -> TauCeti: contribution and mathematical-lineage census

**Status: expanded, intentionally incomplete audit (2026-10-21; PR/intent/main cross-check).** This is a
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
in the October 13 campaign audit; `M21` = the named accepted declaration
was located on TauCeti `main` on October 21 (not a final-diff/commit audit); `B` = presently Bors-marked closed, but the
accepted diff has not yet been compared declaration-by-declaration in this
census. Evidence is as of 2026-10-21 unless a dated source is given.

## Intention #776: scope, explicit references, and comparison discipline

[OperatorTheory integration intention #776](https://github.com/TauCetiProject/TauCetiRoadmap/issues/776)
was read directly on 2026-10-21, along with its claim discussion. It
specifically proposes integrating **already-formalized, source-backed DKPS
mathematics** into eight TauCeti roadmaps; it does **not** claim ownership
of those whole roadmaps or of independently completed results. The intention
explicitly names three initial DKPS ports—[#13329](https://github.com/TauCetiProject/TauCeti/pull/13329),
[#13331](https://github.com/TauCetiProject/TauCeti/pull/13331),
and [#13333](https://github.com/TauCetiProject/TauCeti/pull/13333)—and
explicitly excludes the independently undertaken Gram-rigidity
[#13247](https://github.com/TauCetiProject/TauCeti/pull/13247) and
eigenvector-cross-term [#13380](https://github.com/TauCetiProject/TauCeti/pull/13380).
These five references are *in the issue body*; later PRs must be linked by
independent PR-body/accepted-source evidence, not described as individually
listed in the original intention.

The eight claimed areas and the maintained donor-topic mapping
([`roadmap-topic-map.md`](roadmap-topic-map.md)) are:

| Roadmap within intention #776 | DKPS topics | Representative PRs in this census (not a claim that all are direct ports) |
| --- | --- | --- |
| PolarDecomposition | T01–T03 | #13329, #13333, #13599: DKPS ports; #16127, #16450: independent implementations |
| OrthogonalGeometry | T26 | #13247: independent Gram rigidity; #13980: canonical reducing/projection API refinement |
| Majorization | T05, T07 | #14241: adapted rectangular UI seminorms; #14026, #14102, #14197: independently developed results |
| PrincipalAngles | T04, T06, T08 | #15983: equal-rank projection-gap identity; #15340: independent overlap operator; compare donor proofs |
| OperatorIdeals | T09–T11 | #13866: DKPS-derived approximation-number results; #14501, #14589, #16010: independently proved overlap |
| SelfAdjointSpectralTheory | T13, T14, T15a–T15c | #17527, #18917, #19000: adapted foundations; #19145: new variation bound on that foundation |
| SpectralSubspacePerturbation | T12, T16–T18 | #19252, #19229: DKPS-related; #16545: canonical sine-theta prerequisite built upstream |
| MatrixSpectralStatistics | T19–T21 | #13331, #13475: adapted results; #15360, #15962, #16322: independent overlapping developments |

*The topic codes are donor ownership/grouping metadata, not a claim that
every numbered milestone has been upstreamed.* Intention #776 is a
**starting source boundary**, not a closed list of PRs; the historical
campaign tracker and accepted main tree provide subsequent evidence.

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
| [#14241](https://github.com/TauCetiProject/TauCeti/pull/14241) | MAJ/OI: rectangular unitarily invariant seminorms, orbit certificates and zero extension | PR explicitly adapts `ForTauCeti/.../UnitarilyInvariantSeminorm/Basic.lean` and `ZeroExtension.lean` to canonical API | D, B |
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
| [#19229](https://github.com/TauCetiProject/TauCeti/pull/19229) | SSP-D12: singular-subspace Gram perturbation | Adapted from DKPS singular-subspace perturbation theory | D, M21 |
| [#19252](https://github.com/TauCetiProject/TauCeti/pull/19252) | SSP-C20: equal-rank spectral projector bound | Based on maintained DKPS projection/perturbation proof | D, M21 |
| [#19268](https://github.com/TauCetiProject/TauCeti/pull/19268) | SSP-C19: canonical spectral-subspace residual sine bound | Adapted from `ForTauCeti/.../SinTheta/DirectedBounds.lean` and `.../Spectral/Subspace.lean`; the accepted module names both donor sources | D, M21 |

*This table is not a claim that all 29 PRs merged through GitHub's native merge
API or that all their final declarations have been rechecked on current main.*
The October 13 source audit independently established the six `M13` cases;
other rows rely on the PR provenance text and Bors integration label unless
explicitly marked `M21`. The `M21` rows are #19229, #19252, and #19268: the
named `SingularSubspace/Perturbation.lean`, `Projection/SpectralPerturbation.lean`,
and `UnitarilyInvariantSeminorm/SinTheta/Spectral.lean` declarations were found
on TauCeti main. The PR provenance identifies the DKPS donor modules; final
proof descent remains subject to a declaration-level diff audit.

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
| [#19242](https://github.com/TauCetiProject/TauCeti/pull/19242), [#19277](https://github.com/TauCetiProject/TauCeti/pull/19277) | SSP-C23 pairwise pi/2; SSP-C09/C10 reduced extensions | Open |
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
| [#19145](https://github.com/TauCetiProject/TauCeti/pull/19145) | SA-B42 sharp polarized PVM variation (`M21`: on main) | **New downstream proof** on DKPS-derived PVM/polarization foundations; replaces closed #19009, not an unchanged DKPS proof |

### Accepted overlap and additional roadmap PRs omitted from the initial census

A new scan of TauCeti PR descriptions found the following **29 additional
Bors-marked PRs** (besides the direct #14241 above). These belong in the
historical result map even when they do **not** support a claim of direct DKPS
proof adaptation. `I` means the PR expressly denies using/porting the donor
(or describes an independent derivation); `C` means a dependency, parallel
construction or roadmap match merits further comparison, but direct proof
descent is not established. A Bors title here is not yet a full accepted-diff
audit. The original mathematical work of other contributors remains credited.

| PR | Roadmap result or API | Relationship to DKPS |
| --- | --- | --- |
| [#13839](https://github.com/TauCetiProject/TauCeti/pull/13839) | PD: adjoint/singular-value symmetry | I: PR explicitly does not follow the donor proof |
| [#13967](https://github.com/TauCetiProject/TauCeti/pull/13967) | PD-C09–C18: finite singular system | C: accepted named singular-system implementation; donor descent not established |
| [#13980](https://github.com/TauCetiProject/TauCeti/pull/13980) | OG: canonical reducing and projection API | C: extends existing API; retains DKPS attribution for a prior projection-completeness observation, not a fresh bulk port |
| [#14026](https://github.com/TauCetiProject/TauCeti/pull/14026) | MAJ-A18–A25: forward Schur–Horn | I: PR explicitly states from-scratch proof |
| [#14501](https://github.com/TauCetiProject/TauCeti/pull/14501) | OI: elementary approximation-number calculus | I: developed independently of DKPS port #13866 |
| [#14589](https://github.com/TauCetiProject/TauCeti/pull/14589) | OI: approximation number/rank/compactness | I: explicitly independent of DKPS port #13866 |
| [#14936](https://github.com/TauCetiProject/TauCeti/pull/14936) | SSP: Haagerup–Zsidó kernel | I: independently proved, no use of DKPS port #13868 |
| [#15200](https://github.com/TauCetiProject/TauCeti/pull/15200) | PA: trace and Hoffman–Wielandt inequalities | I: expressly not a DKPS port |
| [#15211](https://github.com/TauCetiProject/TauCeti/pull/15211) | PA-B41: Davis eigenvalue change | I: expressly does not port DKPS proof |
| [#15340](https://github.com/TauCetiProject/TauCeti/pull/15340) | PA: family overlap and principal cosines | I: expressly does not port DKPS implementation |
| [#15360](https://github.com/TauCetiProject/TauCeti/pull/15360) | MSS: positive-semidefinite Gram factorization | I: DKPS formalization explicitly not consulted |
| [#15375](https://github.com/TauCetiProject/TauCeti/pull/15375) | SSP: Haagerup–Zsidó kernel L1 mass | I: direct proof against upstream API, not donor port |
| [#15457](https://github.com/TauCetiProject/TauCeti/pull/15457) | SSP: Lyapunov/separated Sylvester | I: expressly independent of related DKPS proposal #13873 |
| [#15668](https://github.com/TauCetiProject/TauCeti/pull/15668) | PD/SA: Hilbert complexification | C: explicitly cites parallel DKPS construction; proof-copy relationship unestablished |
| [#15899](https://github.com/TauCetiProject/TauCeti/pull/15899) | SA: real Hilbert functional calculus | I: distinct method from acknowledged DKPS real calculus; no code copied |
| [#15917](https://github.com/TauCetiProject/TauCeti/pull/15917) | OI: symmetric gauges on sequences | I: written from sources, not DKPS |
| [#15931](https://github.com/TauCetiProject/TauCeti/pull/15931) | MSS: Hermitian CFC and spectral projectors | I: explicitly not drawn from DKPS implementation |
| [#15962](https://github.com/TauCetiProject/TauCeti/pull/15962) | MSS-C01–C05: sample moments/Chebyshev | I: expressly independent of DKPS proposal #13876 |
| [#15976](https://github.com/TauCetiProject/TauCeti/pull/15976) | SSP: dimension-free Davis–Kahan sine | I: expressly independent of original DKPS port |
| [#15983](https://github.com/TauCetiProject/TauCeti/pull/15983) | PA-B29: equal-rank directed projection-gap identity | C: independent mathematical proof using canonical gap API; prerequisite for DKPS-related #19252 |
| [#16010](https://github.com/TauCetiProject/TauCeti/pull/16010) | OI: Hilbert–Schmidt energy | I: expressly independently formalized |
| [#16061](https://github.com/TauCetiProject/TauCeti/pull/16061) | SSP: interval/exterior Sylvester in UI seminorms | I: expressly independently formalized |
| [#16152](https://github.com/TauCetiProject/TauCeti/pull/16152) | SSP: angular/graph subspaces | I: expressly independently formalized |
| [#16260](https://github.com/TauCetiProject/TauCeti/pull/16260) | SA: RCLike continuous functional calculus | I: new proofs follow Mathlib, no donor code copied; retained credit for old DKPS real calculus |
| [#16322](https://github.com/TauCetiProject/TauCeti/pull/16322) | MSS: empirical second moments/concentration | I: expressly independently formalized |
| [#16382](https://github.com/TauCetiProject/TauCeti/pull/16382) | SSP/YWS: population-gap eigenblock residuals | I: expressly independently formalized |
| [#16450](https://github.com/TauCetiProject/TauCeti/pull/16450) | PD: canonical polar factor/unitary extensions | I: expressly not copied or adapted from DKPS |
| [#16545](https://github.com/TauCetiProject/TauCeti/pull/16545) | SSP-C17/C18: finite-dimensional interval/exterior sine theorem | C: canonical prerequisite of #19252; proof uses upstream Sylvester machinery, no direct donor-port claim |
| [#16661](https://github.com/TauCetiProject/TauCeti/pull/16661) | SSP/PA: Rayleigh–Ritz, Ritz residual and trial-map angles | I: expressly independently formalized |

These 29 rows and direct #14241 add **30 PRs previously absent from the
65-reference first census**, giving 95 distinct referenced PRs in the
expanded starting ledger. This count describes links *documented*, not
accepted DKPS-derived proofs. It is not an exhaustive search of TauCeti PR
history or a final accepted-commit audit.

Do not convert *"depends on a library whose earlier theorem came from DKPS"*
into *"this entire new proof originated in DKPS"*. A transitive dependency and
an actual proof or mathematical idea lineage are distinct relationships.

## D. October 21 integration-to-retirement frontier: what the three merges unlock

Four PRs were checked against their final subject modules on TauCeti `main`
on 2026-10-21, not merely against Bors titles. Their upstream declarations
are present. **No code is deleted by recording their acceptance.** The
maintained DKPS baseline for the retirement comparisons is commit
`ec7c6d13`, which includes the earlier canonical restriction, seminorm, and
singular-subspace migrations. The C19 consumption below was then compiled in
an isolated checkout against the newly pinned TauCeti main revision.

| Accepted PR and main API | Candidate donor consumers | What can be removed; what must remain |
| --- | --- | --- |
| [#19252](https://github.com/TauCetiProject/TauCeti/pull/19252), `Submodule.mul_projectionGap_le_norm_sub_of_pointIntervalExteriorGap` and `Module.End.mul_norm_sub_starProjection_pointSpectralSubspace_le` in `Projection/SpectralPerturbation.lean` | `ForTauCeti/.../SinTheta/Perturbation.lean`: `opNorm_projection_sub_projection_le` and `opNorm_spectralProjection_sub_spectralProjection_le` | **Upstream consumption:** both local finite-dimensional constant-one duplicates were removed; repository search found no maintained callers. The paper-facing half-line estimate `opNorm_pointSpectralSubspace_sub_le` remains because it has no equal-rank premise and a different spectral-gap shape. Infinite-dimensional, unbounded, and ideal-norm projector results also remain. Depends on independent upstream gap identity [#15983](https://github.com/TauCetiProject/TauCeti/pull/15983) and sine theorem [#16545](https://github.com/TauCetiProject/TauCeti/pull/16545). |
| [#19229](https://github.com/TauCetiProject/TauCeti/pull/19229), `LinearMap.mul_norm_sinThetaMap_rightSingularSubspace_le` and `...leftSingularSubspace_le` in `SingularSubspace/Perturbation.lean` | `YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`: `rightSingularSubspace_sinTheta_le` and `leftSingularSubspace_sinTheta_le`; removed donor-only singular-subspace definitions | **Upstream consumption:** the two paper-facing theorem names were retained and their mathematical estimates already compiled when forwarded to #19229. This follow-on retirement changes their binder types to canonical `Module.End.PointIntervalExteriorGap`, their selected subspaces to `LinearMap.rightSingularSubspace` / `.leftSingularSubspace`, and their sine maps to `Submodule.sinThetaMap`. It deletes two legacy definitions and four private proof conversions. The original donor statement used a common `Icc a b` selection and explicit `0 < δ`; these conditions remain in the new specializations, while upstream itself permits arbitrary separate spectral sets and does not need strict positivity. YWS Hermitian dilation, Gram blocks, and other application results remain, as they are not superseded by these two theorems. |
| [#19268](https://github.com/TauCetiProject/TauCeti/pull/19268), `UnitarilyInvariantSeminorm.mul_map_starProjection_orthogonal_pointSpectralSubspace_comp_le_map_sylvester_apply` (and its automatic-`Ioo` specialization) in `UnitarilyInvariantSeminorm/SinTheta/Spectral.lean` | `ForTauCeti/.../SinTheta/Perturbation.lean`: `sinTheta_pointSpectralSubspace_le` | **Upstream consumption:** the finite-dimensional canonical spectral-selection proof now applies the accepted residual theorem to the compressed reference operator and transports the rectangular sine/residual back through the subspace inclusion. The source-facing declaration, positive-gap premise, selected interval, exterior-spectrum premise, and constant remain unchanged. Generic invariant-subspace, ordered-gap, general spectral-distance, and unbounded theorems remain because C19 does not subsume them. |
| [#19145](https://github.com/TauCetiProject/TauCeti/pull/19145), `ProjValMeasure.polarizedComplexMeasure_variation_univ_le` and `instIsFiniteMeasurePolarizedVariation` in `ProjValMeasure/Variation.lean` | Spectral-measure integration and polarized-measure consumers; inspect `ForTauCeti/Analysis/InnerProductSpace/{ProjValMeasure,BorelCalculus,LinearPMap}` as dependencies become canonical | **No matching maintained local variation theorem was found to delete wholesale.** This is a new sharp bound using DKPS-derived PVM/polarization infrastructure from #17527/#19000, not proof that all donor Borel calculus or unbounded spectral measures can be retired. Enable the canonical `IsFiniteMeasure` instance at qualified consumer sites and eliminate local ad hoc domination arguments only if a true duplicate is located. Replaces closed attempt [#19009](https://github.com/TauCetiProject/TauCeti/pull/19009). |

**Historical dependency pin:** the October 21 YWS consumption overlay updated TauCeti
from `87dad819828705ed8329ff53b9bc53634a064b1a` to
`f91b6396a35d847a87a0d37519325918356bc0fc`, preserving the Lean 4.36.0-rc1
and Mathlib pins. The YWS two-theorem forwarding overlay (v3) compiled at that
pin, as confirmed by the DKPS maintainer. The follow-on canonical-interface
retirement was likewise completed before the present spectral-subspace migration.
Keep the former pin for historical regression triage. This consumption run
verified live TauCeti `main` at `7205a079ee99f6962eb39fadd8067517ae38bf73`
with the same Lean toolchain and Mathlib revision, then committed that pin in
DKPS commit `5cf2439c`.

**Canonical point-spectral-subspace follow-up (2026-10-21):** the maintained
finite-dimensional donor no longer defines `TauCeti.pointSpectralSubspace`.
The old span-of-eigenvectors representation is already provided by the
accepted `Module.End.pointSpectralSubspace` and its
`Module.End.pointSpectralSubspace_eq_span` characterization in
`TauCeti.Analysis.InnerProductSpace.PointSpectrum` (now pinned at
`7205a079ee99f6962eb39fadd8067517ae38bf73`). The migration uses the
upstream subspace directly in the finite-dimensional `ForTauCeti` perturbation
lemmas, paper-facing Davis–Kahan APIs, and the remaining YWS Hermitian-dilation
corollary. It also retires the redundant local span-equation theorem, replaces
the local eigenspace-independence proof by
`Module.End.pointSpectrumIn_pointSpectralSubspace`, and uses
`Module.End.map_pointSpectralSubspace_le` for invariance. This is **not** a
claim that local `restrictedPointSpectrum`, `PointSpectrumIn`, `IsInvariant`,
or the linear-map-valued `spectralProjection` have been retired: their remaining
consumers and carrier requirements need a distinct migration. The upstream
point-spectral-subspace definition selects precisely the same eigenvector span,
with no extra symmetry or finite-dimensional hypothesis.

**Retirement acceptance criterion:** for each replaced local theorem, record
(1) exact upstream declaration and accepted commit; (2) original statement
and hypothesis comparison, including rank, scalar field, spectra/gap
orientation, domains and constants; (3) actual consumer rewrites and deleted
proof LOC; and (4) successful local Lean build. Merely adding a forwarding
bridge or an upstream import **does not** count as donor retirement.

## E. Incomplete Hilbert-space roadmap audit: remaining research

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

This is a **manually curated, non-exhaustive starting point**. Revisit the status and source
classification when a PR changes or a new historical proof comparison is
performed; do not silently convert a hypothesis of influence into an accepted
attribution claim. There is no need for a new polling script or checker.
