# DKPS -> TauCeti: contribution and mathematical-lineage census

**Status: expanded, intentionally incomplete audit (2026-10-21 baseline; 2026-10-25 Gram and Hilbert–Schmidt consumption updates).** This is a
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
was located on TauCeti `main` on October 21 (not a final-diff/commit audit);
`M22` = the named declaration was checked in the pinned 2026-10-22 TauCeti tree;
`M25` = the accepted commit and donor statements were compared on October 25;
`B` = presently Bors-marked closed, but the
accepted diff has not yet been compared declaration-by-declaration in this
census. Evidence is as of 2026-10-21 unless a dated source is given; see the current [consumption review](upstream-consumption-review-2026-10-22.md).

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
| [#13599](https://github.com/TauCetiProject/TauCeti/pull/13599) | PD-A50–A53: Courant–Fischer and Weyl | `ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean`; developed locally on Mathlib, then adapted upstream | D, M13; [28 October donor/accepted-proof comparison](../../papers/dk_formalization_journal/COURANT_FISCHER_LINEAGE_AUDIT.md) |
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
| [#18942](https://github.com/TauCetiProject/TauCeti/pull/18942) | SSP-D01: eigenfamilies, ordered eigenframes and corresponding eigenblocks | Adapted from `ForTauCeti/Analysis/InnerProductSpace/Spectral/EigenFrame.lean`; gap-separated span/canonical-block results were **not** part of the accepted PR | D, M22 |
| [#19299](https://github.com/TauCetiProject/TauCeti/pull/19299) | SSP-C27 rectangular Gram prerequisites and scalar double-angle identities | Adapted from DKPS `DoubleAngle/Gram.lean` and the isometry-adjoint helper in `RectangularSingularValues.lean`; not the full perturbation inequality | D, M25 |

*This table is not a claim that all these PRs merged through GitHub's native merge
API or that all their final declarations have been rechecked on current main.*
The October 13 source audit independently established the six `M13` cases;
other rows rely on the PR provenance text and Bors integration label unless
explicitly marked `M21`. The `M21` rows are #19229, #19252, and #19268: the
named `SingularSubspace/Perturbation.lean`, `Projection/SpectralPerturbation.lean`,
and `UnitarilyInvariantSeminorm/SinTheta/Spectral.lean` declarations were found
on TauCeti main. The PR provenance identifies the DKPS donor modules; final
proof descent remains subject to a declaration-level diff audit. The `M22`
row #18942 was checked in the pinned `773bcb657352235c6348ff45be9b7f19f147c19e`
tree after Bors closed the PR on October 22; its final proof descent has not
been audited line by line.

### October 25: accepted rectangular Gram prerequisites

PR #19299 is present on accepted main as
`69cd1ab4dcfbb6676e344f3f193e63473eab5a3d`, included in the new dependency
revision `efded067c28ffca3483fd731674eb13b42543fbb`. The accepted source
preserves the Kitware/DKPS provenance and generalizes several isometry-block
hypotheses. This establishes an explicit proof adaptation, not ownership of
all of SSP-C27.

The local retirement patch removes these ten donor declarations without aliases:

- `TauCeti.sin_two_mul_arcsin`, `TauCeti.sin_two_mul_arcsin_sq`;
- `TauCeti.gram_comp_of_gram_eq_id_sub`, `TauCeti.gram_two_smul_comp`,
  `TauCeti.gram_two_smul_comp_apply_of_eigenvector`;
- `TauCeti.gram_isometryBlock_eq_id_sub`,
  `TauCeti.adjoint_comp_isometryBlock_eq_zero`,
  `TauCeti.adjoint_reflection_comp_isometryBlock`,
  `TauCeti.gram_adjoint_reflection_comp_isometryBlock`;
- `TauCeti.LinearIsometry.adjoint_apply_apply`.

Their accepted owners are `Real`, `LinearMap`, and `LinearIsometry`, in
`TauCeti/Analysis/SpecialFunctions/Trigonometric/Arcsin.lean`,
`TauCeti/Analysis/InnerProductSpace/Adjoint.lean`,
`TauCeti/Analysis/InnerProductSpace/PartialIsometry.lean`, and
`TauCeti/Analysis/InnerProductSpace/DoubleAngle/Gram.lean`.
The two maintained scalar consumers use `Real.sin_two_mul_arcsin_sq`
directly. The ambient projector theorem `TauCeti.gram_sinTwoAngleOperator`
remains an unmerged donor result; it is not discarded with the accepted
rectangular prerequisites. The retirement and its consumers passed the full
default build together with the module migration on October 25, with
warnings treated as errors (21,039 jobs).

## B. DKPS-origin submissions without established upstream integration

These are relevant to the contribution history, but are **not** counted as
accepted results. Most states below were checked against the TauCeti PR pages on 2026-10-21
and were not copied from older October 13/19 campaign snapshots. The
SSP-D01 #18942 row moved to the accepted section after its October 22 merge. Closed-without-Bors
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
| [#18927](https://github.com/TauCetiProject/TauCeti/pull/18927) | SA-E32–E34 measurable spectral grid cells | Open |
| [#19242](https://github.com/TauCetiProject/TauCeti/pull/19242), [#19277](https://github.com/TauCetiProject/TauCeti/pull/19277) | SSP-C23 pairwise pi/2; SSP-C09/C10 reduced extensions | Open |
| [#19329](https://github.com/TauCetiProject/TauCeti/pull/19329), [#19338](https://github.com/TauCetiProject/TauCeti/pull/19338) | SSP-C28/C29 sine-to-tangent; SSP-D19 right singular-vector gap | Open |

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
| [#19268](https://github.com/TauCetiProject/TauCeti/pull/19268), `UnitarilyInvariantSeminorm.mul_map_starProjection_orthogonal_pointSpectralSubspace_comp_le_map_sylvester_apply` (and its automatic-`Ioo` specialization) in `UnitarilyInvariantSeminorm/SinTheta/Spectral.lean` | Former `ForTauCeti/.../SinTheta/Perturbation.lean` wrapper `sinTheta_pointSpectralSubspace_le`; canonical seam in `RoadmapBridge/Integration.lean` | **Upstream consumption completed for the redundant wrapper:** the initial compression/transport proof was later deleted in commit `655c57d8`; the `RoadmapBridge` example applies the accepted rectangular residual theorem directly. The generic invariant-subspace, ordered-gap, spectral-distance and unbounded theorems remain because C19 does not subsume them. Do not resurrect the donor wrapper or count that deleted intermediate proof as a maintained theorem. |
| [#18942](https://github.com/TauCetiProject/TauCeti/pull/18942), `Module.End.IsEigenfamily`, `LinearMap.IsSymmetric.IsOrderedEigenframe`, and `LinearMap.IsSymmetric.CorrespondingEigenblocks` in `Spectral/Eigenframe.lean` | `ForTauCeti/.../Spectral/EigenFrame.lean`, `.../Spectral/ResidualGap.lean`, and YWS symmetric, residual, Procrustes, statistics, and rectangular modules | **Compiled consumption:** the local `TauCeti.IsEigenFamily` structure and `TauCeti.IsOrderedEigenframe` predicate and their duplicate basic lemmas are retired. Maintained consumers use canonical `Module.End.IsEigenfamily` / `LinearMap.IsSymmetric.IsOrderedEigenframe` directly, retaining only the non-upstreamed population-gap `span_eq_spanIndices` and `pointInternalGap_span`. **Follow-on comparison overlay:** `YuWangSamworth2015.CorrespondingEigenblock.toCorrespondingEigenblocks` proves that the YWS fixed-eigenbasis datum supplies TauCeti's arbitrary-frame-based `CorrespondingEigenblocks`, transporting the canonical `spanIndices` to the frame spans explicitly. The reverse implication is false without added separation; the narrower local datum and constructors remain for application-specific index selection. Rectangular Gram-transfer dimension/invariance and the YWS interval-block invariance now reuse accepted `CorrespondingEigenblocks` lemmas, retiring the independent local `reduces_spanIndices` proof. The corresponding-block comparison was subsequently compiled and accepted by the maintainer. **Rectangular follow-on:** direct use of the accepted `IsOrderedEigenframe` for the right/left Gram operators retires both local `IsOrdered*SingularFrame` aliases and their reflexive lemmas, while the canonical `CorrespondingEigenblocks` invariance/finrank lemmas replace private Gram-transfer wrappers. The twelve consumers of the local singular-value norm wrapper now use `TauCeti.opNorm_eq_singularValues_zero` directly. This is a presentation and proof-source change, not a new theorem, altered gap, or acceptance claim. The TauCeti pin already includes #18942. |
| [#19145](https://github.com/TauCetiProject/TauCeti/pull/19145), `ProjValMeasure.polarizedComplexMeasure_variation_univ_le` and `instIsFiniteMeasurePolarizedVariation` in `ProjValMeasure/Variation.lean` | Spectral-measure integration and polarized-measure consumers; inspect `ForTauCeti/Analysis/InnerProductSpace/{ProjValMeasure,BorelCalculus,LinearPMap}` as dependencies become canonical | **No matching maintained local variation theorem was found to delete wholesale.** This is a new sharp bound using DKPS-derived PVM/polarization infrastructure from #17527/#19000, not proof that all donor Borel calculus or unbounded spectral measures can be retired. Enable the canonical `IsFiniteMeasure` instance at qualified consumer sites and eliminate local ad hoc domination arguments only if a true duplicate is located. Replaces closed attempt [#19009](https://github.com/TauCetiProject/TauCeti/pull/19009). |

**C19 wrapper retirement follow-up (2026-10-22):** the donor theorem
`sinTheta_pointSpectralSubspace_le` in `SinTheta/Perturbation.lean` was a
square-operator wrapper around the accepted rectangular theorem. Its only
maintained consumer was the `RoadmapBridge` seam; that example now applies
TauCeti's theorem directly with the selected-space inclusion as the trial map,
and derives the compressed spectrum from
`pointSpectrumIn_restrict_iff` plus
`pointSpectrumIn_pointSpectralSubspace`. The 63-line donor wrapper was deleted.
The generic invariant-subspace, ordered-gap, general spectral-distance, and
unbounded estimates remain in DKPS because #19268 does not subsume them.

**Canonical self-adjoint restriction follow-up (2026-10-22):** the donor
`LinearPMap.reducingRestriction_isSelfAdjoint` theorem and its Davis--Kahan
`PartialMap` forwarding theorem have been removed. Their maintained consumers
now apply the accepted `LinearPMap.IsReducing.isSelfAdjoint_restrict` API
directly, using `reducingRestriction_eq_restrict` only to align the retained
local restriction spelling with the upstream `A.restrict` result. The donor
theorem added only a redundant dense-domain premise (already implied by
self-adjointness) and forwarded to that exact upstream theorem. The local
`reducingRestriction` construction remains for its domain-aware consumers; this
change does not claim that the broader restriction bridge has been retired.
The unbounded Section 8 Theorem 8.2 source module now states its spectral
hypotheses and derives its Ritz blocks directly with `A.restrict hred.isInvariant`
and Tau Ceti's public restriction-domain and coercion lemmas; its hypotheses and
conclusions are unchanged.
The unbounded directed scalar-generic `sin 2Θ` source module now also states its
form-gap hypotheses over canonical `A.restrict` operators and uses Tau Ceti's
restriction-domain, coercion, and self-adjointness results directly; the theorem
scope and conclusions are unchanged.
The upstream result is in the canonical reducing API associated with
[#13980](https://github.com/TauCetiProject/TauCeti/pull/13980); that PR remains
classified as related API refinement, not a direct DKPS proof port.
The now-unused donor and Davis--Kahan symmetry forwarding theorems were also
removed; Tau Ceti's `LinearPMap.IsFormalAdjoint.restrict` is the canonical
symmetry-preservation result, and maintained-source search found no callers of
the forwarding names.
The unused local density and closed-graph restriction wrappers were removed
after confirming that no maintained modules consume them; their statements
follow directly from Tau Ceti's `IsReducing.dense_restrict_domain` and
`IsClosed.restrict`. The Davis--Kahan adjoint-domain forwarding alias is also
gone. Its donor theorem remains because the corresponding upstream adjoint-domain
argument is private, so it is not yet replaceable by a public API.

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
The upstream point-spectral-subspace definition selects precisely the same
eigenvector span, with no extra symmetry or finite-dimensional hypothesis.

**Canonical restricted point-spectrum follow-up (2026-10-21):** the duplicate
`TauCeti.restrictedPointSpectrum` and `TauCeti.PointSpectrumIn` definitions,
their two membership lemmas, and the local proof
`pointSpectrumIn_pointSpectralSubspace` have now been retired against the
accepted [#14418](https://github.com/TauCetiProject/TauCeti/pull/14418)
declarations in `TauCeti.Analysis.InnerProductSpace.PointSpectrum`, introduced
by TauCeti commit `1f2ab68732510bdfccdd517505193dc128901c7d` and present in the
pinned tree `7205a079ee99f6962eb39fadd8067517ae38bf73`. Maintained consumers
now use `Module.End.restrictedPointSpectrum`,
`Module.End.mem_restrictedPointSpectrum_iff`,
`Module.End.mem_restrictedPointSpectrum`, `Module.End.PointSpectrumIn`,
`Module.End.pointSpectrumIn_iff`, and
`Module.End.pointSpectrumIn_pointSpectralSubspace` directly. The upstream
predicate and membership statements express the same eigenvalue/eigenvector
conditions as the donor versions, while the accepted APIs work over general
`RCLike` endomorphisms without imposing the donor's inner-product-space
context. Source-facing Davis--Kahan and YWS statements retain their spectral
sets, gap orientations, scalar generality, and conclusions. Consumers that
previously applied `PointSpectrumIn` as a subset now use the public
`pointSpectrumIn_iff` characterization, since the upstream predicate is
intentionally opaque.

The local `restrictedPointSpectrum_restrict` and
`pointSpectrumIn_restrict_iff` results remain as DKPS-specific bridges between
`A.restrict hU` and ambient eigenvectors; #14418 does not provide that transfer
theorem. The former local `LinearPMap.InvariantSubspace` predicate has since
been deleted in favor of Tau Ceti's canonical
`LinearPMap.IsInvariant`/`LinearPMap.isInvariant_iff`, present in the pinned
revision `dded4e1133eb74742ae658ebd8de8d66f8d2b470`. The old definition and
theorem statement both expressed
`∀ x : A.domain, (x : E) ∈ U → A x ∈ U`; the canonical API has exactly that
statement and scalar/carrier scope. The donor `ReducesSubspace` record has since
also been retired. Its four conjuncts are represented by Tau Ceti's canonical
`LinearPMap.IsReducing`; complementary-projection domain preservation follows
from `sub_starProjection_mem_domain`. Maintained Riccati, spectrum,
unitary-transport, spectral-measure, and paper-facing consumers now use the
canonical record directly, with no forwarding alias. The unused linear-map-valued
`spectralProjection` and its range theorem have been removed in favor of the
accepted `Module.End.pointSpectralSubspace` and its `starProjection`; the separate
linear-map projection helpers remain local because they are used throughout finite
spectral and angle geometry. The core donor and all 25 changed maintained
modules, including the paper-facing finite wrappers, YWS consumers, and
`RoadmapBridge.Integration`, compiled at the pinned dependency revision.
The invariant-predicate retirement and its nine touched Lean modules also
compile at that same pin, including `LinearPMap.Closed`, `UnitaryTransport`,
spectral measure construction, complex spectral descent, unbounded reflection,
both unbounded Riccati interfaces, the reducing-spectrum union theorem, and
natural sine-theta examples. The standalone source UIN conformance module and
the complete `ForTauCeti` and `DavisKahan.All` targets compile at the same pin.
The touched `Challenge.DavisKahan1970.Conformance` and `.Leaderboard`
targets also compile, and comparator preflight passes the migrated point-spectrum
rows. One pre-existing `sinTheta_wholeSpace_symmetricNorming` signature mismatch
remains; the aggregate `Challenge` target also has an unrelated missing
`TauCeti.abs_eigenvalues_sub_le_opNorm` reference in its Mathlib-candidate
leaderboard.

**Canonical Hermitian-dilation follow-up (2026-10-21):**
`YuWangSamworth2015.Core.SingularSubspace` now consumes the accepted
`LinearMap.hermitianDilation` and its symmetry theorem from
`TauCeti.Analysis.InnerProductSpace.HermitianDilation.Basic`, replacing the
local product-coordinate dilation, Gram block diagonalization, and their
coordinate, symmetry, and squaring proofs. The source-facing YWS dilation
corollary keeps its spectral-gap hypotheses and angle conclusion, while its
right-hand side is expressed directly as the rectangular perturbation norm via
`LinearMap.norm_toContinuousLinearMap_hermitianDilation_sub` from `.Norm`.
The dilation itself and its square identity are accepted in
[#18946](https://github.com/TauCetiProject/TauCeti/pull/18946) as
`LinearMap.hermitianDilation` and `LinearMap.hermitianDilation_comp_self`;
the exact perturbation-norm equality comes from
[#19010](https://github.com/TauCetiProject/TauCeti/pull/19010), TauCeti commit
`74d007dcb`. The YWS core, Frobenius-Gram, and Theorem 4 consumers compile at
the pinned TauCeti revision.

**Canonical Gram perturbation follow-up (2026-10-21):**
`ForTauCeti.Analysis.InnerProductSpace.Gram.Operator` no longer duplicates the
finite-dimensional right/left Gram difference identities or their operator-norm
bounds. `YuWangSamworth2015.Rectangular.FrobeniusGram` now applies Tau Ceti's
`ContinuousLinearMap.adjoint_comp_self_sub_adjoint_comp_self`,
`self_comp_adjoint_sub_self_comp_adjoint`, and corresponding norm-bound
theorems directly, converting their continuous-map results to algebraic maps
only for the existing Frobenius arguments. The paper-shaped coefficient
wrappers remain downstream and preserve the YWS constants. The stronger
pointwise `norm_gram_sub_gram_apply_le` foundation remains in
`ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace`; its assumptions and
pointwise conclusion still support the symmetric YWS result. Its finite-
dimensional proof now converts those pointwise assumptions to operator norms
and applies Tau Ceti's accepted
`ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le` instead
of reproving the Gram estimate by splitting the perturbation into two terms.
The Gram donor, Frobenius, Theorem 4, and rank-one modules compile at TauCeti
`7205a079ee99f6962eb39fadd8067517ae38bf73`.

**Rectangular adjoint-duality follow-up (2026-10-22):**
`YuWangSamworth2015.Rectangular.FrobeniusGram` derives the left Gram
Frobenius bound from the right Gram bound applied to the adjoint, together
with `rectangularFrobenius_adjoint`. This retires a second independent
cross-dimensional Gram expansion and ideal-law proof. The operator-norm
Gram coefficient results continue to consume TauCeti's accepted right and
left Gram perturbation bounds directly. In `Rectangular.RankOne`, a common
private real inequality replaces four repeated coefficient transports.
The fixed-eigenbasis and arbitrary-frame singular-vector interfaces remain
distinct; no theorem, hypothesis, or inequality coefficient changes.
This is local proof consolidation using established upstream Gram bounds,
not a claim that a new Frobenius theorem was accepted upstream.

**Rectangular Frobenius ideal-law retirement (2026-10-22):**
At the existing TauCeti dependency pin `773bcb657352235c6348ff45be9b7f19f147c19e`,
`TauCeti.UnitarilyInvariantSeminorm.schatten_comp_le_left`,
`schatten_comp_comp_le`, `schatten_two`, and `schatten_apply_adjoint` directly
subsume the finite-dimensional, cross-dimensional left and two-sided Frobenius
ideal laws and adjoint invariance formerly proved in
`YuWangSamworth2015.Rectangular.FrobeniusGram`. The public local wrappers
`frobenius_comp_rectangular_le_opNorm_mul`,
`rectangularFrobenius_twoSided_comp_le`, and `rectangularFrobenius_adjoint`,
and the private finite-approximation-energy proof have been retired.
The Gram proof and Appendix Lemma A1 now consume the accepted results directly;
the row recovery direction uses the unchanged column contraction theorem on
adjoints. No paper-level theorem/hypothesis, ideal constant, or TauCeti pin is
changed. The independent paper-specific Hilbert--Schmidt ideal framework and
its more general consumers remain.

**Adjoint norm-bound retirement (2026-10-22):**
`ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace` no longer defines a
second pointwise adjoint norm estimate.
`ForTauCeti.Analysis.InnerProductSpace.AlignedBasis` now calls the accepted
`LinearMap.norm_adjoint_apply_le` from
`TauCeti.Analysis.InnerProductSpace.Adjoint`; the other maintained consumer,
rectangular UIN majorization, already called this upstream declaration directly.
The upstream result has the same finite-dimensional hypotheses and pointwise
bound as the deleted donor theorem. This is downstream consumption of an
accepted API, not a new claim about proof provenance: the deleted local proof
was authored by Claude, and no DKPS ancestry is inferred for the Tau Ceti
declaration. The change is verified against the pinned TauCeti tree
`dded4e1133eb74742ae658ebd8de8d66f8d2b470`.

**Invariant restriction-coercion retirement (2026-10-22):**
`ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace` no longer exports
`coe_restrict_apply_of_isInvariant` as a simp bridge. Its `IsInvariant` predicate
is exposed and reducible, so `LinearMap.coe_restrict_apply` from Mathlib's
`Mathlib.Algebra.Module.Submodule.LinearMap` applies directly to
`A.restrict hU`. The predicate and all restriction hypotheses retain the same
proposition; only the redundant lemma is removed. `DavisKahan.All`, every direct
importer of the donor module, YWS singular-subspace consumers, and
`RoadmapBridge.Integration` compile with the bridge deleted, at Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`.

**Retirement acceptance criterion:** for each replaced local theorem, record
(1) exact upstream declaration and accepted commit; (2) original statement
and hypothesis comparison, including rank, scalar field, spectra/gap
orientation, domains and constants; (3) actual consumer rewrites and deleted
proof LOC; and (4) successful local Lean build. Merely adding a forwarding
bridge or an upstream import **does not** count as donor retirement.

**Latest accepted-main retirement batch (2026-10-22):** DKPS
`0ab9c7cafac4` is migrated to supplied TauCeti main
`f99e274230de08a9a8189a97dbfc910536646449`. The Haagerup--Zsido
exterior Fourier identity, kernel measurability/integrability, and sharp
`pi/2` mass are now consumed directly through upstream
`TauCeti.Analysis.Fourier.HaagerupZsido.{Fourier,Mass}`. This retires
eight maintained DKPS kernel/support modules; only two downstream
source-facing integral proofs change, and both preserve their statements
and normalization. Independently useful generic integral helpers in the
retired support chain are **no longer maintained**, but their retirement
does not prove verbatim upstream ancestry. The local
`ContinuousLinearMap.realAlgebra` / `.realIsScalarTower` definitions also
retire in favor of upstream `TauCeti.Analysis.Normed.Operator.RealAlgebra`,
with consumers preserving opt-in local instances. All nine removed donor
paths had Kitware source headers; this census and Git history preserve
their provenance. The pin and Lake manifest now agree; compilation remains
the maintainer's next gate.

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

**Canonical finite-dimensional Sylvester API follow-up (2026-10-22):** the
local `ForTauCeti` `LinearMap`-valued `sylvesterOperator`, its positive-gap
injectivity proof, and the total `solveSylvester` wrapper have been removed.
Pinned Tau Ceti `dded4e1133eb74742ae658ebd8de8d66f8d2b470` provides the
canonical `ContinuousLinearMap.sylvester`, `sylvester_injective`,
`sylvester_sum_eigenvectorBasis`, `sylvester_bijective`, and
`sylvester_apply_eq_iff` APIs. These upstream results use disjoint point spectra
and a continuous-linear-map carrier, so they subsume the local positive-gap
finite-dimensional solver. Repository search found no maintained consumer of
the removed local declarations. The local ordered and interval/exterior gap
predicates remain: they are consumed by source-facing finite-dimensional and
unbounded Sylvester estimates and are not replaced by the upstream equation API.
The parallel bounded `ContinuousLinearMap.sylvesterOperator` and
`sylvesterOperatorL` definitions, their linearity/coercivity wrappers, and the
donor module `ForTauCeti.Analysis.InnerProductSpace.Sylvester.Operator` have
also been removed. Bounded sine-theta, infinite-dimensional Sylvester, and
Rosenblum consumers now state their equations through Tau Ceti's canonical
`ContinuousLinearMap.sylvester`; the two operator-norm sine estimates use its
accepted quadratic-form bound directly. The local operator-norm specialization
`opNorm_le_div_of_comp_sub_comp_eq` was deleted after its consumers moved.
The remaining local Sylvester bounds in `Bound.lean` support unitarily invariant
gauges and other estimates not supplied by the accepted operator-norm theorem.
The `ForTauCeti` and `DavisKahan.All` targets compile after the retirement.

**Accepted modulus and Gram-factor consumption (2026-10-24):** the exact
principal-angle formula for the new smoothed transport problem required loading
the accepted `Projection/AngleOperator.lean` alongside the canonical nonacute
rotation. This exposed duplicate declarations in the local operator-modulus
and Gram-contraction donors. The accepted inputs were inspected at pinned Tau
Ceti `f99e274230de08a9a8189a97dbfc910536646449`; the local pre-migration sources
are preserved at DKPS `fd801aceb`.

| Local mathematics retired or retained | Accepted replacement and actual scope | Provenance disposition |
| --- | --- | --- |
| `ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`: the rectangular modulus construction and its defining, positivity, norm, kernel, and single-operator commutation laws | `TauCeti/Analysis/InnerProductSpace/Modulus.lean`: `ContinuousLinearMap.modulus`, `modulus_comp_modulus`, `eq_modulus_iff`, `isSelfAdjoint_modulus`, `ker_modulus`, and `commute_modulus_of_commute`; real/complex Hilbert spaces of unrestricted dimension | Same mathematical API on the same carrier; local construction and forwarding aliases removed. The old donor headers credit Jon Crall, Claude Fable 5, and OpenAI GPT-5.6 Thinking and identify their DKPS ancestry. This consumption records accepted overlap, not an independently verified claim that the upstream proofs descend from those donors. |
| `ForTauCeti/Analysis/InnerProductSpace/Polar/GramContraction.lean`: equality-based construction, extension, norm, and two-sided factorization laws | `TauCeti/Analysis/InnerProductSpace/Gram/Factor.lean`: the stronger rectangular `factorThru` construction and `exists_contraction_of_gram_eq`, which needs equality of Gram operators and no supplied self-adjoint square root | Local equality construction retired. Its Jon Crall / Claude Opus 5 provenance remains in Git history; no upstream proof-adaptation claim is inferred from the shared theorem name. |
| Two-operator commutation of rectangular moduli | Retained in `ForTauCeti/Analysis/InnerProductSpace/ModulusCommutation.lean`, using the accepted single-operator commutation theorem twice | Genuinely missing consequence; no parallel modulus definition or compatibility aliases. |
| One-sided factorization under Gram domination | Retained and generalized to rectangular `A : E →L[𝕜] G` in `ForTauCeti/Analysis/InnerProductSpace/Gram/Domination.lean`, consuming accepted `factorThru` | The previous square-root-specific consequence is replaced by its natural Gram-inequality form. The accepted construction supplies the factor; the local donor proves the norm-domination implication. Classical mathematics, with no independent novelty claim. |

The maintained historical namespace map is updated to the accepted declaration
names. Source-facing theorem names and the 29-result completion denominator are
unchanged; their proofs consume the accepted foundations directly.
The `ForTauCeti` and `DavisKahan.All` builds passed after this retirement.


### October 25: canonical Hilbert–Schmidt energy and block splitting

At accepted pin `efded067c28ffca3483fd731674eb13b42543fbb`, the installed
`HilbertSchmidt/Basic.lean`, `Isometry.lean`, and `Pythagoras.lean` subsume the
corresponding local energy construction and splitting/invariance proofs.
The pre-retirement donor source is preserved at DKPS `a3a2bd771`.
This is verified accepted overlap; those upstream modules do not establish
proof descent from the local Jon Crall / Claude Opus 5 implementation, so no
new adaptation or PR-origin claim is made here.

| Retired local mathematics | Accepted owner and scope | Consumer disposition |
| --- | --- | --- |
| `ContinuousLinearMap.hilbertSchmidtEnergy`, its defining equation, zero/scalar laws, matrix expansion, adjoint and basis independence | `TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic`; real/complex spaces, arbitrary basis indices, including infinite energy | Consumers use the accepted definition and its public equation. The adjoint identity has the opposite orientation, handled explicitly. |
| `hilbertSchmidtEnergy_comp_left_le`, `hilbertSchmidtEnergy_comp_right_le`, and `enorm_adjoint` | `ContinuousLinearMap.hilbertSchmidtEnergy_comp_le_left`, `.hilbertSchmidtEnergy_comp_le_right`, and Mathlib's isometric-adjoint `enorm_map` | The right-ideal scalar factors are reordered explicitly in the block proof; no old-name aliases remain. |
| `TauCeti.HilbertSchmidt.hilbertSchmidtEnergy_isometry_comp` and `.hilbertSchmidtEnergy_comp_isometry` | `ContinuousLinearMap.hilbertSchmidtEnergy_isometry_comp`, `.hilbertSchmidtEnergy_comp_coisometry`, and the two-sided theorem in `HilbertSchmidt.Isometry` | The column-model conjugation and Sylvester flow apply accepted results directly. |
| All three theorems in local `HilbertSchmidt.Pythagoras` | `ContinuousLinearMap.tsum_hilbertSchmidtEnergy_comp_left`, `.tsum_hilbertSchmidtEnergy_comp_right`, `.tsum_tsum_hilbertSchmidtEnergy_comp` | The donor module is deleted. The block decomposition consumes the stronger rectangular theorem directly, without the unnecessary target basis parameter. |
| Local real `hilbertSchmidtNorm` definition and its nonnegativity, zero, scalar, adjoint, triangle, ideal, and operator-domination proofs | Canonical `ContinuousLinearMap.hilbertSchmidtNorm` and its energy-based API in `HilbertSchmidt.Basic` | Source-facing norm statements retain their meaning. The paper square-root-of-approximation-energy identity follows directly from the native basis formula. |

The donor retains the extended-valued ideal gauge and its genuinely remaining
ideal/column-space results, along with three additional energy consequences.
The local extended-gauge presentation is still distinct from the accepted family
gauge. The same-day constructor/completeness retirement is recorded below. The real-norm/extended-gauge identity now
uses the accepted complete-target formula; the source-facing theorems already
work between complete Hilbert spaces.


**Same-day family follow-up:** the exact comparison also identifies
`TauCeti.SymmetricOperatorIdealFamily.hilbertSchmidt` and its underlying
`OperatorIdealFamily.hilbertSchmidt` as the canonical constructors on the same
rectangular/diagonal carriers. The local `TauCeti.hilbertSchmidtIdealFamily`,
its completeness proof, and unused carrier/gauge wrapper lemmas are removed,
with no alias. `SymmetricNormIdeal.hilbertSchmidt` consumes the accepted family
and its completeness instance directly. The source-facing finite-gauge norm
identity is proved using `OperatorIdealFamily.gauge_hilbertSchmidt`; its theorem
name is retained for the paper. The real and complex paper triangle inequalities
also apply the accepted energy-based triangle theorem directly, replacing the
local tensor/complexification detours. The extended-valued gauge and membership
presentation still have downstream consumers and remain the next retirement
cluster. This is accepted-API consumption, not an upstream proof-origin claim.

The family follow-up passed the full default build (21,051 jobs) with warnings
treated as errors, after `lake exe cache get`.
The committed follow-up `e1b3f88d9` also passed explicit `Challenge` and
`DavisKahan.Audits.All` builds (20,831 jobs), after the cache fetch.


### October 25: retire the remaining Hilbert–Schmidt representation

The next consumption pass removes `ContinuousLinearMap.hilbertSchmidtENorm`,
`ContinuousLinearMap.IsHilbertSchmidt`, their closure and gauge laws, and
`TauCeti.chosenHilbertBasisSet` / `.chosenHilbertBasis`. Their pre-retirement
source is preserved at DKPS `51454da84`. No compatibility definitions or aliases
replace them. Extended norm expressions use the accepted rectangular
`OperatorIdealFamily.hilbertSchmidt` gauge directly; finiteness proofs use the
accepted Hilbert–Schmidt energy. The complex column model owns its fixed basis
locally through Mathlib's existing `exists_hilbertBasis`.

The paper-facing full-displacement optimality and vacuity theorems retain their
hypotheses and infinite-energy cases. Their extended-norm expressions now name
the accepted gauge, including both real and complex scalar branches. The source
energy/gauge comparison and finite-norm reading are proved from the accepted
`gauge_hilbertSchmidt` formula. The corresponding supporting declaration names
are `approximationNumberEnergy_eq_hilbertSchmidtGauge_sq` and
`hilbertSchmidtGauge_eq_ofReal_hilbertSchmidtNorm`; no old-name wrappers remain.

Three genuinely remaining consequences stay in the donor: pointwise-on-a-basis
Fatou for the canonical energy (`hilbertSchmidtEnergy_le_liminf`, now without
completeness hypotheses), negation of the real norm, and the real-norm contraction
estimate with native finite-energy hypotheses. The duplicated norm reading,
chosen-basis API and membership predicate are completely removed from maintained
Lean sources. This records accepted overlap, not an independently established
upstream proof-adaptation claim.

The representation retirement passed the full default build (21,051 jobs),
with warnings treated as errors, after the cache fetch.


**Reconciliation follow-up:** the complete donor
`ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison` is removed.
The two live consumers, the Schatten-2 endpoint and principal-sine energy identity,
apply accepted `ContinuousLinearMap.tsum_singularValue_sq_eq_hilbertSchmidtEnergy`
directly, converting the already-stated real approximation numbers termwise.
The paper-owned `approximationNumberEnergy_eq_basisEnergy` likewise uses that
accepted unrestricted-dimensional identity; its statement is unchanged.

The removed one-sided bounds are subsumed by accepted
`hilbertSchmidtEnergy_le_tsum_singularValue_sq` (no completeness) and
`tsum_singularValue_sq_le_hilbertSchmidtEnergy` (complete source).
The removed compactness endpoint is available as
`ContinuousLinearMap.isCompactOperator_of_hilbertSchmidtEnergy_ne_top` in accepted
`HilbertSchmidt.Columns`, whose module was explicitly compiled. Obsolete finite-basis
truncation/compression helpers had no remaining consumers outside the deleted
module; their retirement does not claim that each helper was independently ported.
Original Kitware/Jon Crall/Claude Opus 5 authorship remains in Git history at
`57447d82a`. Accepted overlap is verified at the unchanged Tau Ceti pin; proof
descent is not inferred from matching statements.

Ideal consumers now import the accepted family directly. The remaining donor
contraction-norm theorem is imported explicitly by its actual Theorem 6.2 consumer,
rather than exposing the obsolete representation transitively.

The reconciliation retirement passed the full default build (21,049 jobs),
with warnings treated as errors, after `lake exe cache get`.
The committed checkpoint `1f2946e00` also passed explicit `Challenge` and
`DavisKahan.Audits.All` builds (20,829 jobs), after the cache fetch.
The full signature preflight matched all 42 implemented comparator targets;
the three deliberately declared missing solutions remain skipped.


### October 25: consume the canonical Hilbert–Schmidt column operator

At unchanged accepted pin `efded067c28ffca3483fd731674eb13b42543fbb`,
`TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Columns` supplies
`HilbertBasis.columnOperator : ℓ²(ι, F) →L[𝕜] E →L[𝕜] F`. Its carrier is the
same Mathlib `lp` used by the donor, and its defining inner-product series agrees
with the old basis-coordinate series through `HilbertBasis.repr_apply_apply`.
The pre-retirement donor is preserved at DKPS `ac1aa9379`.

The three donor modules `HilbertSchmidt.Lp`, `.Space`, and `.Conjugation` are
removed, together with `ofLp`, `columns`, their reconstruction, membership,
injectivity, linearity and norm proofs, and the `ofOperator` wrapper in
`Sylvester.Group`. No compatibility definitions or forwarding aliases replace them.
Consumers use `columnOperator_mk`, `columnOperator_injective`, the native energy
and norm identities, and the bundled map's `map_add` / `map_sub` / `map_smul`.
The local pointwise-convergence wrapper is also removed: continuity of the native
bundled operator and continuous evaluation supply the generator proof directly.

Both the Sylvester flow and the block action are now constructed directly as
Mathlib `lp` column families. Their real/complex scope, arbitrary basis index
types, infinite-dimensional setting and unbounded generator-domain conclusions
are retained. The block norm proof uses accepted Hilbert–Schmidt ideal laws;
unitarity of the flow uses accepted isometry/coisometry norm invariance.
The paper-owned fixed-basis model and its theorem names remain in the source
layer, with their represented operators stated as the canonical `columnOperator`.

Remaining analytic estimates for strong continuity, block reassembly, and the
unbounded Sylvester generator have no corresponding declaration in the installed
accepted tree under the inspected APIs and remain donor mathematics. This is
verified accepted overlap, not an independently audited claim that the upstream
column proofs were adapted from these Jon Crall / Claude Opus 5 donors. The older
Spectra tensor presentation was already replaced independently by the Mathlib
`lp` model; its attribution remains in Git history and the existing provenance.

The column-model retirement passed the full default build (21,045 jobs), with
warnings treated as errors, after `lake exe cache get`.
The committed column checkpoint `3d9bea88c` also passed explicit `Challenge`
and `DavisKahan.Audits.All` builds (20,825 jobs), after the cache fetch.


### October 25: detach Gram norm identities from the local Schatten power sum

`nuclearENorm_gramOperator` (complex Hilbert spaces) and its private real source
counterpart retain their arbitrary-dimensional, extended-valued statements without
finiteness hypotheses. They now apply accepted `nuclearENorm_def`,
`OperatorIdealFamily.gauge_hilbertSchmidt`, and
`tsum_singularValue_sq_eq_hilbertSchmidtEnergy` directly, combined with the
remaining donor Gram singular-value identity. No new bridge declaration is added.
The existing real approximation-number view is still used by the unmerged Gram
identity; this does not claim completion of that separate carrier migration.

The unused `schattenENorm_one` and replaced `schattenENorm_two` wrappers are
removed. Accepted `Family.TraceClass` and `Family.HilbertSchmidt` own the normed
endpoints. No maintained production module now imports `Family.Schatten` from
`ForTauCeti`. That donor remains for its stronger exponent scope: homogeneity,
operator-norm and ideal bounds, and lower semicontinuity hold for all `0 < p`,
including `p < 1`, while the accepted normed Schatten family requires `1 ≤ p`.
This retirement records accepted overlap at the unchanged pin, without asserting
historical proof descent. Pre-retirement proofs remain at DKPS `760da90e3`.

The Gram endpoint follow-up passed the focused three-module build (7,544 jobs)
and full default build (21,045 jobs), with warnings treated as errors, after
the respective `lake exe cache get` calls.


### October 25: remove the local operator-norm family

The accepted `SymmetricOperatorIdealFamily.opNorm` has the same arbitrary-Hilbert,
scalar-generic, diagonal-universe scope as local `operatorNormFamily`. Its
`opNorm_toOperatorIdealFamily` equation identifies the underlying family with
accepted `OperatorIdealFamily.opNorm`; the accepted completeness instance then
applies explicitly at the paper constructor and specialization sites. The donor constructor,
completeness specialization, gauge wrapper, and the two paper real-gauge/membership
endpoint wrappers are deleted, with no replacement aliases or bridge definitions.
All consumers now instantiate the accepted symmetric family directly. The paper
core completeness proof uses native `OperatorGauge.Carrier` rather than importing
the retired layer for its transitional `Elem` spelling.

The two unbounded Neumann estimates use Mathlib's `opNorm_comp_le` twice, removing
the otherwise unused local two-sided norm helper. Source theorem conclusions and
ideal scope are unchanged. The legacy historical norm exploration has only its
import redirected; it remains an explicitly unmaintained archive.

Accepted scope was checked in `TauCeti.Analysis.OperatorIdeal.OperatorNorm` at
unchanged pin `efded067c28ffca3483fd731674eb13b42543fbb`; pre-retirement local
source is preserved at DKPS `226aeb096`. This records consumption of accepted
overlap, not a new audit of historical proof descent. Remaining family-carrier
adapters and the genuinely unmerged compact ideal family are separate obligations.

The operator-norm retirement passed the focused build (7,390 jobs) and full
default build (21,043 jobs), with warnings treated as errors, after their
respective cache fetches.


### October 25: retire duplicate compactness and finite-rank approximation proofs

At the unchanged accepted pin, `ApproximationNumber.Compact` provides
`tendsto_singularValue_nhds_zero_iff`,
`isCompactOperator_of_tendsto_singularValue`,
`IsCompactOperator.tendsto_singularValue`, and
`isCompactOperator_iff_tendsto_singularValue`. These cover the donor sequence
criterion, approximable-implies-compact implication, and Hilbert-target converse.
The forward Hilbert-target result still requires no target completeness, and the
accepted arbitrary-domain version permits a seminormed source. The compactness
implication only needs a locally compact field, covering the donor's proper-field
hypothesis. The native sequence formulation uses operator-norm convergence of the
approximants, equivalent to convergence of their norm differences to zero.

The donor `ApproximationNumber.Compact` and `.CompactHilbert` modules are removed.
Their unused quantitative finite-net helper is retired with its proof, without
claiming a separate accepted API for that exact helper. The compact eigenspace
and diagonal consumers apply native convergence results, using the existing real
view only where their unmerged conclusions still mention real approximation
numbers. The remaining compact-adjoint theorem and equivalence use native
singular values exclusively; their real/complex and arbitrary-universe scope
is preserved. No compatibility theorem or alias replaces a retired declaration.

Accepted `Normed.Operator.Compact.FiniteRank` also subsumes both proofs in donor
`Normed.Operator.FiniteRankCompact`. The accepted theorem
`LinearMap.HasFiniteRange.isCompactOperator` permits topological vector-space
targets over locally compact fields, so it covers the donor's normed-space scope.
Both live consumers (the second-primitive snapshots and free-beam affine part)
apply it directly. That donor module is deleted as well.

Pre-retirement source, original Jon Crall / Claude Opus 5 authorship and license
remain at DKPS `a824d8090`; accepted source was checked at Tau Ceti
`efded067c28ffca3483fd731674eb13b42543fbb`. This records accepted mathematical
overlap and direct consumption, without inferring historical proof descent.

The compactness retirement passed the focused five-module build (7,788 jobs)
and full default build (21,037 jobs), with warnings treated as errors, after
the respective cache fetches.


### October 25: consume the accepted isometric-transport adaptation

`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry` explicitly credits
adaptation of this repository's donor `ApproximationNumber/Isometry.lean` under
the Kitware Apache-2.0 license. Its private sandwich inequality and two-sided
inverse-isometry proof follow the donor construction, now using canonical
nonnegative singular values. The accepted theorem
`singularValue_comp_linearIsometryEquiv T e f n` also generalizes the four normed
spaces to seminormed spaces while preserving arbitrary nontrivially normed
fields, independent universes, and absence of completeness assumptions.
This is an explicit adapted-source relationship, beyond merely sharing a topic.

The local `approximationNumber_comp_linearIsometryEquiv` and its private
contraction helpers are removed with their entire donor module. The remaining
diagonal-realization uniqueness proof uses the native theorem directly, through
the existing real approximation-number equation; no replacement alias is added.
The historical norm exploration has its import redirected and remains unmaintained.
The unmerged uniqueness theorem itself is retained.

Pre-retirement source is DKPS `42f55fbe8`; the accepted file and its explicit
provenance were compared at Tau Ceti `efded067c28ffca3483fd731674eb13b42543fbb`.
The accepted header credits Jon Crall and GPT-6; original local Jon Crall
attribution and the Kitware license remain preserved in history and this ledger.

The isometric-transport retirement passed its focused build (6,744 jobs) and
full default build (21,037 jobs), with warnings treated as errors, after the
respective cache fetches.


The three retirement checkpoints (`a824d8090`, `42f55fbe8`, `b82f80b42`) also
passed explicit `Challenge` and `DavisKahan.Audits.All` builds (20,813 jobs),
after `lake exe cache get`. Their combined maintained Lean diff removes a net
557 lines and five donor modules. Paper and visualization files were untouched;
the three original untracked files remain outside the builds and commits.

The broader consumption goal remains open. One precise next comparison is local
`le_approximationNumber_of_lt_rank` in `ApproximationNumber.MinMax` against
accepted `le_singularValue_of_lt_rank` in Tau Ceti's module of the same name.
Both conclude the coercivity lower bound from `(n : Cardinal) < rank V`; the
local input quantifies over subtype vectors, whereas the accepted input uses
`∀ x ∈ V`. The accepted result permits a seminormed target and only a
nontrivially normed field. Migrate its consumers to the native sequence before
removing the real-valued wrapper, and compare the other min–max declarations
individually rather than treating the whole donor as redundant.

The full comparator signature preflight matched all 42 implemented targets
on raw universe signatures and full types. Three explicitly declared missing
solutions remain skipped; no external comparator run or source-completeness
claim is inferred. The auxiliary local-only name parser still has its recorded
imported-declaration limitations; it is not a substitute for these compiler checks.


### October 25: consume the canonical min–max bounds and concrete formulas

At unchanged Tau Ceti pin `efded067c28ffca3483fd731674eb13b42543fbb`, accepted
`ApproximationNumber.MinMax` supplies the coercive-subspace lower bound, its
independent-family and unit-vector variants, the orthogonal-tail upper bound,
and the exact infimum formula. The zero-based rank convention agrees throughout.
The coercive lower bound only needs a normed source over a nontrivially normed
field and a seminormed target; its unit-vector version assumes `RCLike` without
requiring an inner product. The orthogonal-tail formula requires a complete
inner-product source but allows an incomplete seminormed target. These cover the
respective donor hypotheses without adding compactness or finite-dimensionality.

The three local lower-bound wrappers and their proofs are removed. Homogeneous
consumer arguments now apply `le_singularValue_of_linearIndependent` directly;
the tangent residual estimate uses `le_singularValue_of_lt_rank_of_unit_norm`
on its selected span. The compact eigenvalue consumer uses
`singularValue_le_nnnorm_comp_orthogonal` directly. Public source-facing theorem
statements, including trial-space and tangent spectral mapping, are unchanged.
The unused projection-form infimum and its kernel/rank support are retired as an
accepted mathematical overlap; this does not claim that every auxiliary helper
has a separately named upstream counterpart. The source-dimension cutoff is
provided by accepted `singularValue_eq_zero_of_rank_domain_le`.

The duplicate `ApproximationNumber.Examples` module is removed. Accepted
`singularValue_id` and `Submodule.singularValue_starProjection` give the full
cardinal-rank profiles, including infinite rank and zero spaces, without
completeness. Both source block-shift cutoff consumers use accepted
`singularValue_eq_zero_of_rank_le`, converting their finite-rank bound directly.
No forwarding aliases replace the retired examples. The separate diagonal example remains, with its obsolete module-migration
commentary removed; comparison with accepted `FiniteDiagonal` is a follow-up.

The donor `MinMax` module retains only the rectangular projection/restriction
norm identity, its closed-unit-ball formula, and the spectral-band estimate.
Exact accepted equivalents of these three declarations were not identified;
they are preserved rather than deleted merely because other min–max results
are accepted. Their statements and the spectral-band sign hypothesis remain.
The real approximation-number view is still used by unmerged conclusions; its
complete carrier migration is a separate remaining obligation.

Pre-retirement source and original Kitware/Jon Crall/OpenAI GPT-5.6 Thinking and
Claude Opus 5 attribution remain at DKPS `7109db970`. This comparison records
accepted scope and direct consumption without inferring historical proof descent.

The adjusted trial-space and tangent leaves passed the focused build (7,152 jobs).
The full default build (21,037 jobs) then accepted all migrated consumers, with
warnings treated as errors, after the respective cache fetches.


### October 25: retire the finite Eckart–Young and rank-cutoff donors

Accepted `ApproximationNumber.EckartYoung` supplies
`ContinuousLinearMap.singularValue_eq_linearMap_singularValues`, with the same
scalar-generic finite-dimensional source and target scope and independent
universes as the donor identification. The proof and its unused auxiliary
Eckart–Young bounds and corollaries are removed with donor `FiniteDimensional`.
The accepted module also supplies `LinearMap.abs_singularValues_sub_singularValues_le`;
the local CLM perturbation wrapper had no live theorem consumers and is deleted.
The remaining paper, Ky Fan and sandwich consumers use the accepted equation
directly; no forwarding declaration replaces the retired identification.
The unused lower-bound wrapper in `ApproximationNumber.Core` and its downstream
re-export are also removed. The existing real-valued equality used by source
consumers remains an explicitly unfinished representation obligation.

Accepted `ApproximationNumber.Compact` proves
`singularValue_eq_zero_iff_rank_le` over a complete nontrivially normed field,
without requiring a finite-dimensional source or an inner product. It therefore
strictly subsumes the donor `Rank` proof. That module and its unused finrank
wrapper are deleted, and the roadmap examples now state and prove the native
rank characterization and the finite linear-map singular-value cutoff.

The unused donor `DiagonalExample` is also removed. Accepted `ApproximationNumber.FiniteDiagonal` supplies
`ContinuousLinearMap.singularValue_eq_of_pairwise_inner_eq_zero`, which gives the sorted norms of orthogonal basis images.
For `diagOp b x`, the images are `x i • b i`; orthogonality and `x i ≥ 0` give
norms `x i`, so it covers the square donor's antitone nonnegative case.
`Matrix.singularValue_toLin_of_ite_val_eq` and its vanishing-tail theorem go
further, covering rectangular diagonal maps of unequal dimensions. The accepted
module was explicitly compiled. This does not retire the legacy `diagOp` or
finite singular-value accessor: their consumers are a separate carrier migration.
The unmerged `lp` diagonal realization and the unmerged infinite-dimensional
results are retained.

Pre-retirement DKPS source is `6f7249290`, preserving the Kitware Apache-2.0
license and original Jon Crall, OpenAI GPT-5.6 Thinking and Claude Opus 5
attribution. Accepted statements were compared at unchanged Tau Ceti pin
`efded067c28ffca3483fd731674eb13b42543fbb`. This is verified mathematical overlap,
without asserting a newly established historical proof-descent relationship.

The Eckart–Young/rank retirement passed the focused consumer build (7,644 jobs),
including explicit compilation of accepted `FiniteDiagonal`, and the full default
build (21,031 jobs), with warnings treated as errors, after the respective cache
fetches. The full build also validates removal of the unused core re-export.


The min–max and Eckart–Young checkpoints (`6f7249290`, `cac7793ee`) passed explicit
`Challenge` and `DavisKahan.Audits.All` builds (20,807 jobs), after the cache fetch.
Together they remove a net 1,083 Lean lines and four donor modules, without new
compatibility definitions. The remaining converse min–max predicate and global
capability class are not retired by these checkpoints; accepted
`TauCeti.HasMinMaxLowerBound.of_completeSpace` is the next documented comparison.

The full signature preflight matched all 42 implemented comparator targets
on universe signatures and full types. The three explicitly declared missing
solutions remain skipped. No external comparator or source-completeness claim
is inferred; the auxiliary local-only name parser retains its documented
imported-declaration limitations.

### October 25: consume the native converse min–max theorem

Accepted `TauCeti.HasMinMaxLowerBound.of_completeSpace` in
`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax` supplies the strict
threshold witness `0 ≤ r < aₙ(T)`: a coercivity constant `s > r` on the span of
`n + 1` independent vectors. It works uniformly over `RCLike`, with a complete
inner-product source and a possibly incomplete seminormed inner-product target;
source and target universes are independent. The accepted proof uses the
quadratic-form/orthogonal-tail dichotomy, rather than field classification.

The duplicate `MinMaxUpper` and `MinMaxReal` modules are deleted. The separate
local predicate, `HasMinMaxLowerBoundEverywhere` class, scalar-transport proof of
that class, and fixed-field threshold wrappers are removed. Consumers use the
native predicate and its public equation, or the accepted complete-source theorem
directly. Accepted `ContinuousLinearMap.kyFanGauge_add_le` replaces the redundant
field-specific triangle wrappers; no compatibility aliases replace them.

The finite-restriction localization, LUB, and epsilon consequences remain genuine
unmerged donor results, now in `TauCeti.HasMinMaxLowerBound`. Their explicit native
predicate hypothesis preserves their conditional incomplete-source scope. The
Ky Fan argument conditional on approximation by particular finite restrictions
also remains. Real and complex strong-cutoff consequences, projection estimates,
scalar-transport invariance, and broader Schatten results are retained. These are
not claimed to be separately accepted merely because they use accepted input.

Consumers no longer request the obsolete capability class. Unused target
completeness hypotheses are dropped from real complexification equalities,
selected cutoff limits, pointwise norm comparison, and Schatten triangle results.
The strict threshold, witness count, and source theorem norm scope are preserved.
The Challenge audit names the native Ky Fan theorem and the retained generic
finite-restriction LUB at their actual owners.

Pre-retirement source at DKPS `c891a88ec` preserves Kitware Apache-2.0 licensing
and the Jon Crall, GPT-5.6 Thinking, and Claude Opus 5 attribution in the respective
modules. Accepted scope was compared at unchanged Tau Ceti pin
`efded067c28ffca3483fd731674eb13b42543fbb`. This records direct consumption and
mathematical overlap, without inferring historical proof descent. Extraction
metadata records both the retired and retained declaration owners.

The focused consumer build passed (7,166 jobs), after the cache fetch. The full
default build passed (21,027 jobs), with warnings treated as errors, and was
immediately committed as `cb95b5cfa`. Explicit `Challenge` and
`DavisKahan.Audits.All` builds then passed (20,801 jobs), after their cache fetch.
The local-only declaration-name parser still reports imported upstream names as
missing, including the native Ky Fan theorem that the explicit Challenge build
successfully resolves; it is not compiler evidence. Papers and visualizations
are outside this maintenance checkpoint.

The full comparator signature preflight passed for all 42 implemented targets
on universe signatures and full types; the three declared absent solutions
remain skipped. This is signature validation, not an external comparator run
or a claim that the full source paper is complete.

### October 25: retire the duplicate Ky Fan ideal construction

Revalidation at DKPS `4caeeee43` found that
`ApproximationNumbers.ScalarGeneric` still constructed the finite Ky Fan family
and reproved its completeness, despite an older extraction-manifest label
describing that body as retired. The actual duplicate is now removed, together
with the four local gauge/carrier accessors. Historical namespace-map entries
record these declarations as removed rather than forwarding to aliases.

Accepted `TauCeti.OperatorIdealFamily.kyFan` in
`TauCeti.Analysis.OperatorIdeal.Family.KyFan.Basic` supplies the four ideal laws
and finite gauge for every positive `k`, over arbitrary `RCLike` fields and
complete inner-product sources and targets. Its `kyFan_isComplete` instance
supplies completeness, with independent source/target universes. Accepted
`Family.KyFan.Dominance` supplies `isKyFanDominant_kyFan` and the adjoint-invariance
theorem `OperatorIdealFamily.gauge_adjoint` on a single universe.

The source-specific `KyFanDominantIdealFamily.kyFan` now stores that accepted
family directly, obtains completeness by instance search, and obtains its
dominance and adjoint fields from accepted theorems. Tau Ceti's constructor is
an operator-ideal family, not a separately accepted symmetric constructor: the
extra symmetric structure is assembled inside the existing source norm package.
No replacement generic adapter, constructor alias, or forwarding export is added.
The private symmetric-family adapter in `InfiniteDimensional.Ideals.Symmetric`
is also removed; the square-ideal specialization consumes the source package.

Source rank-one normalization and the two-term beam example use the accepted
family through that package. Their mathematical statements and source scope
remain intact. The native gauge is an `ENNReal` coercion of the canonical
`NNReal` Ky Fan sum; the remaining real source views are numeric coercions.
The explicitly noncompiling historical exploration snapshot is preserved as
history, not counted as a current consumer or compiler evidence.

Pre-retirement source and the Jon Crall/GPT-5.6 Thinking attribution remain at
`4caeeee43`; Kitware Apache-2.0 licensing is preserved. Accepted statements were
compared at unchanged Tau Ceti pin `efded067c28ffca3483fd731674eb13b42543fbb`.
This records direct consumption and mathematical overlap, without inferring
historical proof descent from matching statements. The extraction manifest now
describes the actual replacement and corrects its prior retirement overstatement.

The focused build passed (8,096 jobs), including source normalization, square
ideals, and the beam consumer, after the cache fetch. The full default build
then passed (21,029 jobs), with warnings
treated as errors, and was immediately committed as `89ee0d4ae`.

### October 25: remove the transitional ideal carrier API

The former donor `Family.Basic` module is deleted. Consumers use accepted
`OperatorIdealFamily.operatorGauge`, `OperatorGauge.finiteSubmodule`, and
`OperatorGauge.Carrier` directly. The local `carrier` and `Elem` type aliases,
`val` accessors, membership and arithmetic forwarding lemmas, and duplicate
composition and Cauchy-sequence arguments are removed without replacement
compatibility declarations. The unused gauge-subtraction namespace-map entry
records removal rather than pointing to the deleted theorem.

Accepted `Family.Carrier` supplies the family completeness class and its native
carrier instance and the two composition-closure theorems. Accepted `Carrier`
supplies the normed carrier, its map to bounded operators, its norm formula and
its arithmetic rules. The paper real-valued Cauchy-completeness consequence now
constructs and takes limits in that native carrier. The source norm view retains
its numeric finiteness and `toReal` presentation, with the membership equivalence
renamed to `mem_iff_mem_finiteSubmodule` and its source-presentation consumer
migrated in the same change.

The compact-ideal realization and modulus-invariance results are unmerged
mathematics and are preserved. Their membership statements now use the native
finite-gauge submodule. `compactOperatorIdealFamilyCarrierEquiv` is the retained
isometry to Mathlib's compact-operator submodule, now stated over the native
carrier; compact-family completeness still follows from that isometry and
operator-norm closedness. This does not assume that operator-norm completeness
implies completeness for arbitrary ideal gauges.

The genuinely unmerged `OperatorIdealFamily.gauge_blockSum_le` remains with its
original hypotheses and declaration name in donor `Family.BlockSum`. Its only
import is accepted `TauCeti.Analysis.OperatorIdeal.Family`, and its proof now
uses the accepted left/right contraction estimates. No exact accepted block-sum
statement was found in the inspected native sources, so the theorem is neither
deleted nor counted as accepted. The module plan and extraction manifest record
this retained owner separately from the retired carrier facade.

Pre-retirement source is DKPS `89ee0d4ae`, preserving the respective Jon Crall,
OpenAI GPT-6, Claude Opus 5, and GPT-5.6 Sol attribution and Kitware Apache-2.0
licensing. Scope comparisons use unchanged Tau Ceti pin
`efded067c28ffca3483fd731674eb13b42543fbb`; mathematical overlap alone is not
proof of historical descent. No paper or visualization files are changed.

The focused donor/consumer build passed (7,794 jobs), after the cache fetch,
including the source-presentation endpoint. The full default build then passed
(21,029 jobs), with warnings treated as errors,
and was immediately committed as `851b07d82`. Both this and the Ky Fan checkpoint
then passed the explicit `Challenge` and `DavisKahan.Audits.All` build (20,801
jobs), after its cache fetch. Together they remove a net 279 Lean lines while
preserving the unmerged block-sum, compact-family and modulus mathematics.
The local-only declaration-name parser retains its documented imported-name
limitations; the explicit compiler audit resolves the native targets it reports
absent. This is build evidence, not a full-paper completion claim.

The full comparator signature preflight also passed for all 42 implemented
targets on universe signatures and full types; the three declared absent
solutions remain skipped. No external comparator run is inferred.

### October 25: retire the redundant complete-family aggregate

The local `KyFanDominantIdealFamily` record, its stored `isComplete` field and
its coercion to `FanDominantIdealFamily` are removed. There is no replacement
type alias or conversion instance. The existing `operatorNorm`, `kyFan`,
`kyFan_mem` and `kyFan_gauge` declarations now live in the remaining
`FanDominantIdealFamily` namespace; consumers and the namespace map follow
those actual owners. This does not claim that the remaining dominance record
or its real-prefix field is canonical or retired.

The comparison with native completeness exposed an unnecessary restriction in
the analytic interfaces. The interval/exterior Sylvester proof now applies its
complete symmetric-ideal kernel to each positive finite Ky Fan gauge, obtains
that carrier's completeness from accepted
`TauCeti.OperatorIdealFamily.kyFan_isComplete`, and transfers the prefix bounds
by Fan dominance. The ordered branches already supply the required prefix
bounds. Consequently `davisKahan1970_sylvester_of_spectrumGap`,
`davisKahan1970_sylvester_complex`, and the real descent accept an arbitrary
`FanDominantIdealFamily`, without an ideal-completeness hypothesis.

The sine and double-angle consumers are migrated at that weaker scope. Pure
residual, frame, projection-product, reflection and modulus transport lemmas
also drop their unused ideal-completeness hypotheses. The modulus consequence
uses the existing rectangular modulus-invariance theorem directly instead of
constructing a complete square-ideal record. The finite-interval problem
specializations use the stronger all-gap Fan-family theorem. The tangent-two
companion reuses its sine bound and a private scaled inverse-cosine estimate;
this remains the reflected-overlap companion, not a new identification with
the functional-calculus tangent.

The genuine completeness requirements remain on the bounded-inverse and
integral analytic kernels. Their complete symmetric-family scope, including
families without a Fan-dominance hypothesis, is preserved. Ambient Hilbert-space
completeness, self-adjointness, domains, bounded residuals, gap alternatives,
positive constants and quarter-acuteness assumptions are retained wherever
required. No compactness or finite-rank assumption replaces the unrestricted
operator scope: only the number of terms in the testing Ky Fan gauge is finite.

Accepted `OperatorIdealFamily.IsComplete` is a property of native gauge carriers;
it is not a separately accepted copy of the retired aggregate. The native Ky Fan
completeness theorem covers complete `RCLike` inner-product sources and targets
with independent universes. The source bundle's existing diagonal-universe
scope is retained. Pre-retirement DKPS source is `8d72b6c98`, preserving its
respective authorship and Kitware Apache-2.0 licensing. The accepted comparison
uses unchanged Tau Ceti pin `efded067c28ffca3483fd731674eb13b42543fbb`; direct
consumption does not establish historical proof descent or historical novelty.

The current norm-class readings, Theorem 6.3 clause mapping and Section 2 variant
metadata are updated by hand. The weaker normalized where-defined norm record
is preserved: unconditional Fan dominance is not inferred from its partial
comparison law. Historical review notes remain historical; the 29-result
denominator and ledger-selected source aliases are unchanged.

Focused builds passed for the Sylvester/normalization core (7,076 jobs) and the
generalized sine/double-angle consumers (7,082 jobs), after their cache fetches.
The full default build then passed (21,029 jobs), with warnings treated as errors,
and was immediately committed as `6aee36cb3`. Explicit `Challenge` and
`DavisKahan.Audits.All` builds passed (20,801 jobs), after the cache fetch.
Papers and visualizations are untouched.

The full signature preflight matched all 42 implemented comparator targets on
universe signatures and full types; the three declared absent solutions remain
skipped. Two stale namespace-map destinations for the previously retired real
Ky Fan triangle wrappers are marked removed. The auxiliary local-only name
parser still has its imported-declaration limitations and other historical map
findings; no broad static-gate pass or external comparator run is claimed.

### October 25: native Fan dominance and spectral gauge equality

The duplicate unconditional real-prefix property
`NormalizedSymmetricOperatorIdealFamily.HasFanDominance` is deleted.
`withFanDominance` takes accepted `OperatorIdealFamily.IsKyFanDominant`
directly. The remaining `FanDominantIdealFamily` record stores that native
property instead of a second comparison law; its operator-norm and finite
Ky Fan constructors use the accepted instances. The record, real-valued views
and constructors still require a subsequent carrier migration; they are not
claimed retired here.

The source-facing `SameApproximationSingularValues.mem_and_gauge_eq` consumes
accepted `OperatorIdealFamily.gauge_eq_of_sameSingularValues`, replacing its
two local majorization proofs. Membership follows from equality of the native
extended gauges. The existing approximation-number relation is converted in
that proof; no public conversion API is added. Rank-one normalization and the
weaker where-defined comparison law remain unchanged, and no ideal-completeness
hypothesis is added.

This records direct consumption at unchanged accepted Tau Ceti revision
`efded067c28ffca3483fd731674eb13b42543fbb`, not a claim of proof ancestry or
historical novelty. Pre-change local source is DKPS `21ecd9818`; its authorship
and licenses remain in place. The focused normalization/singular-value
transport build passed (6,776 jobs), following the cache fetch. Papers,
visualizations and the three original untracked files are untouched.

The full default build passed (21,029 jobs), with warnings treated as errors,
and was immediately committed as `be6357a2e`. Explicit `Challenge` and
`DavisKahan.Audits.All` compilation passed (20,801 jobs), following the cache
fetch. The signature preflight matched all 42 implemented comparator targets
on universe signatures and full types; three declared absent solutions were
skipped. The auxiliary local-only declaration-name parser still reports its
23 existing findings, including accepted imported declarations it does not
index; no broad static-gate or external comparator pass is claimed.

### October 25: retire the Fan-dominant carrier and factories

The remaining `FanDominantIdealFamily` record is deleted. Its `Mem` and real
`gauge` aliases, conversion views, operator-norm/Ky Fan factories and the unused
modulus forwarding theorem are removed with it. Generic consumers now take
accepted `SymmetricOperatorIdealFamily` and the native
`OperatorIdealFamily.IsKyFanDominant` property directly; estimates use the
existing `gaugeReal` view. No replacement record, type alias, exported
constructor adapter or old-name forwarding theorem is introduced.

The source-specific `NormalizedUnitaryInvariantNorm` stores that native family
and property directly, with its rank-one normalization unchanged. The separate
where-defined normalized norm record retains its weaker comparison law. Native
`OperatorIdealFamily.kyFan`, its dominance/completeness instances and its
adjoint-invariance theorem supply the finite testing families inside the actual
source proofs. The ordinary operator-norm specialization uses accepted
`SymmetricOperatorIdealFamily.opNorm`.

The two-part real-valued membership/comparison consequence is consolidated in
the existing source theorem
`mem_and_gauge_le_of_all_kyFanApproximationGauge_le`, now allowing independent
operator pairs. Source-facing Sylvester, sine and double-angle statements keep
their full Hilbert-space, domain, spectral-gap and residual hypotheses. Ideal
completeness remains only where the analytic kernel requires it; complete
symmetric-family kernels without Fan dominance remain intact.

Pre-change local source is DKPS `a54c126cd`, with existing authorship and
licenses preserved. The accepted Tau Ceti pin is unchanged at
`efded067c28ffca3483fd731674eb13b42543fbb`. This is direct API consumption;
matching statements alone do not establish historical proof descent. The
extraction manifest, namespace map and current source norm-class readings
follow the actual declarations. Papers, visualizations, historical exploration
snapshots and the three original untracked files are untouched.

The focused native carrier/normalization build passed (6,764 jobs), following
the cache fetch. The full default build passed (21,029 jobs), with warnings
treated as errors, and was immediately committed as `1be42ccc1`. Explicit
`Challenge` and `DavisKahan.Audits.All` builds passed (20,801 jobs), following
their cache fetch. All 42 implemented comparator targets matched on universe
signatures and full types; three declared absent solutions were skipped.
The auxiliary local-only name parser reports 23 findings, including imported
native declarations it does not index and historical map destinations. No
broad static-gate or external comparator pass is claimed.

A subsequent `git ls-remote --symref` query observed accepted Tau Ceti `main`
at `97bf123075b7f142c1e37b827b6b37c156803248`. This checkpoint retains the
validated `efded067` pin. The next dependency task is to inspect that accepted
revision, align its exact Mathlib/toolchain inputs, repin and retire any further
overlap it supplies. The local approximation-number equality relation and
real-valued facade remain separate migration obligations; this checkpoint does
not claim the whole consumption campaign complete.

### October 25: accepted dependency refresh to `97bf1230`

The accepted Tau Ceti pin is refreshed from `efded067` to
`97bf123075b7f142c1e37b827b6b37c156803248`. Direct inspection of the accepted
manifest and toolchain confirms the same exact Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055` and Lean `v4.36.0-rc1` already used
here. `lake update TauCeti` changes only that dependency's manifest entry.

Accepted commit `8e692e2c` (#20399) adds diagonal Riesz measures for star
representations, normal-operator specialization and the general quadratic
star-representation identity. The declaration/type comparison reveals overlap
with the local Borel-calculus diagonal-measure construction. Its retirement is
the next mathematical consumption task, separate from this pin change. No
historical proof-adaptation claim is inferred merely from matching statements;
the local Kitware/Jon Crall/Claude Opus 5 provenance is retained pending that
migration.

### October 25: consume Mathlib's real continuous-function map

The local `TauCeti.BorelCalculus.ofRealLM`, `ofRealLM_apply` and
`star_ofRealLM` declarations are deleted. Their continuous-functional-calculus,
gap-form, restriction and conjugation consumers use accepted Mathlib
`ContinuousMap.realToRCLikeStarAlgHom`, its pointwise formulas and
`isSelfAdjoint_realToRCLike` directly. No alias or old-name forwarding interface
is retained. The restriction-specific composition lemma is renamed
`realToRCLike_comp_specInclCM` to describe its actual carrier.

The diagonal-positivity proof now applies accepted `map_nonneg` and
`ContinuousLinearMap.nonneg_iff_isPositive`, replacing its separate square-root
factorization argument. Its normality, completeness and pointwise nonnegativity
hypotheses are retained. The local diagonal measure and real-functional
construction still exist at this preparatory checkpoint; consuming the newly
accepted `StarAlgHom.representationDiagMeasure` remains a separate migration.

The focused diagonal-measure module compiled (6,295 jobs), following the cache
fetch. Pre-change source is DKPS `32799562e`, with original Kitware/Jon Crall/
Claude Opus 5 provenance retained. The older Mathlib real-function API is
consumed as accepted independent infrastructure; historical proof descent is
not inferred. The extraction manifest records precisely the three retired
declarations and preserves the remaining donor obligations.

The new positivity proof's ordered-operator dependencies are private imports;
the accepted real-function API is public because it occurs in the mathematical
interface. Native symbol evaluation is normalized explicitly to complex casts
in the gap-form identities. The focused central-band and accepted diagonal
measure build passed (7,478 jobs), following the cache fetch, including native
`StarAlgHom`, representation measures and normal-operator diagonal measures.

The full default build passed (21,029 jobs), with warnings treated as errors,
and was immediately committed as `5f82f288d`. Explicit `Challenge` and
`DavisKahan.Audits.All` compilation passed (20,801 jobs), following the cache
fetch. All 42 implemented comparator targets matched on universe signatures
and full types; three declared absent solutions were skipped. The auxiliary
local-only declaration-name parser reports 23 findings, including native
imports it does not index and historical map destinations; no broad static-gate
or external comparator pass is claimed. The source normality/complex-symbol
scope, papers, visualizations and original untracked files are preserved.

### October 25: retire the diagonal Riesz construction

The entire donor module
`ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure` is deleted.
It no longer defines a positive real functional, diagonal measure, finiteness
or regularity instances, integral identities, mass formula or real-symbol CFC
helper API. Borel-calculus, cyclic, multiplicity, real-spectrum and unbounded
spectral-measure consumers now use accepted
`StarAlgHom.representationDiagMeasure (cfcHom ha)` directly. There is no local
measure alias, constructor wrapper or old-name forwarding layer.

Native finite/regular instances, the continuous scalar integral identity,
measure characterization and mass theorem supply the replaced foundation.
Real scalar integral identities are extracted inside the relevant proofs by
taking `Complex.re`. The three real conjugation-invariance arguments compare
continuous scalar integrals instead of exposing a local functional record.
The restriction theorem uses native uniqueness on complex continuous symbols;
its now-unneeded real-symbol composition helper is deleted. The duplicate
finite-sum measure theorem is also removed in favor of Mathlib's instance.

The normal-operator hypotheses, complex symbols, arbitrary Hilbert-space
dimension and real/unbounded consumer scopes are preserved. The remaining
Borel transport, cyclic/multiplicity and unbounded spectral constructions are
unmerged donor mathematics, not claimed accepted by this retirement. The
polarization module and the restriction/naturality core compiled in focused
builds (6,312 and 6,400 jobs), each following its cache fetch.

Accepted Tau Ceti revision is `97bf123075b7f142c1e37b827b6b37c156803248`,
including `8e692e2c` (#20399). Pre-retirement local source is DKPS `9380d70b0`;
original Kitware Apache-2.0/Jon Crall/Claude Opus 5 provenance and the route's
independence from Spectra are preserved in the extraction manifest and Git
history. Matching statements alone do not establish historical proof descent.
The deleted file is removed from live donor clusters and the current file
checklist, preserving every other review mark. Historical semantic-review
snapshots remain historical. Papers and visualizations are untouched.

Validation checkpoint `4f7c6b048` compiled the full default build (21,037
jobs), with warnings treated as errors, after `lake exe cache get`. It was
committed immediately on that success. The separate `Challenge` and
`DavisKahan.Audits.All` build also passed (20,809 jobs), after its cache fetch.
Import-sensitive real Section 8 form bounds now use explicit simplification;
their hypotheses and conclusions are unchanged.

The signature preflight (`check_comparator_signatures.py --no-build`) passed
all 42 compared declarations, with three declared absent and skipped; no
external comparator result is inferred. The tracked mathematical tree is
committed. The original three untracked files remain untouched.

### October 26: consume native equality of singular-value sequences

The relation `ContinuousLinearMap.HasSameApproximationNumbers`, its unfolding
lemma and equivalence proofs are removed. Both source relation aliases
`SameApproximationSingularSequence` and `SameApproximationSingularValues`, and
their duplicated equivalence and prefix-gauge proofs, are also removed.
Maintained consumers take accepted `ContinuousLinearMap.SameSingularValues`
directly; no old relation name or forwarding equivalence is exported.

Accepted `ApproximationNumber.Equivalence` explicitly documents adaptation
from the DKPS donor. Its native nonnegative sequence supports independent
universes and seminormed spaces over arbitrary nontrivially normed fields.
This records explicit proof adaptation at Tau Ceti `97bf1230`, with historical
Kitware/Jon Crall/OpenAI GPT-5.6 Thinking/Claude Opus 5 donor provenance retained.

Additional norm equality and complete-source min--max/pointwise comparisons
remain local on the native carrier. The comparisons permit incomplete targets,
where the accepted factorization route requires complete targets. A semantic
source search also identified accepted `ApproximationNumber.Modulus` results;
the still-local complete-space modulus declarations are the next retirement
obligation, rather than unmerged mathematics. The source norm, Hilbert--Schmidt and subspace transport results retain
their mathematical scope. The existing real-gauge module projects native
equality to scalar approximation-number and gauge equality by coercion; no
old relation or conversion between relation types is maintained. The remaining real approximation-number
and gauge views are a separate migration obligation; this change does not claim
those views retired. Papers, visualizations and original untracked files are
untouched. The native relation/gauge core and focused full-angle, generic
double-angle and selected-branch consumer builds passed (6,712 and 7,646 jobs),
each following its cache fetch. Full default validation will be recorded at
the committed checkpoint.

The native relation checkpoint is `db3ac636f`, committed immediately after the
full default build passed (21,037 jobs; warnings treated as errors).

### October 26: consume accepted modulus invariance

`ContinuousLinearMap.modulus_hasSameApproximationNumbers`, the downstream
`ExactSinTheta` wrapper and its entire `OperatorModulus` forwarding module,
and `Angle.modulus_hasSameApproximationNumbers_rclike` are deleted. Maintained
consumers import accepted `ApproximationNumber.Modulus` and apply
`ContinuousLinearMap.sameSingularValues_modulus` directly over the original
complex or generic `RCLike` field, with arbitrary Hilbert-space dimension and
independent source/target universes. No old-name alias or forwarding theorem
replaces any of these declarations.

The complete-target equisingularity and direct-rotation consumers also use
`sameSingularValues_of_forall_norm_apply_eq` directly. Its stronger source
scope permits removing an unused source-completeness assumption in the
former. The local complete-source comparisons with incomplete targets remain
unchanged; upstream factorization needs complete targets, so they are not
claimed duplicated. The native factorization proof and the former local
min--max proof are distinct routes; historical proof descent is not inferred.

The current file checklist and provenance mappings retire the deleted wrapper.
The historical source-module names remain in provenance. Current-tree and Git-history review confirmed that the separate
`InnerProductSpace.OperatorModulus` donor was already deleted in `f8603c6e6`
when its basic foundations moved to accepted `InnerProductSpace.Modulus`.
Its stale live staging/checklist entries are now retired; historical source
names remain as provenance. Papers and visualizations are untouched.

Validation for `5942b93a5`: the full default build passed (21,037 jobs), and
`Challenge` plus `DavisKahan.Audits.All` passed (20,811 jobs), each following
`lake exe cache get`. All 42 implemented comparator targets matched on universe
signatures and full types; the three declared absent solutions were skipped.
No external comparator result is inferred. After deleting 32 obsolete local
build outputs for the two retired `OperatorModulus` paths, the full default
build passed again (21,037 jobs). Compiler/linter warnings are treated as errors.

The local-only declaration-name parser still reports its 23 imported-native /
historical-map findings; no aliases were added to silence that parser. The
untracked `ProbeModulus.lean` and the workshop export under
`papers/dk_formalization_workshop/ForTauCeti/` still contain legacy imports;
they are outside the maintained Lake build and are preserved under the user's
untracked-file and paper boundary. The three original untracked files remain
unchanged.

Next concrete migration: remove the remaining coordinate-change forwarding
lemmas `SameApproximationSingularValues.comp_isometricEquiv` and
`of_isometricEquiv_comp` from source `Norms/SingularValueTransport.lean` by
using accepted `sameSingularValues_comp_linearIsometryEquiv` in their callers.
The real approximation-number / Ky Fan views also remain a representation
migration obligation. Preserve the genuinely broader incomplete-target
comparison theorems in `ApproximationNumber/SameSequence.lean`; the complete-
target Douglas route is not a scope-preserving replacement for them.

### October 26: retire the coordinate-change forwarding API

The two remaining source coordinate-change wrappers,
`SameApproximationSingularValues.comp_isometricEquiv` and
`of_isometricEquiv_comp`, are deleted. Their callers import accepted
`ApproximationNumber.Isometry` directly and use
`ContinuousLinearMap.sameSingularValues_comp_linearIsometryEquiv`, applying
coordinate identities at the use site. No replacement wrapper or namespace
alias is introduced. Source norm membership and representative packaging stay
in their established paper-facing module.

The real complexification, unbounded residual, scalar-transport, full-angle and
Lemma 6.1 block-coordinate statements retain their mathematical conclusions.
Redundant ambient-completeness assumptions are omitted where the native theorem
permits the stronger statement. Lemma 6.1 makes the isometry coercion explicit
before using its existing coordinate calculation. The historical name map and
isometry extraction record track the exact native replacements and retirements;
the native module explicitly credits the earlier DKPS donor. This is native
consumption, not a new submission or a new historical novelty claim. Papers,
visualizations and the original three untracked files are untouched.

Checkpoint `9b783a9fd` passed the full default build (21,037 jobs, warnings
as errors) and was committed immediately on success.

### October 26: remove the subspace-transport source facade

The `Norms/SubspaceSingularTransport` forwarding module and all three of its
source-name wrappers are deleted. Maintained callers import the genuine
`ForTauCeti` subspace-transport mathematics directly. Its four declarations
now use the canonical `sameSingularValues_*` names; no old-name alias remains.
The donor's unnecessary `SameSequence` dependency is replaced by the smaller
`CanonicalGauge` dependency. Source representative/norm packaging is imported
explicitly where needed. The focused donor, Lemma 6.1, real symmetric and Gram
bridge build passed (7,508 jobs), after its cache fetch.

These generic block transports are unmerged mathematics, not an additional
upstream acceptance claim. The zero-extension theorem retains incomplete
targets, and the other hypotheses and conclusions are preserved. The manifest
now records this donor explicitly, with the prospective target path separated
from acceptance, its current names and its original source provenance. The
retired source module leaves the live checklist; historical source names
remain in provenance. Papers, visualizations and original untracked files
are unchanged.

Checkpoint `8f30839ba` passed the full default build (21,035 jobs, warnings
as errors) and was committed immediately on success.

### October 26: consume projected-subspace completeness directly

The duplicate local proof of
`Submodule.isComplete_coe_of_hasOrthogonalProjection` is deleted from
`InnerProductSpace/ReducingSubspace`. Its consumers now use accepted
`TauCeti.Analysis.InnerProductSpace.Projection.Completeness` under the unchanged
name and hypotheses: every `RCLike` field, complete ambient inner-product
space, and subspace admitting an orthogonal projection. No finite dimension,
nonzero-space condition, or compatibility theorem is added. The focused donor
and subspace-transport build passed (5,008 jobs), after its cache fetch.

The existing opt-in completeness instance remains as local instance packaging;
upstream intentionally offers explicit theorems rather than a global instance.
The local reducing predicate, qualitative API and quantitative orthogonal-block
estimate are preserved. Whole-module retirement is not claimed. Native
`Submodule.IsReducing` is the owner for the next reducing-predicate migration.
The native completeness module acknowledges the DKPS observation; matching
statements alone are not proof-adaptation evidence. Papers and visualizations
are unchanged.

Checkpoint `4ee1a8c10` passed the full default build (21,037 jobs, warnings
as errors) and was committed immediately on success.

### October 26: register the native completeness theorem without an adapter

The local `instCompleteSpaceCoeOfHasOrthogonalProjection` declaration is now
deleted as well. The existing `TauCeti.CompleteSubspace` scope registers
accepted `Submodule.completeSpace_coe_of_hasOrthogonalProjection` itself with
`attribute [scoped instance]`. Existing opt-in consumers retain their scope;
there is no local forwarding instance, alias, or duplicate completeness proof,
and the theorem is not made a global instance. The focused reducing-subspace
and block-transport build passed (5,008 jobs), after its cache fetch.

The local reducing predicate/qualitative API and quantitative orthogonal-block
estimate remain. In particular, native `Submodule.IsReducing` must replace
`ContinuousLinearMap.Reduces` in a separate consumer migration; this cleanup
does not treat the existing local carrier as a final architecture. Papers,
visualizations and original untracked files remain untouched.

Validation for checkpoint `8de5c2569`: full default build passed (21,037 jobs),
with compiler/linter warnings treated as errors. `Challenge` and
`DavisKahan.Audits.All` passed separately (20,811 jobs). Each build followed
`lake exe cache get`. Exact signature preflight passed all 42 compared
declarations on universes and full types; three declared absent solutions
were skipped. No external comparator result is inferred. The native scoped
registration therefore preserves the existing comparator surfaces.

The auxiliary local-only declaration-name parser reports its 23 native-import /
historical-map findings; no aliases were added to silence that parser. Only the
three original untracked files remain outside Git, unchanged. No paper or
visualization changes are included.

The next substantive carrier migration is the bounded reducing predicate:
replace `ContinuousLinearMap.Reduces A U` with accepted
`U.IsReducing (A : Module.End 𝕜 E)` from `InvariantSubspace`, then consume its
invariance and projection-commutation API directly and delete the displaced
qualitative proofs. Preserve the separate quantitative
`LinearMap.norm_starProjection_apply_le_of_mem_orthogonal` statement unless an
accepted theorem covers its actual linear-map / incomplete-ambient scope.
The real approximation-number and Ky Fan views also remain open migration
obligations; no whole-goal completion is claimed by these checkpoints.

### October 26: consume the native bounded reducing carrier

All maintained bounded reducing-subspace statements now use accepted
`Submodule.IsReducing U (A : Module.End 𝕜 E)` from
`TauCeti.Analysis.InnerProductSpace.InvariantSubspace`. The local
`ContinuousLinearMap.Reduces` definition and its symmetric-invariance,
projection-commutation and complement proofs are deleted. Consumers use native
invariant-submodule membership, the projection-commutation equivalence and
`Submodule.isReducing_orthogonal_iff` directly. There is no compatibility
predicate, alias or forwarding theorem. This is an API migration preserving the
real/complex, dimension and completeness scopes of the existing mathematics.

The genuine isometry-conjugation result moves to
`Submodule.IsReducing.map_isometryEquiv`; its proof remains downstream and is
not claimed accepted upstream. The `ReducingSubspace` donor now contains only
the quantitative `LinearMap.norm_starProjection_apply_le_of_mem_orthogonal`
result. The quantitative statement retains arbitrary symmetric linear maps and
incomplete
ambient spaces. A bounded Hilbert-space specialization would not replace that
scope. The source provenance is preserved; native qualitative consumption is
not evidence of historical proof adaptation. Papers, visualizations and the
three original untracked files are unchanged.

Consumers of the accepted projected-subspace completeness result also import
its owning module directly. The residual quantitative donor does not re-export
the native reducing module; qualitative-only importers no longer import the
donor.

The opt-in `TauCeti.CompleteSubspace` registration scope is retired as well.
Consumers register accepted
`Submodule.completeSpace_coe_of_hasOrthogonalProjection` locally with an
instance attribute. No local theorem or instance wrapper replaces it. The
native theorem remains opt-in rather than global, while callers no longer
import the quantitative donor for completeness packaging. Only the two vector
estimate consumers import that donor directly.

Validation for checkpoint `9ed78ed4e`: the full default build passed (21,037
jobs), with compiler and linter warnings treated as errors, and was committed
immediately on success. `Challenge` and `DavisKahan.Audits.All` passed separately
(20,811 jobs); each build followed `lake exe cache get`. Exact signature
preflight passed all 42 compared declarations on universes and full types;
three declared absent solutions were skipped. No external comparator pass is
claimed. The auxiliary local-only name parser retains its 23 native-import /
historical-map findings, with no new findings from this migration.

The bounded reducing carrier migration is now closed. Separate remaining
cleanup includes the real approximation-number and Ky Fan views and the
caller-local projected-subspace completeness instance declarations still
present in some modules. Those can consume the accepted theorem with local
instance attributes too; preserve their actual ambient and scalar hypotheses.
No whole-repository upstream-consumption completion is claimed. The tracked
mathematics is committed; only the three original untracked files remain.

### October 26: consume native directed and sharp projector sine bounds

Delete both `BoundedOperator/SinTheta.lean` and `BoundedOperator/Projector.lean`
from the donor. Their mathematical consumers now invoke accepted
`Submodule.norm_starProjection_comp_starProjection_le_norm_sub_div` and
`Submodule.projectionGap_le_norm_sub_div` from `Projection.SinTheta` directly.
No namespace alias, compatibility module or forwarding theorem remains. The
finite spectral and restricted-spectrum source-facing theorems retain their
statements; only their generic analytic core is supplied upstream.

The native directed theorem is stronger: it requires no ambient completeness,
no symmetry of the source operator, and only invariant subspaces rather than
reducing hypotheses. The native sharp projector theorem permits two different
cuts; the existing common-cut uses specialize them to the same value. A
canonical-consumer example exercises the weaker native hypotheses directly.
The continuity-free `LinearMap` reduced-extension identity remains genuine
donor mathematics, and the other local gap extensions remain where consumed.
The source census's derived projector review target now records the native
bound and its explicit common-cut/projection-norm specialization.

This is consumption of APIs already present at the prior TauCeti pin, not a
claim that the latest main introduced these results. Preserve the native
Spectra-lineage acknowledgement; matching statements do not prove that the
native proof was copied from the DKPS donor. Papers and visualizations are
unchanged.

### October 26: remove redundant subspace-completeness declarations

Replace 23 local forwarding instances in 19 mathematical modules by scoped
registrations of the accepted
`Submodule.completeSpace_coe_of_hasOrthogonalProjection` theorem. Update the
additional tangent consumer that explicitly registered a retired local name.
These are direct native registrations, with no replacement local declaration,
namespace alias or compatibility module. Four stale docstring exemptions are
removed. The native hypotheses are the same: a complete ambient inner-product
space and an orthogonally complemented subspace, over any `RCLike` field.
The registration stays local because global registration would cycle with
Mathlib's converse projection instance. Finite-dimensional ambient-completeness
proofs and proofs with other hypotheses are unchanged.

This continues direct consumption of the accepted completeness API; it does not
introduce new mathematics or assert additional upstream proof ancestry.
The preceding bound migration compiled in the full default build (21,035 jobs)
and was committed immediately as `64e6b3804`.

### October 26: source ownership of the scalar-norm transport module

Move `OperatorIdeal/SymmetricNormingScalarTransport.lean` to
`Sources/DavisKahan1970/SineTheta/Norms/ScalarTransport.lean`, beside the
source-defined `SymmetricNormingFunction` that its theorems concern. Keep every
declaration name, hypothesis and proof unchanged. Update both mathematical
consumers and the source norm aggregate; remove the import from the generic
operator-ideal aggregate. There is no forwarding module at the old path.
This fixes the previously recorded generic-to-source import-policy violation
by assigning the implementation to its mathematical owner, without moving the
paper's norm definition into the generic foundation or weakening the policy.

The preceding native-completeness migration compiled in the full default build
(21,035 jobs) and was committed immediately as `495f03d1a`.

### October 26: validation of the completed consumption checkpoint

TauCeti is pinned to accepted main
`b3de655482f7b86c77d8982566e5a73801fd64fa`, with its exact Mathlib/toolchain
inputs unchanged. The complete default build passed after each migration,
including the final source-module move (`53d8deb9b`, 21,035 jobs), with compiler
warnings treated as errors. `Challenge` and `DavisKahan.Audits.All` then passed
(20,809 jobs). The signature preflight matched full types and raw universe
signatures for all 42 implemented comparator targets; the three explicitly
absent solution targets remain declared skips, not completed obligations.
No full external comparator run is claimed.

The import-layer policy now reports zero violations, closing the previously
recorded generic/source ownership issue. The auxiliary local-source name-drift
scanner still reports the same 23 known findings involving imported APIs and
historical mappings; this checkpoint does not claim that scanner passes. No
aliases were introduced to satisfy it. Papers, visualizations, coordination
checkouts and standalone submission submodules were not modified.


### October 27: consume accepted polar adjoint identities

At the unchanged accepted TauCeti pin
`b3de655482f7b86c77d8982566e5a73801fd64fa`, the donor
`Polar/PartialIsometry.lean` now imports accepted `Polar/Bounded.lean`.
Delete the local `ContinuousLinearMap.modulus_adjoint` proof: its name
collided with the accepted theorem, whose displayed formula differs.
The two internal consumers, `modulus_adjoint_comp_polarPartial` and
`polarPartial_adjoint`, now use accepted `eq_polarFactor`,
`modulus_adjoint_comp_polarFactor` and `polarFactor_adjoint`, with local
proofs identifying the existing donor factor. No replacement public alias
is added. The wider donor-factor migration is not claimed complete.

This is direct consumption of accepted results, not evidence that the
accepted proof was adapted from DKPS. Existing donor/Spectra ancestry is
preserved in the source. A whole maintained-tree search found no external
consumer or census pin of the removed local formula. The name-drift scan
retains the same 23 previously recorded unrelated findings. Full default
and explicit Challenge build evidence is recorded in the research handoff.

## 2026-10-27: consume accepted almost-complex dimension necessity

During the real signed-root parity converse, the pinned accepted Tau Ceti
revision `b3de655482f7b86c77d8982566e5a73801fd64fa` was inspected directly.
`TauCeti/Geometry/Symplectic/Finrank.lean` already declares
`TauCeti.AlmostComplexStructure.even_finrank_real`, without a finite-dimensional
hypothesis. The local same-name finite-dimensional proof in
`ForTauCeti/Analysis/InnerProductSpace/OrthogonalComplexStructure.lean` is
retired; that module now imports and uses the accepted declaration directly.
Its genuine orthogonal existence converse, paired orthonormal construction
and compatible-metric facts remain local. The new real compatible-projection
theorem consumes this existing converse and the accepted dimension necessity.

This records direct consumption and removal of a duplicate, not a submission
or evidence of DKPS proof descent in the accepted theorem. Upstream integration
is verified by the actual pinned source; its PR and original proof ancestry
were not separately audited. The underlying complex-dimension parity fact is
classical. Mathematical attribution and the transport application are recorded
in [the unification note](../spectral-transport-unification.md), rows T1/T8.


## 2026-10-30: consume the accepted real spectral grid (SA-E32--E34)

**Upstream integration:** [TauCeti #18927](https://github.com/TauCetiProject/TauCeti/pull/18927), accepted main commit
[`3bd7882f07072fe6918ca2a50175cbca678f07de`](https://github.com/TauCetiProject/TauCeti/commit/3bd7882f07072fe6918ca2a50175cbca678f07de),
confirmed in the supplied TauCeti tree at
`463ab293070d4cb355d0a0e036469464070088bc`. Its implementation lives in
`TauCeti/Order/Interval/Set/RealGrid.lean` and
`TauCeti/MeasureTheory/Constructions/BorelSpace/Real.lean`, in the `Real`
namespace; the accepted source explicitly identifies the original Kitware DKPS
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralGrid.lean` as adapted
source. This is a source-backed **adaptation**, not an inference from the roadmap
node alone. It changes ownership from the partial-operator namespace to reusable
real interval and measure theory and strengthens the disjointness result to all
widths.

**Historical donor anchor:** DKPS `e4637c3919ae`,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralGrid.lean`
(Kitware, Inc.; Jon Crall and Claude Opus 5; Apache-2.0). The six original
declarations are `TauCeti.LinearPMap.gridCell`, `.measurableSet_gridCell`,
`.pairwise_disjoint_gridCell`, `.iUnion_gridCell`, `.abs_le_of_mem_gridCell`,
and `.abs_sub_le_of_mem_gridCell`. They are now replaced, respectively, by
`Real.gridCell`, `Real.measurableSet_gridCell`, `Real.pairwise_disjoint_gridCell`,
`Real.iUnion_gridCell`, `Real.abs_le_of_mem_gridCell`, and
`Real.abs_sub_le_of_mem_gridCell`. The original proofs and names remain in Git
history and the extraction manifest's historical `source_declarations` field.

**Retirement scope:** Delete the six donor proofs/definition; update
`ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralGrid` and its
`ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap` consumer to import
and apply the accepted `Real` API directly. Retain four unmerged theorem
statements: `tsum_enorm_sq_specProjection_gridCell`,
`tsum_enorm_sq_adjoint_specProjection_gridCell`, `specProjection_comp_self`,
`exists_mem_spectrum_of_specProjection_ne_zero`. No public aliases are added.

**Build boundary:** the dependency-pin checkpoint and the subsequent
consumption change require focused and downstream Lean compilation in the live
checkout; this dated entry documents the proposed migration, not a fabricated
build result. The prior #18927 row in the October 21 historical table records
its then-open status and must not be read as current.


## 2026-10-31: consume accepted symmetric two-orientation Davis--Kahan (SSP-C24)

**Integration:** [TauCeti #19817](https://github.com/TauCetiProject/TauCeti/pull/19817),
accepted main commit [`140f78ce562fc8b1652cc184a409bf38a70cb81f`](https://github.com/TauCetiProject/TauCeti/commit/140f78ce562fc8b1652cc184a409bf38a70cb81f),
present in the supplied TauCeti main tree at `463ab293070d4cb355d0a0e036469464070088bc`.
The accepted source
`TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Symmetric.lean`
explicitly names the original DKPS `sinAngleOperator_perturbation_le` as adapted
source (Kitware / Apache-2.0; Jon Crall and GPT-6 for the accepted adaptation).
It provides the symmetric constant-one theorem for both projector difference
(`UnitarilyInvariantSeminorm.mul_map_sub_starProjection_le_map_sub`) and the
canonical full-space sine angle operator
(`UnitarilyInvariantSeminorm.mul_map_sinAngleOperator_le_map_sub`), with the two
opposite interval/exterior spectral-gap hypotheses. The upstream version uses
bounded operators and `Submodule.sinAngleOperator`, while the DKPS original used
linear maps, `TauCeti.sinAngleOperator`, and an explicit `0 < δ` assumption. The
upstream version also handles `δ ≤ 0`. This is a theorem-level proof adaptation
with broader scalar-gap scope, not merely a common roadmap number.

**Historical source:** DKPS `e4637c3919ae`,
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`; before its
extraction, `DavisKahan/FiniteDimensional/SinTheta/Perturbation.lean` (see the
manifest's historical `source_module` and `source_declarations`). Copyright
2026 Kitware, Inc.; authors Jon Crall and GPT 5.6 High; Apache-2.0. The
original complete proof is recoverable with:
`git show e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`.

**Retired maintenance:** Delete the local public theorem
`TauCeti.sinAngleOperator_perturbation_le`, its two private Ky Fan/compression
proof stages, and five private adjoint/subtype transport helpers used only by
that symmetric proof. No local forwarding theorem or staging alias is retained.
The original Part III source-facing name
`TauCeti.DavisKahan.FiniteDimensional.partIII_sinTheta_angleOperator_uiNorm`
now aliases the **accepted upstream**
`UnitarilyInvariantSeminorm.mul_map_sinAngleOperator_le_map_sub` directly. The
original local theorem and its eight retired local declarations remain indexed
in the extraction manifest's historical provenance; the upstream accepted
module remains responsible for the reusable mathematics.

**Preserved:** The distinct directed/one-sided `sinTheta_perturbation_le`,
`sinTheta_perturbation_le_of_orderedGap`, operator-norm interval gap, Frobenius
spectral-distance theorem, `frobenius_sinTheta_le`, `kyFan_sinTheta_le`, and
other spectral-distance results are not covered by SSP-C24 and remain local.
The planar sharpness theorem remains and its documentation now identifies the
accepted theorem as the target of its constant-one equality. The previous
source name appears in historical documentation only.

**Validation boundary:** This entry records source comparison and a proposed
upstream-consumption change, not a local Lean compilation. With the accepted
TauCeti pin, run `lake exe cache get` before focused builds of
`ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`,
`DavisKahan.Sources.DavisKahan1970.PartIII`,
`DavisKahan.FiniteDimensional.Sharpness`, and finally the default project
build. Commit only after those pass.

## 2026-10-31: retire the parallel finite principal-tangent definition

**Upstream owner:** `Submodule.principalTangents` in
`TauCeti/Analysis/InnerProductSpace/Projection/Acute.lean`, accepted in
[TauCeti #16645](https://github.com/TauCetiProject/TauCeti/pull/16645)
(2026-10-15). The accepted source is present at pinned TauCeti
`463ab293070d4cb355d0a0e036469464070088bc`.

**Retired DKPS declaration:** `TauCeti.principalTangents` from
`ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`, historically
`DavisKahan/FiniteDimensional/Core/AngleGeometry.lean`. The exact original
statement and implementation can be recovered with:

`git show e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`

The accepted definition and the donor definition each map the corresponding
principal angles through `Real.tan`, with the same zero-padded `Finsupp` result.
The finite Davis--Kahan Ritz, graph-operator, canonical-embedding, source
presentation and challenge/comparator consumers now use `(approximateSubspace X).principalTangents U`
directly, retaining the local sine-embedding bridge needed for isometric trial
coordinates. The redundant private contraction proof in the finite Ritz module
is also removed in favor of the existing donor
`sinThetaEmbedding_apply_norm_le` theorem.

**Important scope boundary:** [#19329](https://github.com/TauCetiProject/TauCeti/pull/19329)
subsequently added `Submodule.tanThetaMap` and its principal-tangent
singular-value identity. It does **not** justify deleting the DKPS map
`tanThetaEmbedding U X = S |C|⁺` or the corresponding residual inequalities:
these maps have different source coordinates and different actions, even
when their singular values agree. Those results remain in the donor until an
exact replacement is available. No forwarding alias is introduced, and no
independent upstream proof is attributed to DKPS solely because it overlaps
our formalization.


## 2026-10-31: consume native coisometry singular-value padding

**Accepted source:** `TauCeti/Analysis/InnerProductSpace/SingularValues.lean` at
TauCeti `463ab293070d4cb355d0a0e036469464070088bc` defines
`LinearMap.singularValues_linearIsometry_comp` and
`LinearMap.singularValues_comp_adjoint_linearIsometry`. They preserve the exact
zero-padded singular-value sequence on postcomposition by an isometric embedding
and precomposition by its adjoint. These are the same statements as the DKPS
`TauCeti.singularValues_linearIsometry_comp` and
`TauCeti.singularValues_comp_adjoint_linearIsometry`, respectively, with
the second theorem taking its arguments in the opposite order.

**Historical donor:** `ForTauCeti/Analysis/InnerProductSpace/RectangularSingularValues.lean`
at DKPS commit `e4637c3919ae` (original `ForMathlib` extraction entry,
introduced by commit `82d20de`; Kitware 2026, Jon Crall, GPT-5.6 High,
Claude Fable 5; Apache-2.0). Recover with:

`git show e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/RectangularSingularValues.lean`

**Retired maintained mathematics:** The original DKPS proof of
`LinearMap.singularValues_adjoint` and its pointwise
`LinearMap.singularValues_adjoint_apply` wrapper; the DKPS postcomposition-isometry and
coisometry-padding theorems; the proof-only
`LinearIsometry.adjoint_eq_zero_of_mem_orthogonal`; and the private padded
orthonormal-basis / zero-eigenvalue argument used solely by the coisometry proof.
Their pre-retirement statements and implementation remain recoverable in Git;
`source_declarations` in the extraction manifest records the retired public names.

**Updated consumers:** Principal-angle embeddings, coordinate sine/cosine
embeddings, singular-value majorization and UI-seminorm transports, and the
planar zero-extension used in Davis--Kahan sharpness examples and the
sandwich-majorization proof now use the accepted `LinearMap` theorems directly. The rectangular Gram/eigenspace
comparison results and the genuine Ritz-residual tangent bounds are retained.
This is direct use of accepted APIs, not a claim that TauCeti adapted its
proofs from DKPS.

**Build boundary:** Source-to-API and reference checks support the retirement,
but do not substitute for Lean compilation. After `lake exe cache get`, build
`ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues`, the updated
principal-angle / coordinate-embedding / UI-seminorm consumers,
`DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceAssembly`, and the
repository default targets before committing.


## 2026-10-31: retire the C-star spectral-interval donor and unused singular-system proofs

**Whole-module retirement — norm versus real spectrum.** The DKPS module
`ForTauCeti/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean` (Kitware, Jon Crall,
Claude Fable 5; Apache-2.0) contained the theorem
`TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`:
for self-adjoint `a` and `0 ≤ r`, `‖a‖ ≤ r` iff `spectrum ℝ a ⊆ Set.Icc (-r) r`.
The identical statement is accepted as
`IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc` in
`TauCeti/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`,
[TauCeti #21259](https://github.com/TauCetiProject/TauCeti/pull/21259),
main commit `9af2e53076bedeb7ae6d0cdddb5f0057a1f66e52` (2026-10-30).
The accepted proof uses the real spectral-radius theorem; it is not represented here as a
port of the donor proof using continuous functional calculus. The earlier DKPS
spectral-gap inverse result was adapted in
[TauCeti #13872](https://github.com/TauCetiProject/TauCeti/pull/13872).

The entire local C-star module is deleted. Five direct importers use the native
TauCeti module; four theorem calls in the tangent/Riccati/Sylvester proofs
use the root `IsSelfAdjoint` name. The original source and transformation
history remain recoverable from donor revision `e4637c3919ae804c3f2ffd3356dd3d6132432d04`,
`ForTauCeti/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`; its provenance
header records earlier `ForMathlib` development at `fc38eb4`. The manifest
retains the historical declaration names and the accepted replacement.
There is no forwarding module or forwarding theorem.

**Partial local singular-system retirement.** The following four DKPS declarations
in `ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean` no longer have
maintained source consumers: `TauCeti.selfCompAdjoint_apply_leftSingularVector`,
`TauCeti.singular_reconstruction`, `TauCeti.eq_sum_singularValue_rankOne`, and
`TauCeti.exists_orthonormalBasis_extending_leftSingularVector`. The accepted
`TauCeti/Analysis/InnerProductSpace/SingularValues.lean` provides, respectively,
`LinearMap.self_comp_adjoint_leftSingularVector`,
`LinearMap.apply_eq_sum_singularValues_smul`,
`LinearMap.eq_sum_singularValues_smul_rankOne`, and
`LinearMap.exists_orthonormalBasis_apply_eq_leftSingularVector`. The final theorem
upstream even chooses a compatible indexed codomain basis, stronger than the
original set-range inclusion. The finite singular expansion uses the same
ordered eigenbasis and normalized left vectors, with scalar factors grouped
differently. No maintained proof relies on the four retired names; the stale
reference in `DavisKahan/Explorations/Historical/SourceUnitaryInvariantNormFanDominance.lean`
is kept as historical text because that file is explicitly not a build target.

The still-used local definitions and singular relations are intentionally retained;
this change does not erase the genuine Ritz-residual and coordinate tangent results.
The original complete singular-system source is preserved in donor revision
`e4637c3919ae804c3f2ffd3356dd3d6132432d04`,
`ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean` (earlier origin
`82d20de`, Kitware, Jon Crall, GPT-5.6 High, Claude Fable 5; Apache-2.0).
The TauCeti singular-system implementation is identified as overlapping accepted
mathematics, not asserted to be copied from DKPS.


## 2026-10-31: consume accepted native matrix rank factorization

**Full donor-module retirement (MSS-A08).** The 301-line
`ForTauCeti/LinearAlgebra/Matrix/RankFactorization.lean` is deleted from
maintained DKPS sources. Original proof code is preserved in repository history
at `e4637c3919ae:ForTauCeti/LinearAlgebra/Matrix/RankFactorization.lean`,
tracing earlier to `7bc63b8` in the former `ForMathlib` staging layer. The original
Kitware development is attributed to Jon Crall and Claude Fable 5 (Apache-2.0).

The accepted TauCeti replacements at pin `463ab293070d` are:

- `TauCeti/LinearAlgebra/Matrix/Rank.lean`: `Matrix.exists_eq_mul_fin_rank`
  (originally `TauCeti.Matrix.exists_eq_mul_rank`),
  `Matrix.exists_eq_mul_of_rank_le`, and `Matrix.rank_le_iff_exists_eq_mul`;
  accepted as part of [#14510](https://github.com/TauCetiProject/TauCeti/pull/14510),
  main commit `2e37076eb3` (2026-10-11). The native implementation uses
  linear-map/basis factorization and accepts arbitrary row index types.
- `TauCeti/LinearAlgebra/Matrix/Rank/Factorization.lean`:
  `Matrix.exists_unit_eq_mul_of_rank_factorization` generalizes the original
  `TauCeti.Matrix.exists_units_eq_mul_of_rank_factorization` from `Fin r` to
  an arbitrary finite intermediate index type; adapted with direct DKPS source
  attribution in [#13475](https://github.com/TauCetiProject/TauCeti/pull/13475),
  main commit `1d10f2719b` (2026-10-16).
- `Matrix.rank_left_factor_eq`, `Matrix.range_left_factor_eq` (native `Rank.lean`)
  and `Matrix.exists_mul_eq_of_range_le`,
  `Matrix.mul_left_cancel_of_mulVec_injective` (native `Range.lean`) replace
  the donor's proof-only lifting, rank/range, and cancellation machinery.

The still-unmerged result in
`ForTauCeti/LinearAlgebra/Matrix/PosDef.lean` (rank-constrained positive
semidefinite Gram realization) is **retained**, with its rank-factorization
step now calling `Matrix.exists_eq_mul_of_rank_le` directly. The paired rank
challenge's independent conformance statement and its leaderboard now use
TauCeti's native `Matrix` namespace and the renamed exact-rank theorem.
No forwarding alias is kept in `ForTauCeti`. The module-plan seed and
manifest staging reference are removed, and the manifest's historical record
retains the original declaration names and new destinations.

**Build boundary:** Source-reference and archive checks are not Lean
compilation. In the live checkout, run `lake exe cache get`, build
`ForTauCeti.LinearAlgebra.Matrix.PosDef` and the challenge modules, then
run the repository default `lake build` before committing this deletion.


## 2026-11-01: consume native entrywise matrix eigenvalue bounds

**Full donor retirement (MSS matrix spectral bounds).** Delete the 80-line
`ForTauCeti/Analysis/Matrix/EntrywiseEigenvalue.lean` module after migrating its sole
source importer `RoadmapBridge.OperatorTheory` to the accepted
`Matrix.IsHermitian.abs_eigenvalues₀_sub_le_of_entry_le`. The donor theorem was
`TauCeti.Matrix.abs_eigenvalues₀_sub_le_of_entry_le` for `Fin n` matrices; the
accepted result works for arbitrary finite index types (including empty types)
and has the same numerical coefficient. `Fintype.card_fin` transports the bound.

The accepted TauCeti result is in
`TauCeti/Analysis/Matrix/Eigenvalues.lean`, [PR #15222](https://github.com/TauCetiProject/TauCeti/pull/15222),
main commit `20f931816c` (2026-10-12), present at the pinned revision
`463ab293070d`. The DKPS original is recoverable at
`e4637c3919ae:ForTauCeti/Analysis/Matrix/EntrywiseEigenvalue.lean`; its
earlier `ForMathlib` introduction was `2356fd0` (Jon Crall, Claude Opus 4.8;
Apache-2.0, Kitware, Inc.). The statements overlap mathematically; this
entry does not assert the TauCeti proof was copied from DKPS.

**Partial retirement of spectral measurability donor.** Remove
`TauCeti.Matrix.abs_eigenvalues₀_le_of_entry_le` and the one-sided
`TauCeti.Matrix.eigenvalues₀_le_of_entry_le` from
`ForTauCeti/Analysis/Matrix/SpectralFunctionMeasurable.lean`.
The native `Matrix.IsHermitian.abs_eigenvalues₀_le_of_entry_le` supplies the
stronger statement; the one-sided estimate follows from `le_abs_self`. Update
`Acharyya2025.ManifoldCondition`, `DkpsQuench2026.Spectral.Regularity`, and
`Helm2025.AcharyyaBridge` to consume it directly. The original local proofs
remain recoverable from the same donor revision `e4637c3919ae`, tracing the
measurability module's initial `ForMathlib` source `82989e1` (Jon Crall,
Claude Fable 5, Claude Opus 4.8; Apache-2.0).

The remaining matrix spectral measurability definitions, spectral projection
construction, and statistical/paper-facing conclusions are **not** removed.
No forwarding aliases are introduced. The extraction manifest and module plan
record the source retirement; these are independent from compilation evidence.

## 2026-11-01: retire the independently implemented finite-mean and centered-scatter donor

**Full donor retirement (MSS-C06--C14).** Remove the 273-line
`ForTauCeti/Probability/Moments/CenteredScatter.lean` and migrate its only maintained
Lean importer, `DkpsQuench2026/Spectral/GramSpectrum.lean`, to
`TauCeti.Analysis.Convex.FiniteMean` and
`TauCeti.Analysis.InnerProductSpace.CenteredScatter`. The Quench spectral-floor
and centered-augmentation results remain; their statements do not change.

The original Kitware donor was authored at `fc38eb4` in
`ForMathlib/Analysis/InnerProductSpace/CenteredScatter.lean` (Jon Crall,
GPT-5.6 High, Claude Fable 5; Apache-2.0), and its complete pre-retirement
source is recoverable from
`e4637c3919ae:ForTauCeti/Probability/Moments/CenteredScatter.lean`. The
original declarations and exact accepted replacements are recorded in the
`extraction-manifest.json` record. The original DKPS statement uses `Fin n`;
TauCeti's replacement works over an arbitrary finite index type.

**Independent upstream mathematics, not proof descent.**
[#15445](https://github.com/TauCetiProject/TauCeti/pull/15445), accepted on
TauCeti `main` as commit `819340e91e33bd6aeb480d520f39308421e08c67`,
**explicitly states that its implementation was independent of the DKPS bulk
port #13876**. The commit is an ancestor of the pinned TauCeti main
`463ab293070d4cb355d0a0e036469464070088bc`. Do not count this as a DKPS proof
port. It supersedes the local implementation, so there is no reason to
continue maintaining the duplicate.

The Quench proof now uses `finiteMean_eq_inv_smul_sum`,
`re_inner_centeredScatter_apply_self`, and
`re_inner_centeredScatter_snoc_apply_self`. No replacement adapters,
forwarding aliases, or new theorem statements are introduced. The remaining
SampleMean, Variance, and matrix-concentration donors are not affected.

**Build boundary:** Source inspection and fresh ZIP extraction do not certify
Lean compilation. In the live checkout, build
`DkpsQuench2026.Spectral.GramSpectrum` and the default `lake build` before
committing the deletion.


## 2026-11-01: consume SSP-C09/C10 bounds, retain the broader pointwise donor

**Bounded-operator consumption (14 donor lines plus 26 consumer lines retired).**
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/OperatorNorm.lean` now imports
`TauCeti.Analysis.InnerProductSpace.Projection.Block` directly. Its two
coercivity/upper-bound steps use
`ContinuousLinearMap.le_re_inner_reducedExtension_self` and
`ContinuousLinearMap.re_inner_reducedExtension_self_le`, replacing the private
`re_inner_reducedExtension_self'` wrapper and its repeated Pythagorean algebra.
The public theorem `exists_isSymmetric_comp_sub_comp_eq`, its two coercivity
bounds, its Sylvester residual identity, and downstream sin-Θ results retain
their original statements. The local `norm_sq_eq_starProjection_add_sub`
helper is retired: `Submodule.norm_sq_eq_add_norm_sq_starProjection` is
available upstream and used by the native form-bound proofs.

**Genuinely remaining statement.** The donor module stays in the tree, with its
`TauCeti.re_inner_reducedExtension_self` theorem. Unlike the accepted bounded
`ContinuousLinearMap` result, it assumes only an arbitrary
`R : E →ₗ[𝕜] E`, without continuity or finite-dimensionality. This is
strictly broader in carrier scope and is not claimed to be upstreamed. The
last maintained consumer happens to convert finite-dimensional maps to bounded
maps, so it can use the accepted API directly without requiring a new adapter.

**Provenance.** [TauCeti PR #19277](https://github.com/TauCetiProject/TauCeti/pull/19277)
explicitly identifies the maintained Kitware DKPS
`ForTauCeti/Analysis/InnerProductSpace/ReducedExtension.lean` as the source
for its accepted bounded reduced-extension mathematics. Integration commit
`ca1eac22f582487d71706084aee719436b098186` is an ancestor of pinned main
`463ab293070d4cb355d0a0e036469464070088bc`. The original DKPS donor at
`e4637c3919ae` is attributed to Jon Crall and Claude Opus 5 (Apache-2.0).
TauCeti `Projection.Block` separately credits the Spectra Formalization
Project for the broader projection-block development. Both provenances are
retained without claiming the proofs were copied verbatim. See the existing
`extraction-manifest.json` for source declarations and replacement mapping.


## 2026-11-01: near-isometry polar factorization consumes independent TauCeti #16127

**Retired private implementation, retained paper-facing statements.** The
maintained donor `ForTauCeti/Analysis/InnerProductSpace/NearIsometry.lean`
previously reconstructed the modulus and unitary polar factor using a custom
real orthonormal eigenbasis, diagonal operators, and inverse-square-root
coordinates. Its private lemmas for diagonal arithmetic, spectral estimates,
Gram eigenbasis construction, and isometry extension have no remaining
consumers and are now removed.

The same public factorization theorem
`TauCeti.LinearMap.exists_linearIsometryEquiv_comp_polarFactor` is proved by
taking `S = M.operatorAbs` and `W` from the accepted
`LinearMap.exists_linearIsometryEquiv_comp_operatorAbs_eq`, with
`LinearMap.isSymmetric_operatorAbs`, `LinearMap.operatorAbs_sq`, and
`LinearMap.norm_operatorAbs_apply_sub_le`. The original sharp estimate and
historical factor-two variants retain their statements for Acharyya and
challenge consumers; there is no new TauCeti forwarding API.

**Scope and lineage.** [PR #16127](https://github.com/TauCetiProject/TauCeti/pull/16127)
provides the finite-dimensional `RCLike` unitary polar construction and the
modulus estimate, strictly generalizing the real-specific algebraic foundation
used here. Its integration commit `2b69ec4d36` is in the pinned TauCeti main
snapshot `463ab293070d`. The PR *explicitly calls its proof independent* of the
DKPS donor; it must not be counted as a DKPS proof port. The historical donor
was introduced in Davis--Kahan commit `fc38eb4` for Jon Crall, developed by Claude Fable 5
and Claude Opus 4.8, then redesigned by Claude Opus 5 (Kitware, Apache-2.0).
The original reconstruction is present in donor revision `e4637c3919ae`.
The local five public declarations are preserved, and their original naming
and source history remain in `extraction-manifest.json`.

## 2026-11-01: SA-B02 consumes the accepted one-measure continuous-approximation theorem

**Removed donor implementation.** In
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean`,
`TauCeti.BorelCalculus.exists_continuous_integral_norm_sub_le` was the
one-measure L¹ approximation of an integrable complex-valued function on the
compact operator spectrum. Its local proof is now deleted; direct consumers
in `BorelCalculus/Operator.lean` and `BorelCalculus/Multiplicative.lean`
apply `ν.exists_continuous_integral_norm_sub_le` from
`TauCeti.MeasureTheory.Function.ContinuousApproximation`. The accepted
`MeasureTheory.Measure.exists_continuous_integral_norm_sub_le` is the same
estimate for **any** compact metric Borel space, not only an operator spectrum.
No local compatibility alias was retained.

**Lineage.** [TauCeti #18907](https://github.com/TauCetiProject/TauCeti/pull/18907)
(SA-B02) explicitly states that its approximation proof was **adapted from**
the maintained Kitware DKPS donor module. Its integration commit is
`254557afab32f37a4214172559f7849c801f5ba3`, included in pinned TauCeti
`463ab293070d4cb355d0a0e036469464070088bc`.
Original donor revision `e4637c3919ae` retains Kitware's Apache-2.0
copyright and authors Jon Crall and Claude Opus 5. The full original
`source_declarations` list remains in `extraction-manifest.json`.

**Scope retained in DKPS.** The polarized integral `pair`, `pair_of_continuous`,
`norm_integral_sub_integral_le`, `norm_pair_sub_pair_le`, `pairVectors`, and
`diagMeasure_le_sum` remain local, as do downstream Borel-calculus constructions.
This consumption does not claim that those results have migrated to the accepted
general approximation theorem.


## 2026-11-01: MSS-C01 uncentered Chebyshev consumption

**Full 83-line donor retirement.** Remove
`ForTauCeti/Probability/Moments/Variance.lean` (originally
`ForMathlib/Probability/Moments/Variance.lean`) and migrate the maintained
Quench, Acharyya, and probability-challenge consumers from
`TauCeti.meas_gt_le_ofReal_integral_sq_div_sq` to
`TauCeti.meas_gt_le_div_sq_of_integral_sq_le` in
`TauCeti.Probability.Moments.Chebyshev`. The accepted theorem gives the same
uncentered event bound from integrability and `∫ Y² ≤ v`, but it needs no
`IsProbabilityMeasure` instance and takes arguments in the order
`(integrability, moment bound, positive threshold)`. The paper-facing
`Acharyya2024.Probability.meas_gt_le_ofReal_secondMoment_div_sq` remains with
its original theorem type and uses the accepted result directly. No new alias
or substitute proof is introduced in `ForTauCeti`.

**Distinct mathematical lineage.** The historical Kitware donor was introduced
at Davis--Kahan commit `56f7495`, authored by Jon Crall and Claude Fable 5,
Apache-2.0; its original implementation is recoverable in donor revision
`e4637c3919ae:ForTauCeti/Probability/Moments/Variance.lean`.
[TauCeti PR #15962](https://github.com/TauCetiProject/TauCeti/pull/15962)
(MSS-C01--C05), integrated as
`8c6d1312b675b1443cb85c6de6dff4b8b8ba93c4`, **explicitly says its
implementation was written independently of the DKPS bulk port #13876**.
This is replacement by accepted mathematics, **not** a DKPS proof port.
The separate `ForTauCeti/Probability/Moments/SampleMean.lean` still contains
local finite-sample proofs and remains available for subsequent migration.


## 2026-11-01: MSS-C02--C05 sample-mean donor consumption

**Complete donor retirement.** Remove
`ForTauCeti/Probability/Moments/SampleMean.lean`, the 275-line historical Kitware
`ForMathlib` sample-mean implementation, and migrate its direct Acharyya and Quench
consumers to `TauCeti.Probability.Moments.SampleMean`. The four retired declarations
are `TauCeti.integral_sq_scaledSum_sub_of_pairwise_indep`,
`TauCeti.integral_norm_sq_average_sub_eq_sum`,
`TauCeti.integral_norm_sq_average_sub_of_iid`, and
`TauCeti.integral_norm_sq_average_sub_le_of_bound`.

**Accepted replacements.** The scalar identity uses
`TauCeti.integral_finiteMean_sub_sq`; the vector identity uses
`TauCeti.integral_norm_finiteMean_sub_sq`; the identical-error and uniformly
bounded cases are supplied respectively by
`TauCeti.integral_norm_finiteMean_sub_sq_of_forall_eq` and
`TauCeti.integral_norm_finiteMean_sub_sq_le_of_forall_le`. The accepted API
expresses the mean as `TauCeti.finiteMean`; DKPS call sites rewrite it by
`TauCeti.finiteMean_eq_inv_smul_sum` and instantiate the nonempty `Fin r` index
from the already-assumed positive sample count. The upstream vector theorem
works for any complete real inner product space, strictly beyond the donor's
finite-dimensional space assumption. Acharyya2024's coordinate-to-Bochner
mean bridge and original paper statements are retained. Both Quench scalar
spectral regularity estimates and the evaluation/raw-response moment bounds
use upstream theorems directly. The generic SampleMeanMSE comparator fixture
and runner entry are retired: they compare the removed generic donor to its
own copied statements, while the unchanged Acharyya/Quench statements exercise
the accepted replacement at the paper boundary. They impose no stronger
mathematical contract. The original fixture is recoverable from Git history.

**Lineage.** The DKPS donor was introduced at Davis--Kahan commit `e9379f2`,
with original authors Jon Crall and Claude Opus 4.8, Copyright 2026
Kitware, Inc., Apache-2.0. The last donor implementation is recoverable at
`e4637c3919ae:ForTauCeti/Probability/Moments/SampleMean.lean` (and its
original namespace/file in the prior Davis--Kahan history).
[TauCeti #15962](https://github.com/TauCetiProject/TauCeti/pull/15962),
integration commit `8c6d1312b675b1443cb85c6de6dff4b8b8ba93c4`,
**explicitly identifies its implementation as independent of the DKPS bulk
port #13876**. The PR's MSS-C01--C05 scope includes the uncentered
Chebyshev theorem consumed in the preceding batch; this batch consumes
MSS-C02--C05, not any unmerged higher-moment or matrix concentration work.

## 2026-11-01: consume the accepted singular system and Moore–Penrose construction

The remaining `ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean`
implementation is retired. Its ordered right Gram eigenbasis and normalized
left vectors coincide with the definitions accepted in
[TauCeti #13967](https://github.com/TauCetiProject/TauCeti/pull/13967), integration
`2aa5bee4a1a6ffac8becf3c118884b2ab9cf9486`. Consumers use
`LinearMap.rightSingularBasis`, `leftSingularVector`,
`adjoint_comp_self_rightSingularBasis`, `apply_rightSingularBasis_eq_zero_iff`,
`apply_rightSingularBasis`, `orthonormal_leftSingularVector`,
`norm_apply_rightSingularBasis`, and `adjoint_leftSingularVector` directly.
The last relation upstream covers zero singular values too. This completes the
partial retirement recorded on October 31; its four earlier replacement
mappings remain in the manifest. The principal-plane, trial-coordinate,
double-angle, and finite-source arbitrary-Hilbert-codomain mathematics remains.

`ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean` now uses the
accepted `LinearMap.moorePenroseInverse` and `LinearMap.IsMoorePenroseInverse`
from [#13805](https://github.com/TauCetiProject/TauCeti/pull/13805), integration
`0edbdff64319599032f45b534ae7de31b86c3b21`. The local construction, four
Penrose proofs, uniqueness, adjoint compatibility, injective case, and their
coordinate proof machinery are removed. Consumers use the accepted predicate's
fields and `moorePenroseInverse_comp_of_injective`. The donor retains the two
self-adjoint commutation extensions and the kernel-inclusion factorization;
these results are absent from the pinned accepted API. Their carrier is the
accepted inverse, with no compatibility definition or forwarding alias.

Both integrations are ancestors of pin `463ab293070d`. Neither PR supplies
evidence that its proof was adapted from DKPS; record mathematical replacement,
not proof descent. Historical Kitware Apache-2.0 source remains at
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean`
(introduction `82d20de`, Jon Crall, GPT-5.6 High, Claude Fable 5) and
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean`
(introduction `caa0966`, Jon Crall, GPT-5.6 Thinking). The manifest preserves the
original declarations, including those removed by the earlier partial retirement.

## 2026-11-01: retire the rectangular Fan-dominance proof engine

`UnitarilyInvariantSeminorm/Majorization.lean` retains only the Sylvester
coefficient-mass budget and its nonnegative scaling theorem. The coordinate
unitary-extension, diagonal-lift, SVD-transport, transfer-descent, convex-hull
norm comparison, and bounded-factor implementations are removed. The retained
budget proof scales a unit-mass certificate supplied by TauCeti, rather than
reconstructing a convex combination. The donor's linter override is removed.

The accepted replacements, both in pin `463ab293070d`, are:

- [#14308](https://github.com/TauCetiProject/TauCeti/pull/14308), integration
  `9de0d666098a9ef046dbb7ce3384f0e63af2980c`:
  `LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le`,
  `UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull`,
  `UnitarilyInvariantSeminorm.map_le_of_mem_twoSidedUnitaryOrbitHull`, and
  `map_le_of_kyFanSum_le`.
- [#14662](https://github.com/TauCetiProject/TauCeti/pull/14662), integration
  `38596bb4395faa26cd9c2ede1df65b5e67aeaa0b`: `map_comp_le_left` and
  `map_comp_le_right`. These also allow negative factor-bound constants,
  strictly extending the retired nonnegative-constant statements.

Paper-facing Ky Fan statements retain their finite-prefix presentation;
consumers translate with `kyFanSum_eq_linearMap_kyFanSum`. The block-sum norm
comparison uses `LinearMap.prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull`.
The existing challenge dependency audit now names the accepted leaves.
No forwarding Fan-dominance theorem remains in `ForTauCeti`.

The original source is preserved at
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Majorization.lean`,
with Jon Crall / Claude Fable 5, Kitware copyright, and Apache-2.0 attribution;
the API unification at `bf84b6ff1` credits GPT-6 Astra. The existing manifest
preserves the retired declarations. The accepted Fan-dominance and gauge proofs
are not claimed to be DKPS adaptations. Their use of the DKPS-adapted
seminorm/certificate API from #14241 is **transitive reuse**, not descent of the
Fan-dominance proof itself. The still-local budget extension is not marked
accepted upstream.

## 2026-11-01: canonical unbounded resolvents and Cayley consumers

Deleted `ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean`
(484 lines) and `LinearPMap/SelfAdjointResolvent.lean` (349 lines).
All maintained inverse, resolvent-set, shift identity, Neumann, bounded-operator
bridge, Cayley, spectral-measure, and real/complexification consumers now use
accepted root `LinearPMap` / `IsSelfAdjoint` APIs. Local/root inverse conversions
and the paper-side real-set equivalence are removed. Pure spectral symbols take
the operator rather than a vacuous proof argument. General-field mathematical
scope is preserved.

The accepted core is broader: topological modules for the algebraic foundation,
and `HasSummableGeomSeries` rather than ambient completeness for perturbations.
Its integrations, all ancestors of pin `463ab293070d`, are
[#12771](https://github.com/TauCetiProject/TauCeti/pull/12771)
`83eb0f7fbeb835397951914067a0b6fc359cf914`,
[#14357](https://github.com/TauCetiProject/TauCeti/pull/14357)
`711bc67a45daa2b57ba1539190a9daa15ac05613`,
[#14459](https://github.com/TauCetiProject/TauCeti/pull/14459)
`9c887749b7f41032d4ba21b2b637f083b75c91a4`, and
[#21914](https://github.com/TauCetiProject/TauCeti/pull/21914)
`2c980efea6aed36e84d620692293712b261d1a96`.
The donor was a generalized upstream copy, credited to Tau Ceti contributors
under Apache-2.0 at upstream `1b39d420ac84ed9a5a7d536ce19b37818ad29c39`;
no original Kitware proof contribution is claimed for that core.

Independent self-adjoint resolvent laws come from
[#14305](https://github.com/TauCetiProject/TauCeti/pull/14305),
`b9288156cab0e9acffe09889dbb4f42a1b7d63cd`; independent Cayley unitarity
and normality come from
[#15559](https://github.com/TauCetiProject/TauCeti/pull/15559),
`54252fb0e940e9de464fb187faa1ddf4fa69f7fc`. Their transitive use of
DKPS-adapted self-adjoint foundations is distinct from proof adaptation.
Native `LinearPMap.IsFormalAdjoint.norm_smul_sub_sq` and
`abs_im_mul_norm_le_norm_smul_sub` cover the complex shift estimates;
self-adjoint shift bijectivity covers the specialized closed/dense-range proof.
Separate `Shift` / `RealLowerBound` donors retain additional RCLike lower-bound
and orthogonality results. Historical source is
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean`,
Jon Crall / Claude Opus 5, Kitware copyright, Apache-2.0. The deleted core is
recoverable at the same source commit under its former path. The existing
manifest preserves historical declaration names and source ancestry.

## 2026-11-01: retire lower-bound inversion and auxiliary analytic proofs

Deleted `LinearPMap/Shift.lean` and `LinearPMap/ResolventBound.lean` and removed
the injectivity, real-shift density, and inverse construction from
`RealLowerBound.lean`. Paper gap, form, Sylvester and free-beam consumers now
apply `IsSelfAdjoint.mem_resolventSet_of_norm_le` directly; `norm_sub_rev`
translates the opposite shift sign. The accepted RCLike theorem covers arbitrary
shifts, strictly extending the real-shift donor. Inverse norms use
`LinearPMap.IsResolventAt.norm_le_inv`. These are independent accepted
[#14305](https://github.com/TauCetiProject/TauCeti/pull/14305),
`b9288156cab0e9acffe09889dbb4f42a1b7d63cd`, with transitive reuse of adapted
self-adjoint foundations. The canonical `smulSub` and lower-bound closed/dense
range facts replace the unconsumed opposite-sign shift implementation.
`RealLowerBound` retains only the coercivity-to-norm estimate and its direct
canonical-inversion consequence; the mathematical estimate is not superseded.

The unused product/commutation specializations and one-direction spectral
mapping proof are subsumed by the canonical first resolvent identity and
`TauCeti.LinearPMap.notMem_spectrum_resolvent_iff` in
[#14486](https://github.com/TauCetiProject/TauCeti/pull/14486),
`bd5ca4d951ad85677e9b60deb0d11f13279fc37c`. The latter is an independent
both-directions theorem over topological fields/modules, broader than the
retired RCLike normed-space statement. No proof descent is claimed.
Historical Kitware Apache-2.0 sources are preserved at `e4637c3919ae` under
the deleted paths and `RealLowerBound.lean`, Jon Crall / Claude Opus 5;
`ResolventBound` introduction is `a58913e9e`. Later shift factoring at
`b95a44bea` credits GPT-6 Astra. The existing manifest retains original names.

Removed the duplicate `LinearPMap.IsClosed.mem_domain_of_tendsto` proof from
`GraphCore.lean`. Its accepted replacement in
[#13871](https://github.com/TauCetiProject/TauCeti/pull/13871),
`b73f7898d5854ded5adbc9fa738a8f150c039724`, explicitly adapts DKPS and
extends sequences in inner product spaces to arbitrary nontrivial filters over
topological modules. The Riccati consumer uses that accepted declaration.
`IsGraphCore`, `top`, and `ambient_approximation` remain: they express sequential
graph density without closedness, which cannot simply be identified with
Mathlib's `HasCore`. Source: `e4637c3919ae`, earlier `CommonCore.lean`,
Jon Crall, Kitware copyright, Apache-2.0.

Removed the determinant, adjugate and inverse measurability helpers from
`MeasureTheory/MatrixKernelSelection.lean`. Its approximants use the accepted
matrix `MeasurableInv` instance, `Measurable.inv`, and `Matrix.measurable_iff`.
Independent [#6967](https://github.com/TauCetiProject/TauCeti/pull/6967),
`42f6e23a92392ac7001bbda30dc71f3d38c20672`, covers arbitrary finite matrix
indices and suitable fields, with no invertibility hypothesis. The measurable
unit kernel-vector selection and pointwise kernel-projection limit remain;
they are not consequences supplied by that replacement. Historical source is
`e4637c3919ae:ForTauCeti/MeasureTheory/MatrixKernelSelection.lean`, introduction
`cf57b8201`, Jon Crall / Claude Fable 5, Kitware copyright, Apache-2.0.
All cited integrations are contained in pin `463ab293070d`.

## 2026-11-01: canonical finite polar factors and modulus comparisons

Retired the modulus and restricted-modulus polar construction from
`Polar/Decomposition.lean`. Direct rotations, principal planes, alignment,
intertwining unitaries, singular-subspace arguments and UI-seminorm consumers use
`LinearMap.operatorAbs` and `LinearMap.polarFactor` directly, with native
norm/kernel/range, factorization, commutation and adjoint facts. The accepted
factor supports rectangular RCLike maps; its adjoint law has no invertibility
hypothesis, strengthening the old square invertible result. The two modulus
bridges in `Polar/CFCBridge.lean` are deleted; callers use
`LinearMap.toContinuousLinearMap_operatorAbs_eq_cfcAbs` and
`toContinuousLinearMap_operatorAbs_eq_modulus` directly.

Accepted integrations, all in pin `463ab293070d` (independent implementations
unless noted otherwise):

- [#13940](https://github.com/TauCetiProject/TauCeti/pull/13940),
  `7b2a8f443f96040539e6479461b3325307ffb9bb`: finite positive square root/modulus.
- [#16086](https://github.com/TauCetiProject/TauCeti/pull/16086),
  `0a2aed9e3a73e222aadd47ef9a13c09b1c256385`: canonical rectangular polar factor.
- [#16450](https://github.com/TauCetiProject/TauCeti/pull/16450),
  `7d1da9ada3041f5e1e5d10884964da59fc89e5b9`: adjoint law and unitary extensions.
  Its integration explicitly says it does not copy or adapt the DKPS implementation.
- [#16523](https://github.com/TauCetiProject/TauCeti/pull/16523),
  `893678359b586eace5dfe8ce192eb8a725406cb6`: finite/bounded CFC comparison.
- [#20358](https://github.com/TauCetiProject/TauCeti/pull/20358),
  `f4a3266bdf016c565840d069c5db06eb5352ddd1`: finite/bounded modulus agreement.
  Jon Crall authored this direct bridge from accepted comparison lemmas; it does
  not copy the donor square-root uniqueness proof.

Retained selected square unitary APIs are used by direct rotations and alignment.
The singular-case choice now uses the accepted extension theorem instead of
reproving isometric extension. A selected unitary's kernel action is not
canonical; it is distinct from the canonical polar partial isometry. Extra
negation/normal-adjoint modulus identities and uniqueness against a competing
positive factor remain. The local functional-calculus comparison and bounded
polar-decomposition presentation use the native engine. No forwarding alias for
the retired modulus, polar factor or their core theorems remains.

Historical Kitware Apache-2.0 source is at `e4637c3919ae` under the two donor
paths, originating in `ForMathlib.Analysis.InnerProductSpace.PolarDecomposition`
at `3676b5559`, Jon Crall / Claude Opus 4.8. The manifest now records the
original declarations of both split modules rather than an empty inventory.
These replacements distinguish independent foundations from the Jon Crall-authored
accepted comparison bridge; no donor-proof descent is inferred.

## 2026-11-01: canonical finite symmetric functional calculus

Removed `TauCeti.selfAdjointFunctionalCalculus` and its duplicate core proofs.
All maintained consumers use `LinearMap.IsSymmetric.cfc` and accepted algebra,
eigenvector, positivity, norm, intertwining and commutant-preservation laws.
The defining spectral sums were proved equal with native `cfc_eq_sum` before
retirement. Independent [#13785](https://github.com/TauCetiProject/TauCeti/pull/13785),
`cb2fd0c03991250f6eea42030c41a3d025512cb8`, supplies the same arbitrary-symbol
RCLike calculus; it does not require symbol continuity. Indexed paper estimates
explicitly convert the native `HasEigenvalue` hypotheses through ordered
eigenvalues. The zero-dimensional case remains covered.

`SelfAdjointFunctionalCalculus.lean` retains coordinate vanishing, transfer
between two scalar symbols, and extraction of a preimage eigenvalue from an
eigenvector of `f(T)`: these are not supplied by the accepted module. Its short
dependent operator-congruence lemma is now `cfc_congr_operator`. The planar
paper's scalar-operator evaluation is private and follows directly from native
eigenvector action; the sole square-symbol calculation uses native multiplication
and identity laws. There is no forwarding calculus definition or core alias.

Deleted the rest of `Polar/CFCBridge.lean`, including `calculusStarAlgHom`, its
norm/identity/algebra proofs, and the globally continuous complex comparison.
Native `IsSymmetric.toContinuousLinearMap_cfc` from
[#16523](https://github.com/TauCetiProject/TauCeti/pull/16523),
`893678359b586eace5dfe8ce192eb8a725406cb6`, is stronger: arbitrary symbols and
RCLike scalars. The directed-tangent consumer also removes its duplicate private
`ContinuousOn` comparison and finite CFC eigenvector proof, applying accepted
`ContinuousLinearMap.cfc_apply_of_apply_eq_smul` directly. Its original source
hypotheses remain in the paper-facing statement. Unused symbol-extension helpers
and the finite bounded-polar presentation were proof support for the superseded
construction and are retired with it; canonical polar factorization and the
accepted modulus comparison cover their mathematical scope.

Historical sources are `e4637c3919ae` under the two donor paths: the calculus
originates at `caa0966`, Jon Crall / GPT-5.6 Thinking; the polar/CFC bridge at
`3676b5559`, Jon Crall / Claude Opus 4.8. Both retain Kitware copyright and
Apache-2.0 attribution in the manifest. No proof adaptation is inferred for
#13785 or #16523; the distinct Jon Crall-authored #20358 comparison bridge is
recorded above. All integrations are in pin `463ab293070d`.


## 2026-11-01: canonical bounded polar factors and injective-factor uniqueness

Retired the range-extension engine in `Polar/PartialIsometry.lean`:
`polarInitial`, `modulusCorestrict`, `polarInitialMap`, `polarPartial`,
`polarInitialIsometry`, `polarFinal` and their construction, kernel/range,
projection, factorization, adjoint, inverse and uniqueness proofs. The full
RCLike complete-space equality with the accepted factor was compiled before
removal using `ContinuousLinearMap.eq_polarFactor`. Maintained callers now use
`ContinuousLinearMap.polarFactor`, `(ker M)ᗮ` and `range.topologicalClosure`
directly. Polar intertwining uses native factorization uniqueness; the obsolete
`TauCeti.adjoint_comp_self_comp_modulus` support wrapper in
`PrincipalAngles/Equisingular.lean` is gone.

Accepted [#16936](https://github.com/TauCetiProject/TauCeti/pull/16936),
`3266a7a2637755febeecd0484d578678a508d44e`, is an ancestor of pin
`463ab293070d`. It constructs the factor through `factorThru`, rather than the
donor range-extension implementation. No direct donor proof adaptation is
claimed. Its partial-isometry dependency explicitly adapts Kitware proofs;
that is transitive reuse, not authorship of the canonical polar construction.
The donor now retains five additional commutant, negation and skew-adjoint
identities on the accepted factor. `Polar/Symmetry.lean` consumes these
negation/skew identities, removing its duplicate square specializations.

`Polar/Isometry.lean` also loses its inverse-defined
`polarIsometryOfIsUnitModulus` and `polarLinearIsometry`/`polarLinearIsometryEquiv`
factories. Reflection-tangent proofs use native norm preservation and a standard
isometry bundle. The retained modulus-invertibility criteria and sharp
pointwise/rectangular Gram perturbation bounds are now stated on the canonical
factor. They cover rectangular complex Hilbert spaces, whereas the accepted
`norm_sub_polarFactor_le` is an endomorphism bound. The old inverse constructor's
junk branch has no maintained consumer; no equality with the canonical factor
is claimed in that branch.

Finally, `Polar/Decomposition.lean` loses
`TauCeti.polarFactor_eq_of_isUnit_eq_comp_positive`. Finite direct rotation
applies `LinearMap.eq_polarIsometry_of_comp_eq` and
`polarIsometry_toLinearMap` directly. Accepted
[#16080](https://github.com/TauCetiProject/TauCeti/pull/16080),
`18681919170b67de8799d152b7a29a9a6a315889`, covers rectangular injective maps,
strictly beyond the old square invertible formulation. The later source
reference [#20360](https://github.com/TauCetiProject/TauCeti/pull/20360),
`3f89d482c31ad0fb4325394ea7ba001e7d65c8c1`, cites the donor statement;
a citation is not a claim of proof adaptation.

Historical sources remain at `e4637c3919ae` under the three donor paths.
`PartialIsometry` credits Jon Crall, Claude Opus 5 and OpenAI GPT-5.6 Sol;
`Isometry` credits Claude Opus 5; finite `Decomposition` credits Jon Crall and
Claude Opus 4.8 (introduction `3676b5559`). All carry Kitware copyright and
Apache-2.0. The manifest preserves original declaration names and distinguishes
retired construction from the retained quantitative and algebraic extensions.

Validation: focused polar, reflection-tangent, equisingularity, support geometry,
finite uniqueness and nuclear-duality builds passed. The full default
`lake build` passed (21529 jobs), followed by `lake build Challenge` (19769 jobs),
with no compiler or linter warnings.


## 2026-11-01: native orthonormal synthesis, overlap and principal cosines

Compiled the two defining correspondences before removing the local engines:
`TauCeti.familyIsometry hu = hu.synthesisMapIsometry`, and
`TauCeti.overlapOp hu hv = TauCeti.overlapOperator 𝕜 u v`.
Thus the previously scope-sensitive coordinate-overlap comparison is resolved
for these family operators. Native finite-index APIs include the donor's
`Fin d` case without changing the paper's mathematical scope.

Retired `familyMap` and its inner-product proof, `familyIsometry` and its
coordinate/single-vector proofs from `Gram/Matrix.lean`; the span/range
containment helper in `AlignedBasis.lean` is replaced by
`Orthonormal.range_synthesisMapIsometry`. All maintained callers, including
Acharyya2025 and the nested Yu–Wang–Samworth package, use the native synthesis
isometry. Approximate rigid-motion alignment remains in `Gram/Matrix`.

Retired `overlapOp`, its action/contraction/Frobenius proofs, and the duplicate
`cosPrincipalAngles`/`sinThetaSq` definitions and basic order, bounds, symmetry
and sum identities. Consumers use native overlap, principal cosines and squared
sine directly; finite sums use `Fintype.card_fin` and
`Fin.sum_univ_eq_sum_range` where necessary. Deleted the coordinate adjoint,
projection-factorization, span membership and coisometry forwarding helpers,
and the long cosine dictionary proof. The existing local-carrier cosine bridge
and rank-one statements in `AngleGeometry` now apply the accepted span and
singleton theorems directly; the finite double-angle caller does likewise.

Accepted integrations (each verified in pin `463ab293070d`):

- [#15120](https://github.com/TauCetiProject/TauCeti/pull/15120),
  `63ca9e2f2bac253526484a022e3bc0b557712c40`: canonical coordinate isometry,
  independently using native synthesis and Mathlib.
- [#13988](https://github.com/TauCetiProject/TauCeti/pull/13988),
  `6e9359613bce697ea5483673e3d46e96f4a6c881`: canonical range/adjoint extension.
  The integrated refactor removed its proposed parallel `familyIsometry` API;
  its final range proof uses Mathlib's linear-combination range machinery.
  This is not an unchanged DKPS-family implementation landing under another name.
- [#15340](https://github.com/TauCetiProject/TauCeti/pull/15340),
  `fe7e204a9aa8c36b52c6605c774166bc590b4498`: expressly independent overlap and
  principal-cosine development, not a port of DKPS.
- [#16582](https://github.com/TauCetiProject/TauCeti/pull/16582),
  `0df7c1368e4d208845ec50de86ccac8e042e31ca`: canonical span/cosine dictionary,
  singleton formula and isometric/coisometric padding. The integration uses the
  native frame factorization; no donor proof adaptation is asserted.

Historical source is `e4637c3919ae` under the three donor paths plus
`AngleGeometry.lean`. The coordinate family was introduced in `AlignedBasis`
at `75fdc44`, then moved to `Gram/Matrix` by `7295883b5`; `PrincipalAngles`
originates at `34319dc`. Original family/angle authors are Jon Crall and Claude
Opus 4.8; the surrounding Gram module credits Jon Crall and Claude Fable 5.
Kitware copyright and Apache-2.0 remain recorded. The manifest preserves the
original public declaration inventories, rather than replacing source names
with the new API names.

Importing the native frame API also exposes `TauCeti.gramOperator` for finite
families. Bounded-operator paper consumers explicitly qualify their existing
`ApproximationNumber.gramOperator`, preserving the original operator and avoiding
name shadowing; no new adapter is introduced.

The selected-polar cross-term identities remain distinct from TauCeti's
existentially chosen Procrustes family. Fin-indexed eigenblock enumeration,
projector-distance/largest-angle consequences and equal-rank sine-spectrum
arguments also remain for further comparison; this checkpoint does not claim
that every surrounding angle theorem is unmatched upstream. Explicitly adapted
native cross-block Frobenius proofs have separate provenance from #15340.

Validation: focused coordinate/angle, Yu–Wang–Samworth, finite double-angle,
Acharyya2025 and unbounded double-angle consumer builds passed. The full default
`lake build` and `lake build Challenge` passed without compiler or linter warnings.

## 2026-11-01: canonical submodule sequences and directed Frobenius sine

Retired the `TauCeti.principalCosines`, `principalSines`, `principalAngles`
and `AvoidsQuarterTurn` definitions in `AngleGeometry.lean`. Their defining
correspondences with the accepted `Submodule` APIs were compiled before
removal. All maintained papers and comparator statements now use those native
objects. Their symmetry/self proofs, the unused span/singleton forwarders and
local/native identity adapters are gone. The separate
`AvoidsQuarterTurnEmbedding` alias and its two proof-only exercises have no
maintained consumers; they retire with the old ambient predicate. The actual
trial-coordinate tangent and its Ritz-residual mathematics remain intact.

The accepted equal-rank `Submodule.principalSines_comm` also displaces the
entire complementary-Gram/polar-conjugation sine-spectrum engine in
`PrincipalAngles.lean`, including its coordinate and padding helpers. The
local `singularValues_operatorAbs` proof is replaced by the native linear-map
lemma. The projector-difference norm proof and its equal-length basis-selection
helper are replaced directly at paper callers by
`Submodule.projectionGap_eq_directedProjectionGap_of_finrank_eq`; the native
identity needs only finite-dimensional subspaces, without finite-dimensional
ambient space. The source largest-angle statement in `SharpDisplacement`
retains its original positive-dimension hypothesis and now uses native
`principalAngles_apply` and `principalSines_zero`.

Deleted the complete `SinTheta/Frobenius.lean` donor: definition,
characteristic equality and nonnegativity. All callers use
`Submodule.sinThetaFrobenius`; the old linear sine map agrees with the native
bounded map after its defining equation. The YWS complement identity and
arbitrary-spanning-family Frobenius bridge retain their paper statements with
direct native proofs. Their private ambient-basis extension construction is
retired. The rank-one Frobenius consequence uses the native spanning-family
projection formula. No forwarding donor module remains.

Accepted integrations, verified in pin `463ab293070d`:

- [#14677](https://github.com/TauCetiProject/TauCeti/pull/14677),
  `7fd5323416c03413b1fbc4c956b7bd7552b4d82c`: native principal sequences and
  equal-rank sine symmetry. The integration expressly says no prior
  formalization was followed. Its Gram-eigenspace multiplicity argument differs
  from the donor polar-unitary proof: independent replacement.
- [#16645](https://github.com/TauCetiProject/TauCeti/pull/16645),
  `3b449bc8628f565cf81e0129f4bd235e041d9f08`: quarter-turn avoidance and
  largest-sine/gap identities. Direct API consumption; no donor adaptation is
  inferred from overlapping statements.
- [#15983](https://github.com/TauCetiProject/TauCeti/pull/15983),
  `0b158be1c6578d63da36f4a1e8c585b3556e63e8`: the stronger equal-rank gap
  identity. Its direct finite-rank projection geometry replaces the local
  finite-ambient basis/singular-value symmetry route; no port lineage is claimed.
- [#16105](https://github.com/TauCetiProject/TauCeti/pull/16105),
  `c3db4e6a16cd44b70f6d21cd48ed50171f8ac588`:
  `LinearMap.singularValues_operatorAbs`. The accepted norm-invariance proof
  replaces the local Gram-equality proof; no direct adaptation claim is made.
- [#18985](https://github.com/TauCetiProject/TauCeti/pull/18985),
  `8f3309548f652e2dcad9f36c5642a1e5f4b0d2a0`: **explicitly adapted** DKPS
  Frobenius sine definition and basic API. This is direct proof/API lineage,
  distinct from independent #14677.
- [#20342](https://github.com/TauCetiProject/TauCeti/pull/20342),
  `93100a5ab2aab79794c6da85a98e8747aaa29591`: **explicitly adapted** DKPS
  cross-block and arbitrary-spanning-family Frobenius bridges. These general
  bridge lemmas replace the YWS proof support. Its population-gap theorem is
  only canonical-eigenbasis scope, so the stronger maintained arbitrary-ordered-
  eigenframe YWS theorem is not retired or weakened.

Historical donor sources are recoverable at `e4637c3919ae` under
`AngleGeometry.lean`, `PrincipalAngles.lean`, `Residual/AngleEmbedding.lean`,
`SinTheta/Frobenius.lean` and `YuWangSamworth2015/Core/Statistics.lean` in their
respective current source directories. `AngleGeometry`, `AngleEmbedding` and
YWS statistics credit Jon Crall / GPT 5.6 High; `PrincipalAngles` credits Jon
Crall / Claude Opus 4.8; Frobenius sine credits Jon Crall / GPT 5.6 Sol. The
latter and the YWS bridge were separated by
`6c7741125d3b025e7ac1ef2c13bf992711a9e1be`. All preserve Kitware copyright
and Apache-2.0. The redundant paper helper
`ComplexTraceOptimality.sin_principalAngles_eq_principalSines` is also retired
for `Submodule.sin_principalAngles`; its original Jon Crall / GPT-6 source is at
`da5b9cd731c91a893c8c04b5e1dad49ed0bb509f` under
`DavisKahan/FiniteDimensional/DirectRotation/ComplexTracePrincipalAngles.lean`.

Linear projection/angle-operator presentations and local acuteness remain for
the next representation slice; they are not classified as mathematically
unmatched merely because these consumers still use their old carrier.

Validation: focused native-sequence, Frobenius, YWS, counterexample, Ritz,
trace and Section 8 builds passed. The full default `lake build` and
`lake build Challenge` passed without compiler or linter warnings.

## 2026-11-01: native acuteness and transversality conditions

Removed `TauCeti.IsAcute` and `TauCeti.IsTransverse` from `AngleGeometry.lean`.
Compiled their correspondences before removal: the two projection-zero
conditions are exactly native `Submodule.IsAcute`, and one-sided
transversality is `Disjoint U Vᗮ`. These comparisons are RCLike-generic and
need no completeness or finite-dimensionality. All maintained paper and
comparator callers use the native predicate/property; pointwise proofs now
use native projection injectivity or disjointness explicitly.

Accepted [#16645](https://github.com/TauCetiProject/TauCeti/pull/16645),
`3b449bc8628f565cf81e0129f4bd235e041d9f08` (in pin `463ab293070d`), supplies
`Submodule.IsAcute`, `isAcute_iff_disjoint`,
`IsAcute.of_projectionGap_lt_one` and
`directedProjectionGap_lt_one_iff`. Its dimension-free gap-to-acuteness
replaces the old projection-zero/gap proofs; its finite directed-gap
characterization replaces the donor compactness/minimum-of-projection-norm
engine. Local acuteness symmetry is also retired. This records direct native
API consumption; no proof-adaptation lineage is inferred for #16645.

The literal source formulation of Definition 3.2,
`TauCeti.isAcute_iff_inf_orthogonal_eq_bot`, moves to the existing paper module
`DavisKahan/Geometry/Halmos/TwoProjections.lean`, proved directly by the native
predicate's disjointness characterization. The maintained source statement map
and full census now name `Submodule.IsAcute`; their old historical notes are
preserved. Generic infinite geometry no longer imports the old finite angle
donor just to obtain its predicate. The infinite-dimensional acute/gap-one
counterexample remains, along with the distinction between printed acuteness
and a uniform gap below one.

The trial-coordinate kernel characterization now takes native disjointness
and uses `Submodule.injOn_starProjection_iff_disjoint` with
`LinearMap.ker_eq_bot`. It retains the original omission of *both*
finite-dimensional hypotheses and does not require orthogonal projection onto
`range X`. The actual `tanThetaEmbedding = S |C|⁺`, its failure branch and
Ritz-residual identities are preserved; this predicate migration asserts no
operator equality with `Submodule.tanThetaMap`.

The finite converse/iff without a separate rank-equality parameter remains as
a short consequence of two native directed-gap characterizations. Section 8's
source dimension comparison uses Mathlib's disjoint-subspace rank bound and
orthogonal-complement dimension identity. The
infinite-dimensional approximate-annihilation lower-gap criterion remains:
it covers angles approaching `π/2` without attaining it, beyond the accepted
finite converse. Linear angle-operator presentations remain for the next slice.

Original donor source remains at
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean` and
`Residual/AngleEmbedding.lean`, Jon Crall / GPT 5.6 High, Kitware copyright,
Apache-2.0. The manifest preserves original declaration names and records
exactly which proof engine retires and which broader/source formulations remain.

Validation: focused finite, infinite, Ritz, counterexample, Section 8 and
changed audit builds passed. The full default `lake build` (21,535 jobs) and
`lake build Challenge` (19,783 jobs) passed without compiler or linter warnings.

## 2026-11-02: canonical Ky Fan sums throughout maintained consumers

Retired the finite-prefix definition `TauCeti.kyFanSum` and its
`kyFanSum_eq_sum_fin`, `kyFanSum_eq_sum_range`,
`kyFanSum_eq_linearMap_kyFanSum` and `kyFanSum_eq_kyFan` conversion aliases.
All maintained paper, donor, ideal and comparator statements now use
`LinearMap.kyFanSum A k`; the exact Fin/range correspondence is handled with
Mathlib's `Fin.sum_univ_eq_sum_range` where needed.

Accepted [#14136](https://github.com/TauCetiProject/TauCeti/pull/14136),
`d5e905c6f95e6e14eb5f36562be6cc5edb858995`, is integrated in the unchanged pin
`463ab293070d`. Its commit explicitly says no formalization was vendored or
adapted: this is independent work on the same roadmap result, not a DKPS proof
adaptation. Native `kyFanSum_min_finrank_range`/`kyFanSum_eq_nuclear`,
`kyFanSum_smul`, `norm_sum_inner_le_kyFanSum` and the Ky Fan seminorm application
law also replace `kyFanSum_eq_of_finrank_le`, `kyFanSum_real_smul` and
`sum_le_kyFanSum_of_orthonormal`. The pointwise-domination helper
`kyFanSum_le_of_singularValues_le` also retires; its paper caller sums the
pointwise comparison directly. Native monotonicity replaces the paper's
finite-index monotonicity proofs.

The donor retains four additional results: `eigenvalues_operatorAbs` is the
sorted-modulus eigenvalue identity; `sum_filter_lt_eq_sum_fin` still serves
finite-vector prefix consumers; `orthonormal_unimodular_smul` preserves an
arbitrary orthonormal family under independent unit phases; and
`sum_abs_le_kyFanSum_of_orthonormal` rephases coefficients to bound their
absolute **real parts**, used in the branch-free double-angle argument. The
native bound on the norm of a sum does not immediately give the sum of
absolute real parts; this rephasing proof remains on the native sum.

Original donor:
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/KyFan.lean`, originally
`ForMathlib.Analysis.InnerProductSpace.KyFan`, introduction `199390a`;
Jon Crall / Claude Fable 5, copyright Kitware, Inc., Apache-2.0.
Historical exploratory sources are not rewritten as current consumers.

Validation: focused donor/ideal/block-trace, branch-free double-angle, Ritz,
finite trace and source norm builds passed. Full default `lake build`
(21,535 jobs) and `lake build Challenge` (19,783 jobs) passed without compiler
or linter warnings.

## 2026-11-02: native product-map block sums and doubled spectra

Retired `UnitarilyInvariantSeminorm.orthogonalBlockSum` throughout maintained
Lean sources. The compiled carrier correspondence is exactly Mathlib's
`(A.prodMap B).withLpMap 2`, including the rectangular, scalar, subtraction
and product-unitary presentations. The local `orthogonalBlockSum_apply`,
`_smul`, `_sub`, `_comp`, `_adjoint` and `_linearIsometryEquiv` interfaces
retire; consumers use native product maps and explicit carrier changes.
No replacement local block-map definition or forwarding alias is introduced.

Accepted [#14456](https://github.com/TauCetiProject/TauCeti/pull/14456),
`13f061f3f1b1dfce3a28c5af2629c16b08b97584`, supplies
`LinearMap.adjoint_prodMap_withLpMap`,
`LinearMap.singularValues_prodMap_withLpMap_self` and
`LinearMap.kyFanSum_prodMap_withLpMap_self`. These replace the local adjoint
and doubled-block spectral/Ky Fan proofs, including arbitrary rectangular
RCLike maps and zero-dimensional spaces.

Accepted [#14451](https://github.com/TauCetiProject/TauCeti/pull/14451),
`9c78f15118d3d6dfa5db26ee032eeb0c7989686c`, supplies native unitary-orbit and
orbit-hull block stability and `UnitarilyInvariantSeminorm.map_prodMap_withLpMap_le`.
It replaces `orthogonalBlockSum_apply_le_of_kyFanSum_le`; its coupling theorem
requires neither finite dimension nor completeness. The unused local
`orthogonalBlockSum_mem_convexHull_twoSidedUnitaryOrbit` weighted-product
proof and its private real-scalar bridge retire. The
`singularValues_orthogonalBlockSum_congr` forwarding corollary also retires;
the scalar equality consumer applies native orbit stability and the accepted
orbit/singular-value equivalence directly.

Both integrations are in the unchanged pin `463ab293070d`; their integration
messages explicitly report no external formalization vendored. This records
independent implementations of the same roadmap results and transitive reuse
of accepted APIs, not DKPS proof-adaptation lineage.

Retained on the native map: the linear diagonal assembly,
symmetry/positivity and modulus compatibility, the block-subspace definition
and its projector formula, the scalar equality consequence used by finite
extremizers, and pointwise singular-value norm comparison. These additional
formulations are absent from the accepted module. The donor now imports only
the native block-sum module. The remaining trace assembly/instance consumers
explicitly import the still-local `Singular.Subspace` trace identity, rather
than obtaining it through unrelated block-map imports.

Historical source:
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/BlockSum.lean`;
split `7b732f4ca` under `RectangularUnitarilyInvariantNorm/BlockSum.lean`;
Jon Crall / Claude Fable 5, copyright Kitware, Inc., Apache-2.0. Original donor
names remain in the manifest even after their declarations are deleted.

The old real-convex-hull formulation was compiled directly from native
orbit-hull stability and `LinearMap.twoSidedUnitaryOrbitHull_eq_convexHull`
under the original restricted real scalar action, without finite dimension.
This verifies the scalar-action correspondence explicitly.

Validation: focused block, modulus/projector compatibility, source trace,
extremizer and doubled-Sylvester builds passed. Full default `lake build`
(21,535 jobs) and `lake build Challenge` (19,783 jobs) passed without compiler
or linter warnings. The obsolete local linter suppression was removed.

## 2026-11-02: native directed cross-projection maps

Retired `TauCeti.cosThetaMap`, `sinThetaMap` and `sinTwoAngleOperator` in
favor of `Submodule.cosThetaMap`, `Submodule.sinThetaMap` and
`Submodule.sinTwoAngleOperator`. Exact equalities of the old linear maps
with the native continuous maps' linear carriers were compiled before
removal over arbitrary RCLike inner-product spaces, without finite dimension
or completeness. The duplicate self-zero and defining double-angle
characterizations retire as well. Maintained finite matrix, singular-value
and UI-norm arguments use explicit `.toLinearMap`; norm and application
arguments use the native continuous maps directly. No global forwarding
map or adapter is introduced.

The accepted owners are [#14677](https://github.com/TauCetiProject/TauCeti/pull/14677),
`7fd5323416c03413b1fbc4c956b7bd7552b4d82c`, and
[#16645](https://github.com/TauCetiProject/TauCeti/pull/16645),
`3b449bc8628f565cf81e0129f4bd235e041d9f08`, in pin `463ab293070d`.
This is direct API consumption, with no inferred DKPS proof adaptation;
#14677 expressly reports no prior formalization followed.

The one-sided native double-angle map is `2 P_{Uᗮ} P_V P_U`.
The paper's separate ambient CFC `sin(2 Θ)` operator remains: this migration
does not identify those different operators. The trial-coordinate tangent
`S |C|⁺` and its Ritz-residual identities retain their scope. The ambient
projector Gram identity in `DoubleAngle/Gram.lean` remains on the native map;
the accepted rectangular isometry-block Gram identity does not directly
state that arbitrary-projector formula.

The duplicate operator-norm interval/Sylvester proof in
`SinTheta/Perturbation.lean` retires for the existing full UI-norm bound
specialized to native `UnitarilyInvariantSeminorm.opNorm`.
`RankOneSinTheta.lean` uses Mathlib's
`norm_sq_eq_add_norm_sq_starProjection` directly for the unit-vector
complement identity (pinned Mathlib `2cabef97b63d`,
`Analysis/InnerProductSpace/Projection/Basic.lean`). Its line operator-norm
formula now uses the native continuous map and omits the unused finite
ambient dimension assumption. Paper-facing theorem hypotheses are preserved.

Original directed-map donor:
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`,
previous paper home `DavisKahan/FiniteDimensional/Core/AngleGeometry.lean`,
Jon Crall / GPT 5.6 High, Kitware copyright, Apache-2.0. Original names and
source anchors stay in the manifest. The finite positive angle-operator
presentations remain for the next canonical-modulus slice, together with
additional projector/basis results; they are not classified as unmatched
merely because their callers still use linear maps.

Validation: native-map correspondence, directed Gram, rank-one, Ritz,
principal-plane, counterexample, planar sharpness, trace and YWS focused
builds passed. Full default `lake build` (21,535 jobs) and
`lake build Challenge` (19,783 jobs) passed without compiler or linter warnings.


## 2026-11-02: native positive cosine and sine operators

Retired `TauCeti.cosAngleOperator`, `TauCeti.sinAngleOperator`,
`sinAngleOperator_eq_operatorAbs`, `singularValues_projection_sub_projection`
and `uiNorm_projection_sub_eq_sinAngleOperator` from `AngleGeometry.lean`.
The finite linear-map presentations agree with native
`Submodule.cosAngleOperator` and `Submodule.sinAngleOperator` after conversion
to continuous maps; both correspondences were compiled before deletion using
`LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus`. Native completeness
requirements are discharged locally from the original finite-dimensional
hypotheses. Finite source-facing functional calculus uses the native sine
carrier; the mathematical statements of the direct-rotation and sharpness
results retain their scope.

The accepted owner is
`TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator`:

- [#17050](https://github.com/TauCetiProject/TauCeti/pull/17050), integration
  `e36963f4148ed374ed24fcac1fe1953e93b69982`, provides the definitions,
  positivity, squares, commutation, symmetry and norm results. Its integration
  message explicitly says that no external formalization was vendored.
- [#19817](https://github.com/TauCetiProject/TauCeti/pull/19817), integration
  `140f78ce562fc8b1652cc184a409bf38a70cb81f`, provides
  `Submodule.singularValues_sinAngleOperator_eq_sub_starProjection`.
  The accepted provenance explicitly credits adaptation from Kitware DKPS
  `SinTheta/Perturbation.lean`, Jon Crall and GPT-6, Apache-2.0. This is
  proof descent, unlike the independent initial angle-operator implementation.

The finite UI-norm consumers apply native singular-value invariance directly,
without a retained donor forwarding lemma. The repeated projection-commutation
proof in finite direct rotation is replaced by the native theorem; square
identities likewise use `Submodule.sinAngleOperator_sq`.

Also retired the duplicate dimension-free bounded sine definitions in
`DavisKahan/Geometry/Angle/OperatorAngleGeneric.lean` and
`DavisKahan/InfiniteDimensional/SinTheta/General.lean`, after compiling their
full-scope correspondences. The generic sine symmetry, norm, positivity,
self-adjointness and contraction wrappers disappear in favor of native APIs.
Block sums, scalar transport and the additional spectral-angle consequences
remain. Fixed-field real/complex angle constructions await their own
correspondence migration. The source full-space cosine `sqrt(1-sin² Theta)`
and ambient CFC double-angle operator are distinct from the native directed
cosine and one-sided double-angle map and are preserved.

Historical finite source:
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`, original
paper home `DavisKahan/FiniteDimensional/Core/AngleGeometry.lean`, Jon Crall /
GPT 5.6 High. Generic bounded source: `OperatorAngleGeneric.lean` at
`e4637c3919ae`, Jon Crall / Claude Opus 5, introduction `342438a66`.
The infinite-dimensional source at the same snapshot credits Jon Crall /
GPT 5.6 High; its promotion from the experimental surface is
`507ea63b55d8ae002256a4d9863415fb3e798361`. All three carry Kitware, Inc.
copyright and Apache-2.0 licensing. Earlier source-name evidence remains in
the manifest; deletion is not a claim that these authors wrote independent
upstream implementations.


## 2026-11-02: canonical finite majorization and convex descent

Retired the local `TauCeti.FiniteVector.prefixSum`, `WeaklyMajorized` and
`IsSymmetricConvex` definitions, prefix-sum algebra, weak-majorization basic
laws, coordinate-shrinking/solidness proofs and the local transfer-descent
engine. Maintained consumers use native `TauCeti.prefixSum`,
`IsWeaklyMajorizedBy` and `IsSymmetricConvex`, including source Section 8's
real/complex majorization and the Minkowski-sum gauge decomposition.
The equivalences of all three presentations were compiled first. In
particular, closure under transpositions gives closure under every
permutation by swap induction, so the predicate migration loses no scope.

Accepted owners:
[#14102](https://github.com/TauCetiProject/TauCeti/pull/14102), integration
`715fea57c28ebfd7287e23bcaf772e416a5f928f`, and
[#17175](https://github.com/TauCetiProject/TauCeti/pull/17175), integration
`1825b1a3978087c76c9c13f7c172e7433ca0376d`.
The former explicitly states independence from DKPS and bulk port #13865.
The latter moves prefix sums into
`TauCeti.Algebra.BigOperators.Finset.PartialSum` and generalizes their
additive/scalar API. This is consumption of independent accepted work,
not proof-adaptation attribution.

Also removed two copies of the finite-prefix/range-sum bridge:
`TauCeti.prefixSum_comp_val` in `SandwichMajorization.lean` and historical
`TauCeti.FiniteVector.prefixSum_comp_val` in `OperatorIdeal/Family/Schatten.lean`.
Both call `TauCeti.prefixSum_eq_sum_range` directly. The sandwich inequality
and the broader positive-exponent Schatten results remain.

The stronger MAJ-A14 result
`FiniteVector.exists_isTTransform_of_not_forall_le` remains: one swap average
preserves nonnegativity and prefix domination and strictly increases the
number of coordinates agreeing with the target. Native general descent
provides no such single-step certificate. The local `IsTTransform` records
one swap average; native `TauCeti.IsTTransform` allows a Robin Hood move
followed by an arbitrary permutation, so these relations are not identified.
The additional pointwise and total-sum consequences remain on the native
weak-majorization predicate. Finite gauge, zero-padding and rearrangement
presentations await subsequent canonical slices; they are not yet classified
as unmatched mathematics.

Historical source:
`e4637c3919ae:ForTauCeti/Analysis/Convex/Majorization.lean`, extraction
`6c958c237425ecacf403c670a15c5c65d01a59eb`, Jon Crall, GPT-5.6 Thinking,
Claude Fable 5 and Claude Opus 5. Original source homes remain in the manifest.
The two prefix/range helpers are recoverable at the same snapshot under
`ForTauCeti/Analysis/InnerProductSpace/SandwichMajorization.lean` and
`ForTauCeti/Analysis/OperatorIdeal/Family/Schatten.lean`, introductions
`8752c585f06b7c8548ec929ea41ec30f221af9f4` and
`90dceb24ddacda60c3839f316b0a0080631a64a2`; both credit Jon Crall and
Claude Opus 5. All carry Kitware, Inc. copyright and Apache-2.0 licensing.


## 2026-11-02: retire the finite-sequence symmetric-gauge bridge

Deleted `ForTauCeti/Analysis/Normed/SymmetricGauge.lean` (170 lines), including
`SymmetricGauge.ofFin`, `natPerm`, `toFiniteSymmetricGauge`, their embedding,
permutation and gauge proofs, finite majorization monotonicity and
`extend_eq_iSup_ofFin`. There are no maintained importers or declaration
consumers. No forwarding module or aliases remain.

Before deletion, compiled full correspondences identified `ofFin` with
`Finsupp.indicator (range n)` of the coordinate nnnorms and `natPerm` with
`Equiv.Perm.extendDomain Fin.equivSubtype`. The old finite gauge evaluations
agree with native `SymmetricGauge.finSeminorm`; its native symmetry proof and
`IsWeaklyMajorizedBy.apply_le` give the finite majorization law. The same
embedding equality derives the old nonnegative-real extension formula from
`extend_coe_eq_iSup_indicator`, without added antitonicity or finiteness.

Accepted integrations:
[#15917](https://github.com/TauCetiProject/TauCeti/pull/15917),
`6ff0822dc90cb2e050392623c4a504c93f52d7bd`, owns the sequence extension and
explicitly disclaims drawing on DKPS;
[#17212](https://github.com/TauCetiProject/TauCeti/pull/17212),
`5ac8d8e6560127be38a10a628fdeffeb7e871000`, adds `finSeminorm` and its symmetry
and majorization proofs by reusing the accepted finite descent. No direct
DKPS proof adaptation is claimed for that bridge.
[#18021](https://github.com/TauCetiProject/TauCeti/pull/18021),
`710e4228753cefbc3278e72292a7c21d6599a1dd`, moves the existing module unchanged
to `TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Basic`; it does not introduce
these declarations.

Historical source is `e4637c3919ae` under the deleted path, original module
introduction `18078bab944877bf757ae3cf2574f4c407bcc0cf`, finite bridge
`e79a0b5ecbb8dfb89c9327d9431dd37b3d599cee` and
`27a7623895865afe169d93e14d47f226cbd762e4`, extension-view checkpoint
`77721351e0de9fe3c3f7b37226be1412b19943ce`. The header credits Claude Opus 5,
Kitware, Inc. copyright, Apache-2.0. Earlier names and source evidence remain
in the existing extraction manifest.
