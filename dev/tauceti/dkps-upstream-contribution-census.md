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
