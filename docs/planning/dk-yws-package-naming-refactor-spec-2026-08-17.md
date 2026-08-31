# DK/YWS Package Naming Refactor Specification

**Purpose:** execution plan for a coding agent. This is a decision document, not a brainstorming document.

**Audit basis:** repository snapshot `d6f1efbfe648` from 2026-08-17, plus the package-boundary and paper-surface decisions made immediately afterward. Before executing, the agent should inspect `HEAD` only to confirm that the named files/declarations still exist; it should not reopen the design questions settled here.

## 1. Desired end state

The repository should make the ownership boundary obvious from names alone:

```text
TauCeti / ForTauCeti
    reusable, paper-independent foundations

DavisKahan / DavisKahan1970
    Davis--Kahan 1970 application/source formalization

YuWangSamworth2015
    Yu--Wang--Samworth 2015 application/source formalization
```

The two application packages should read like durable scholarly packages, not like traces of the campaigns that produced them.

The naming rules for this refactor are:

1. **Published source numbering wins.** YWS uses the published 2015 Biometrika numbering: Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1. Preprint numbering belongs only in provenance comments/docs.
2. **Do not repeat the package name inside the package namespace.** `YuWangSamworth2015.yuWangSamworth_*` is redundant.
3. **Do not nest another paper's namespace inside an application package.** `YuWangSamworth2015.DavisKahanTheory.*` is wrong ownership vocabulary.
4. **Development-state adjectives are not durable module names.** `Full*`, `Remaining*`, and `*Extensions` should disappear when they mean “what happened to be finished at the time.”
5. **Mathematical adjectives remain.** `FullAngle`, `Real`, `WholeSpace`, `Directed`, `BranchFree`, `Exact`, `FiniteMultiplicity`, etc. describe mathematics and should not be removed merely because they sound specialized.
6. **Presentation-facing and audit-facing theorem surfaces are the same declarations.** Do not introduce a second “pretty” theorem that hides semantics from the audit.
7. **No final compatibility facade.** Temporary aliases are acceptable only inside a dependency-ordered migration. The completed refactor deletes them, consistent with `AGENTS.md`.
8. **Historical records stay historical.** Do not rewrite `scripts/historical/**`, `dev/posthoc-prompt-analysis/**`, dated prompt/event logs, retired migration ledgers, or old commit-accounting records merely to make searches green.

## 2. Scope classification

### A. Rename now — high confidence

These are naming/ownership defects with a clear target and little mathematical ambiguity.

- YWS `DavisKahanTheory` nested namespace.
- YWS redundant `yuWangSamworth_` declaration prefixes.
- YWS preprint-era `Theorem4` / `Lemma5` filenames and declaration spellings.
- YWS `Core`, `GroundedImports`, and `CitationSurface` module vocabulary.
- DK facade/aggregate names whose words mean completion state rather than mathematical content: `FullSineTheta`, `FullPartIII`, `HeadlineGeneric`, `RemainingSourceSurface`, and accepted `*Extensions` leaves.
- DK source modules `PaperHilbertSchmidt` / `PaperOperatorNorm`, where section identity is a better durable name.

### B. Rename opportunistically in the same campaign

- YWS audit/doc filenames (`ELEGANCE_AUDIT`, `GROUNDING`, `verify_grounding.py`).
- DK `Section4FiniteSurface`, `Section9/FullExample`, `Section9/PaperNumericalResults`, and a few audit-module names.

### C. Defer — requires ownership/API analysis, not a mechanical rename

- The roughly 250 DK declarations beginning `Paper...` / `paper...`.
- The 46 DK theorem names containing `paperUINorm`.
- The broad migration of `TauCeti.DavisKahan1970.*` source declarations to top-level `DavisKahan1970.*`.
- The broad migration of `TauCeti.DavisKahan.ExactSinTheta.*` internals.
- Any declaration whose move changes whether it belongs in `ForTauCeti` versus the paper package.

The agent should **not** spend context trying to solve category C during this refactor.

### D. Keep intentionally

- Package roots `YuWangSamworth2015` and `DavisKahan1970`.
- YWS directories/modules `Symmetric`, `Rectangular`, `Appendix`, `Residual`, `Procrustes`, `SingularSubspace`, `TopEigenblock`, `ConsecutiveBlock`, `FrobeniusGram`, `RankBoundary`, `RankOne`, `SingularBlock`, `MixedGap`, `AngleIdentity`, and the sharpness modules.
- Canonical YWS paper declarations `YuWangSamworth2015.theorem2_sinTheta` and `YuWangSamworth2015.theorem2_alignedFrame`.
- YWS semantic predicates `IsEigenvectorBlock`, `PopulationBoundaryGap`, and `SourcePopulationGap`.
- DK `SineTheta/FullAngle.lean` and `FullAngleReal.lean`: “full” is mathematical here (full angle versus directed angle).
- DK `Section8/SourceSurface.lean`: this name deliberately distinguishes the low-level source facade from the downstream Frontier facade.
- DK specialization suffixes such as `_real`, `_exact`, `_wholeSpace`, `_branchFree`, etc.
- The canonical DK paper-facing/audit-facing single-angle theorem in `SineTheta/PaperSurface.lean`. Do not redesign its statement during this naming campaign.

---

# 3. Yu--Wang--Samworth 2015: exact refactor

## 3.1 Module/file moves

Perform these moves first, before declaration renames:

| Current | Target | Reason |
|---|---|---|
| `YuWangSamworth2015/YuWangSamworth2015/Core/` | `YuWangSamworth2015/YuWangSamworth2015/Theory/` | `Core` implies privileged/foundational status; this directory is application-owned supporting theory. |
| `YuWangSamworth2015/YuWangSamworth2015/GroundedImports.lean` | `YuWangSamworth2015/YuWangSamworth2015/Theory.lean` | This is the aggregate/dependency boundary for the supporting theory. `GroundedImports` is campaign jargon. |
| `YuWangSamworth2015/YuWangSamworth2015/CitationSurface.lean` | `YuWangSamworth2015/YuWangSamworth2015/PaperSurface.lean` | The declarations are the paper-facing and audit-facing public surface, not merely citation conveniences. |
| `YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem4.lean` | `YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem3.lean` | Published 2015 numbering is canonical; `Theorem4` is the 2014 preprint number. |
| `YuWangSamworth2015/YuWangSamworth2015/Appendix/Lemma5.lean` | `YuWangSamworth2015/YuWangSamworth2015/Appendix/LemmaA1.lean` | Published 2015 numbering is canonical; `Lemma5` is the preprint number. |
| `YuWangSamworth2015/ELEGANCE_AUDIT.md` | `YuWangSamworth2015/API_AUDIT.md` | “Elegance” is subjective/campaign-oriented; the document audits API factoring. |
| `YuWangSamworth2015/GROUNDING.md` | `YuWangSamworth2015/INTEGRITY_AUDIT.md` | “Grounding” is local workflow jargon; the document records required source/dependency closure and placeholder-free package integrity. |
| `YuWangSamworth2015/scripts/verify_grounding.py` | `YuWangSamworth2015/scripts/check_package_integrity.py` | The script checks required files/declarations and rejects placeholders; “package integrity” describes its actual contract. |


### Mechanical `git mv` sequence

The agent may use this sequence directly from the repository root, adjusting only if `HEAD` already contains one of the moves:

```bash
git mv YuWangSamworth2015/YuWangSamworth2015/Core   YuWangSamworth2015/YuWangSamworth2015/Theory

git mv YuWangSamworth2015/YuWangSamworth2015/GroundedImports.lean   YuWangSamworth2015/YuWangSamworth2015/Theory.lean

git mv YuWangSamworth2015/YuWangSamworth2015/CitationSurface.lean   YuWangSamworth2015/YuWangSamworth2015/PaperSurface.lean

git mv YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem4.lean   YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem3.lean

git mv YuWangSamworth2015/YuWangSamworth2015/Appendix/Lemma5.lean   YuWangSamworth2015/YuWangSamworth2015/Appendix/LemmaA1.lean

git mv YuWangSamworth2015/ELEGANCE_AUDIT.md   YuWangSamworth2015/API_AUDIT.md

git mv YuWangSamworth2015/GROUNDING.md   YuWangSamworth2015/INTEGRITY_AUDIT.md

git mv YuWangSamworth2015/scripts/verify_grounding.py   YuWangSamworth2015/scripts/check_package_integrity.py
```

After the moves, replace module imports mechanically:

```text
YuWangSamworth2015.Core.             -> YuWangSamworth2015.Theory.
YuWangSamworth2015.GroundedImports   -> YuWangSamworth2015.Theory
YuWangSamworth2015.CitationSurface   -> YuWangSamworth2015.PaperSurface
YuWangSamworth2015.Rectangular.Theorem4 -> YuWangSamworth2015.Rectangular.Theorem3
YuWangSamworth2015.Appendix.Lemma5      -> YuWangSamworth2015.Appendix.LemmaA1
```

The root `YuWangSamworth2015.lean` should import `YuWangSamworth2015.PaperSurface`.

## 3.2 Remove the nested `DavisKahanTheory` namespace

For every YWS file that currently has:

```lean
namespace YuWangSamworth2015
namespace DavisKahanTheory
```

remove the inner `namespace DavisKahanTheory` / `end DavisKahanTheory` pair. The declarations become direct members of `YuWangSamworth2015`.


The 13 inspected files carrying the nested namespace are:

```text
YuWangSamworth2015/YuWangSamworth2015/Appendix/LemmaA1.lean
YuWangSamworth2015/YuWangSamworth2015/Rectangular/FrobeniusGram.lean
YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankBoundary.lean
YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankOne.lean
YuWangSamworth2015/YuWangSamworth2015/Rectangular/SingularBlock.lean
YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem3.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/AngleIdentity.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/Corollary1.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/MiddleBlockSharpness.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/MixedGap.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/OrthogonalSharpness.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/PlanarSharpness.lean
YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem1.lean
```

**Do not replace it with `Symmetric` or `Rectangular` declaration namespaces in this pass.** The file/module tree already supplies organization, while the current canonical paper declarations live directly under `YuWangSamworth2015`. Keeping one package namespace minimizes churn and gives concise public theorem names.

Mechanical fully-qualified rewrite:

```text
YuWangSamworth2015.DavisKahanTheory.X -> YuWangSamworth2015.X
```

## 3.3 Remove redundant `yuWangSamworth_` prefixes

Rule:

```text
YuWangSamworth2015.yuWangSamworth_X -> YuWangSamworth2015.X
```

For Appendix Lemma A1 declarations, also translate the preprint number:

```text
yuWangSamworth_lemma5_X -> lemmaA1_X
```

For Theorem 3 declarations, retain `theorem3_...`; do not use the preprint's theorem 4 number.

The complete inspected mapping is below. This includes private helpers because they should not preserve redundant campaign-era prefixes either.

#### `Appendix/Lemma5.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_lemma5_columns` | `YuWangSamworth2015.lemmaA1_columns` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_lemma5_isometricColumns` | `YuWangSamworth2015.lemmaA1_isometricColumns` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_lemma5_orthonormalColumns` | `YuWangSamworth2015.lemmaA1_orthonormalColumns` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_lemma5_orthonormalRows` | `YuWangSamworth2015.lemmaA1_orthonormalRows` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_lemma5_rows` | `YuWangSamworth2015.lemmaA1_rows` | public |

#### `Core/Procrustes.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.yuWangSamworth_alignedFrame_le` | `YuWangSamworth2015.alignedFrame_le` | public |
| `YuWangSamworth2015.yuWangSamworth_alignedFrame_le_residual` | `YuWangSamworth2015.alignedFrame_le_residual` | public |
| `YuWangSamworth2015.yuWangSamworth_alignedFrame_real_le` | `YuWangSamworth2015.alignedFrame_real_le` | public |

#### `Core/Statistics.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.yuWangSamworth_alignedBasis_frame_le` | `YuWangSamworth2015.alignedBasis_frame_le` | public |
| `YuWangSamworth2015.yuWangSamworth_alignedBasis_le` | `YuWangSamworth2015.alignedBasis_le` | public |
| `YuWangSamworth2015.yuWangSamworth_alignedBasis_le_residual` | `YuWangSamworth2015.alignedBasis_le_residual` | public |
| `YuWangSamworth2015.yuWangSamworth_eigenvector_frame_le` | `YuWangSamworth2015.eigenvector_frame_le` | public |
| `YuWangSamworth2015.yuWangSamworth_eigenvector_frame_sinTheta_le` | `YuWangSamworth2015.eigenvector_frame_sinTheta_le` | public |
| `YuWangSamworth2015.yuWangSamworth_eigenvector_le` | `YuWangSamworth2015.eigenvector_le` | public |
| `YuWangSamworth2015.yuWangSamworth_eigenvector_real_le` | `YuWangSamworth2015.eigenvector_real_le` | public |
| `YuWangSamworth2015.yuWangSamworth_intervalBlock_le` | `YuWangSamworth2015.intervalBlock_le` | public |
| `YuWangSamworth2015.yuWangSamworth_sinTheta_frame_le` | `YuWangSamworth2015.sinTheta_frame_le` | public |
| `YuWangSamworth2015.yuWangSamworth_sinTheta_le` | `YuWangSamworth2015.sinTheta_le` | public |
| `YuWangSamworth2015.yuWangSamworth_sinTheta_le_residual` | `YuWangSamworth2015.sinTheta_le_residual` | public |

#### `Rectangular/RankBoundary.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_theorem3_printed_rankBoundary_refutation` | `YuWangSamworth2015.theorem3_printed_rankBoundary_refutation` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_theorem3_printed_rankBoundary_refutation_euclidean` | `YuWangSamworth2015.theorem3_printed_rankBoundary_refutation_euclidean` | public |

#### `Rectangular/RankOne.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularVector_le` | `YuWangSamworth2015.leftSingularVector_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularVector_opNormCoefficient_le` | `YuWangSamworth2015.leftSingularVector_opNormCoefficient_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularVector_le` | `YuWangSamworth2015.rightSingularVector_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularVector_opNormCoefficient_le` | `YuWangSamworth2015.rightSingularVector_opNormCoefficient_le` | public |

#### `Rectangular/SingularBlock.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularAlignedBasis_block_le` | `YuWangSamworth2015.leftSingularAlignedBasis_block_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularSubspace_block_le` | `YuWangSamworth2015.leftSingularSubspace_block_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularAlignedBasis_block_le` | `YuWangSamworth2015.rightSingularAlignedBasis_block_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_block_le` | `YuWangSamworth2015.rightSingularSubspace_block_le` | public |

#### `Rectangular/Theorem4.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_gram_alignedBasis_frame_le` | `YuWangSamworth2015.gram_alignedBasis_frame_le` | private |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_gram_alignedBasis_le` | `YuWangSamworth2015.gram_alignedBasis_le` | private |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_gram_sinTheta_frame_le` | `YuWangSamworth2015.gram_sinTheta_frame_le` | private |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_gram_sinTheta_le` | `YuWangSamworth2015.gram_sinTheta_le` | private |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularAlignedBasis_frame_le` | `YuWangSamworth2015.leftSingularAlignedBasis_frame_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularAlignedBasis_le` | `YuWangSamworth2015.leftSingularAlignedBasis_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularAlignedBasis_opNormCoefficient_le` | `YuWangSamworth2015.leftSingularAlignedBasis_opNormCoefficient_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularSubspace_frame_le` | `YuWangSamworth2015.leftSingularSubspace_frame_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularSubspace_le` | `YuWangSamworth2015.leftSingularSubspace_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_leftSingularSubspace_opNormCoefficient_le` | `YuWangSamworth2015.leftSingularSubspace_opNormCoefficient_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularAlignedBasis_frame_le` | `YuWangSamworth2015.rightSingularAlignedBasis_frame_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularAlignedBasis_le` | `YuWangSamworth2015.rightSingularAlignedBasis_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularAlignedBasis_opNormCoefficient_le` | `YuWangSamworth2015.rightSingularAlignedBasis_opNormCoefficient_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_frame_le` | `YuWangSamworth2015.rightSingularSubspace_frame_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_le` | `YuWangSamworth2015.rightSingularSubspace_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_opNormCoefficient_le` | `YuWangSamworth2015.rightSingularSubspace_opNormCoefficient_le` | public |

#### `Symmetric/AngleIdentity.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_equation4` | `YuWangSamworth2015.equation4` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_equation4_printed_counterexample` | `YuWangSamworth2015.equation4_printed_counterexample` | public |

#### `Symmetric/Corollary1.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_corollary1_real_le` | `YuWangSamworth2015.corollary1_real_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_corollary1_scalarSample` | `YuWangSamworth2015.corollary1_scalarSample` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_corollary1_sinTheta_le` | `YuWangSamworth2015.corollary1_sinTheta_le` | public |

#### `Symmetric/MiddleBlockSharpness.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_sharpness_middleBlock` | `YuWangSamworth2015.sharpness_middleBlock` | public |

#### `Symmetric/MixedGap.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_weylRecovered_le_populationGap_bound` | `YuWangSamworth2015.weylRecovered_le_populationGap_bound` | public |

#### `Symmetric/OrthogonalSharpness.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_sharpness_orthogonalBlocks` | `YuWangSamworth2015.sharpness_orthogonalBlocks` | public |

#### `Symmetric/PlanarSharpness.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_sharpness_planarRotation` | `YuWangSamworth2015.sharpness_planarRotation` | public |

#### `Symmetric/Theorem1.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_theorem1_frobenius_le` | `YuWangSamworth2015.theorem1_frobenius_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_theorem1_opNorm_le` | `YuWangSamworth2015.theorem1_opNorm_le` | public |
| `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_theorem1_uiNorm_le` | `YuWangSamworth2015.theorem1_uiNorm_le` | public |

#### `Symmetric/Theorem2.lean`

| Current declaration | Target declaration | Visibility |
|---|---|---|
| `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le` | `YuWangSamworth2015.alignedFrame_block_le` | public |
| `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le_residual` | `YuWangSamworth2015.alignedFrame_block_le_residual` | public |
| `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le` | `YuWangSamworth2015.alignedFrame_block_real_le` | public |
| `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le` | `YuWangSamworth2015.sinTheta_block_le` | public |
| `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le_residual` | `YuWangSamworth2015.sinTheta_block_le_residual` | public |

## 3.4 YWS names to leave alone

Do **not** shorten these merely for consistency:

```text
CorrespondingEigenblock
OrderedBlockBoundaryGap
IsEigenvectorBlock
PopulationBoundaryGap
SourcePopulationGap
rightSingularSubspace
leftSingularSubspace
hermitianDilation
frameComp
frameAlignMatrix
residualColumn
```

They are mathematical names rather than provenance names.

Do not rename the canonical paper theorem declarations:

```text
YuWangSamworth2015.theorem2_sinTheta
YuWangSamworth2015.theorem2_alignedFrame
```

## 3.5 YWS generated/configuration updates

Update all live references in:

- `YuWangSamworth2015/README.md`
- `YuWangSamworth2015/PROOF_OBLIGATIONS.md`
- renamed audit documents and dependency checker
- `dev/yu-wang-samworth-2015-full-source-census.json`, then regenerate the `.md`
- `formalization.yaml`
- `prose/distilled_literature/YuWangSamworth2015_statistical_davis_kahan.tex`
- `prose/distilled_literature/source_manifest.json`
- semantic-alignment configuration/scripts
- `Challenge/YuWangSamworth/**`
- `comparator/challenge-yu-wang-samworth.json`

### Existing comparator tripwire to repair

In the inspected snapshot, these already disagree:

```text
Challenge/YuWangSamworth/Leaderboard.lean
    #print axioms YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap

comparator/challenge-yu-wang-samworth.json
    TauCeti.sqrt_sum_cross_le_of_population_gap
```

Verify the current checkout. If still present, make the comparator pin match the actual application declaration before or during the rename campaign. A green default build does not detect this drift.

## 3.6 YWS completion search

At the end, this live-tree search should have no hits except explicit prose discussing historical names:

```bash
rg -n   'YuWangSamworth2015\.DavisKahanTheory|yuWangSamworth_|YuWangSamworth2015\.Core|GroundedImports|CitationSurface|Rectangular\.Theorem4|Appendix\.Lemma5'   YuWangSamworth2015 Challenge comparator scripts dev prose formalization.yaml   --glob '!scripts/historical/**'   --glob '!dev/posthoc-prompt-analysis/**'
```

Historical statements like “the 2014 preprint called this Theorem 4 / Lemma 5” should remain, but live module/declaration locators should use the new names.

---

# 4. Davis--Kahan 1970: exact high-confidence refactor

The DK tree contains much more deep implementation history than YWS. The goal here is **not** to rename everything. Fix facade/aggregate names first and leave deep mathematical implementation vocabulary for a separate ownership campaign.

## 4.1 Canonical facade/module moves

| Current | Target | Disposition | Reason |
|---|---|---|---|
| `DavisKahan/Sources/DavisKahan1970/HeadlineGeneric.lean` | `DavisKahan/Sources/DavisKahan1970/HeadlineTheorems.lean` | rename | It contains the remaining headline theorem surfaces. “Generic” is an implementation property, not the module's role. |
| `DavisKahan/Sources/DavisKahan1970/SineTheta/HeadlineGeneric.lean` | `DavisKahan/Sources/DavisKahan1970/SineTheta/GenericEngine.lean` | rename | After `PaperSurface.lean`, this is the supporting scalar-generic proof/certificate engine, not the canonical headline surface. |
| `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean` | `DavisKahan/Sources/DavisKahan1970/SineTheta/SourceAPI.lean` | rename/move | It is a source-vocabulary/API alias facade. “Full” records completion history. |
| `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean` | `DavisKahan/Sources/DavisKahan1970/SineTheta/Generalized.lean` | rename/move | The file owns generalized sine-theta source aliases. |
| `DavisKahan/Sources/DavisKahan1970/GeneralSinThetaExtensions.lean` | fold into `SineTheta/Generalized.lean`, then delete | fold/delete | It is already in the production aggregate; “optional extensions” is stale staging vocabulary. |
| `DavisKahan/Sources/DavisKahan1970/PartIII.lean` | `DavisKahan/Sources/DavisKahan1970/PartIII/FiniteSpecialization.lean` | rename/move | The current file explicitly says it is only the finite specialization. Unqualified `PartIII` should not mean the weaker specialization. |
| `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean` | `DavisKahan/Sources/DavisKahan1970/PartIII.lean` | rename into canonical slot | This is the broader source API and should own the unqualified name. Update its import of old `PartIII` to `PartIII.FiniteSpecialization`. |
| `DavisKahan/Sources/DavisKahan1970/FullPartIIIExtensions.lean` | fold into canonical `PartIII.lean`, then delete | fold/delete | Its own header says it is temporary until extensions are accepted; the production aggregate already imports it. |
| `DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean` | `DavisKahan/Frontier/SourceEndpoints.lean` | move out of production source tree | The file contains open/frontier endpoint signatures and already declares `Frontier.RemainingSourceSurface`; it should not be a production source aggregate member. |
| `DavisKahan/Sources/DavisKahan1970/Section4FiniteSurface.lean` | `DavisKahan/Sources/DavisKahan1970/Section4FiniteSpecialization.lean` | rename | Its header explicitly says this is a finite specialization, not the Section 4 completion boundary. |
| `DavisKahan/Sources/DavisKahan1970/Section9/FullExample.lean` | `DavisKahan/Sources/DavisKahan1970/Section9/Certificate.lean` | rename | The header calls it an end-to-end certificate surface; “FullExample” is completion-state vocabulary. |
| `DavisKahan/Sources/DavisKahan1970/Section9/PaperNumericalResults.lean` | `DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` | rename | The enclosing package is already the paper source package. |
| `DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean` | `DavisKahan/Sources/DavisKahan1970/Sylvester/Section5HilbertSchmidt.lean` | rename | It implements source inequality (5.1); section identity is more informative than `Paper`. |
| `DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean` | `DavisKahan/Sources/DavisKahan1970/Sylvester/Section5OperatorNorm.lean` | rename | It implements source inequality (5.2). |
| `DavisKahan/Sources/DavisKahan1970/Audits/FullPaperSineTheta.lean` | `DavisKahan/Sources/DavisKahan1970/Audits/SineThetaSourceCoverage.lean` | rename | Audit role, not completion state. |
| `DavisKahan/Sources/DavisKahan1970/Audits/GeneralSinThetaExtensions.lean` | `DavisKahan/Sources/DavisKahan1970/Audits/SineThetaNaturalInputs.lean` | rename | It audits the natural-input conveniences, no longer an “extension campaign.” |


### Mechanical DK module moves

Use `git mv` for the one-to-one moves. For the two `*Extensions` files, copy/fold the declarations into the target module first and delete the leaf only after the target builds.

```bash
git mv DavisKahan/Sources/DavisKahan1970/HeadlineGeneric.lean   DavisKahan/Sources/DavisKahan1970/HeadlineTheorems.lean

git mv DavisKahan/Sources/DavisKahan1970/SineTheta/HeadlineGeneric.lean   DavisKahan/Sources/DavisKahan1970/SineTheta/GenericEngine.lean

git mv DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean   DavisKahan/Sources/DavisKahan1970/SineTheta/SourceAPI.lean

git mv DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean   DavisKahan/Sources/DavisKahan1970/SineTheta/Generalized.lean

mkdir -p DavisKahan/Sources/DavisKahan1970/PartIII
git mv DavisKahan/Sources/DavisKahan1970/PartIII.lean   DavisKahan/Sources/DavisKahan1970/PartIII/FiniteSpecialization.lean
git mv DavisKahan/Sources/DavisKahan1970/FullPartIII.lean   DavisKahan/Sources/DavisKahan1970/PartIII.lean

git mv DavisKahan/Sources/DavisKahan1970/Section4FiniteSurface.lean   DavisKahan/Sources/DavisKahan1970/Section4FiniteSpecialization.lean

git mv DavisKahan/Sources/DavisKahan1970/Section9/FullExample.lean   DavisKahan/Sources/DavisKahan1970/Section9/Certificate.lean

git mv DavisKahan/Sources/DavisKahan1970/Section9/PaperNumericalResults.lean   DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean

git mv DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean   DavisKahan/Sources/DavisKahan1970/Sylvester/Section5HilbertSchmidt.lean

git mv DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean   DavisKahan/Sources/DavisKahan1970/Sylvester/Section5OperatorNorm.lean

git mv DavisKahan/Sources/DavisKahan1970/Audits/FullPaperSineTheta.lean   DavisKahan/Sources/DavisKahan1970/Audits/SineThetaSourceCoverage.lean

git mv DavisKahan/Sources/DavisKahan1970/Audits/GeneralSinThetaExtensions.lean   DavisKahan/Sources/DavisKahan1970/Audits/SineThetaNaturalInputs.lean
```

Move `RemainingSourceSurface.lean` separately in Phase D2 because that move changes the production/frontier ownership boundary rather than only the spelling.

### Files deliberately excluded from this pattern

Do **not** rename these just because they contain `Full` or `SourceSurface`:

```text
SineTheta/FullAngle.lean
SineTheta/FullAngleReal.lean
Section8/SourceSurface.lean
```

`FullAngle` is a mathematical distinction. `Section8/SourceSurface` is deliberately documented as a low-level source facade distinct from the downstream Frontier source facade.

## 4.2 DK declaration rename tied to the new sine paper surface

Once `SineTheta/PaperSurface.lean` is canonical, the old supporting theorem name is misleading:

```text
TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_rclike
    -> TauCeti.DavisKahan1970.sinTheta_generic_certificate
```

Reason: it is no longer the headline theorem; it is the stronger supporting certificate/proof bridge, including norm-ideal membership.

Do **not** rename the canonical theorem in `SineTheta/PaperSurface.lean` during this campaign. Its statement was deliberately optimized so the same declaration is both presentation-facing and audit-facing.

For the other three headline families in `HeadlineTheorems.lean`, rename the **module now** but leave theorem declaration spellings alone until those theorems receive the same source-readability audit as the sine theorem. This prevents a naming cleanup from accidentally conferring canonical status on a weaker finite wrapper.

## 4.3 `PaperUnitaryInvariantNorm` and the `Paper*` family

### Immediate rule

In public/paper-facing theorem signatures, use the existing clean alias:

```text
UnitaryInvariantNorm
```

rather than:

```text
PaperUnitaryInvariantNorm
```

Do **not** globally rename the underlying structure in this campaign. The inspected tree has hundreds of direct `Paper*`/`paper*` implementation references, and a global spelling change would mix naming cleanup with a deep operator-ideal API migration.

### Long-term migration, separate commit

After foundations have landed and public consumers use the clean aliases, a later API migration may make these clean names the actual declarations and remove aliases:

```text
PaperUnitaryInvariantNorm      -> UnitaryInvariantNorm
PaperSymmetricNormingFunction -> SymmetricNormingFunction
paperNuclearNorm              -> nuclearNorm
```

That later change must be dependency-ordered and should not be bundled with the package-facade refactor.

### `paper*` names that should remain for now

Keep `paper*` when it genuinely distinguishes a literal source construction or source-specific witness from reusable mathematics, for example:

```text
paperSourceDirectedAngleC
paperSourceFullAngleC
paperCounterexampleA
paperTanTwoBlockRepresentative
paperPlanarTrialMap
paperProjectorDifference
```

The prefix is meaningful there: these objects encode the paper's particular coordinate/source model.

Likewise, do not mechanically strip `paperUINorm` from the 46 deep theorem names in this pass. First make the clean norm type canonical at the public API; then decide whether those implementation theorem names still need migration.

## 4.4 DK application namespace debt — explicit defer

The inspected source tree still has roughly:

- 79 files declaring source material under `TauCeti.DavisKahan1970`, and
- 45 files declaring deep implementation material under `TauCeti.DavisKahan.ExactSinTheta`.

Architecturally, paper-facing declarations should eventually live in the application namespace `DavisKahan1970`, while reusable foundations should remain `TauCeti.*`. The new single-angle `PaperSurface` starts that direction.

**Do not perform a global namespace `sed` in this naming campaign.** A file path under `DavisKahan/Sources/DavisKahan1970` is not sufficient evidence that every declaration inside is paper-only; several files mix wrappers with reusable engines.

The later namespace migration should proceed facade-first:

1. paper/audit surfaces,
2. section-level source aliases,
3. paper-specific implementation records,
4. only then reconsider deep `ExactSinTheta` ownership.

This is an ownership refactor, not a spelling refactor.

---

# 5. Recommended execution order

The agent should use separate commits/checkpoints. Do not attempt every rename in one edit.

## Phase Y1 — YWS module tree

1. `Core/ -> Theory/`.
2. `GroundedImports.lean -> Theory.lean`.
3. `CitationSurface.lean -> PaperSurface.lean`.
4. `Theorem4.lean -> Theorem3.lean`.
5. `Lemma5.lean -> LemmaA1.lean`.
6. Update imports, package aggregate, docs, scripts, census locators.
7. Build `YuWangSamworth2015` before declaration renames.

## Phase Y2 — YWS namespaces/declarations

1. Remove nested `DavisKahanTheory` namespace blocks.
2. Apply the exact declaration table in section 3.3.
3. Update census JSON, semantic-audit references, Challenge, comparator, docs, and prose.
4. Do not leave compatibility aliases in the final state.

## Phase Y3 — YWS docs/scripts

Rename the audit docs/checker if they were not already moved in Y1, update README commands, and remove stale text claiming names are preserved because comparator configs pin them.

## Phase D1 — DK facade modules

Apply the high-confidence module moves from section 4.1, except `RemainingSourceSurface` if the Frontier ownership move needs a separate commit.

Fold accepted extension leaves into their canonical module and delete the extension leaf.

## Phase D2 — DK Frontier ownership correction

Move `RemainingSourceSurface.lean` to `DavisKahan/Frontier/SourceEndpoints.lean`, rename its inner namespace from `RemainingSourceSurface` to `SourceEndpoints`, remove it from the production source aggregate, and update frontier consumers.

## Phase D3 — DK supporting sine certificate name

Rename only:

```text
sinTheta_unbounded_intervalExterior_paperUINorm_rclike -> sinTheta_generic_certificate
```

and update the audit/census references. Leave the canonical `PaperSurface` theorem unchanged.

## Phase D4 — optional docs/audits

Rename the lower-value audit/doc files from section 4.1 and clean their prose. Stop here. Do not enter the broad `Paper*` or namespace migration.

---

# 6. Required search/update surfaces

Every live rename must search the **whole repository**, not just Lean files. At minimum inspect/update:

```text
*.lean
*.json
*.md
*.tex
*.py
*.toml
*.yaml
```

Pay special attention to:

```text
Challenge/**
comparator/*.json
dev/*source-census*.json
dev/*result-inventory*.json
formalization.yaml
scripts/render_semantic_alignment_review.py
prose/distilled_literature/source_manifest.json
papers/formalization_draft2/**
```

Do not rewrite historical-only files unless they are incorrectly presented as current instructions.

---

# 7. Validation contract for the agent

This repository has a documented rename failure mode: a green default build does not compile `Challenge`, and comparator configs store theorem names as strings.

Run these after **each declaration-rename phase**, not only at the end:

```bash
python3 scripts/check_declaration_name_drift.py
```

For the YWS comparator:

```bash
python3 scripts/check_comparator_signatures.py   --no-build comparator/challenge-yu-wang-samworth.json
```

Then explicitly build Challenge:

```bash
lake build Challenge
```

Build package targets with Lake so dependency-changing moves materialize required `.olean` files:

```bash
lake build ForTauCeti
lake build YuWangSamworth2015
lake build DavisKahan
```

After the relevant package succeeds, run the source/audit checks:

```bash
python3 YuWangSamworth2015/scripts/check_package_integrity.py
python3 scripts/check_yu_wang_samworth_source_census.py --probe
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_namespace_policy.py
```

If the YWS checker has not yet been renamed at the point it is run, use its current spelling `verify_grounding.py`.

Regenerate the semantic packets after declarations have their final names:

```bash
python3 scripts/render_semantic_alignment_review.py   --papers yws --importance headline   --output docs/semantic-alignment/yws-headline-review.md

python3 scripts/render_semantic_alignment_review.py   --papers dk --importance headline   --output docs/semantic-alignment/dk-headline-review.md
```

Final integration gate:

```bash
lake build
lake build Challenge
```

Warnings should remain errors where the package already enforces that policy; do not silence linters to make the rename pass.

---

# 8. Explicit non-goals

The agent should not spend tokens on these questions:

1. **Should YWS move back into TauCeti?** No. The application package boundary is intentional.
2. **Should the YWS source-facing theorem statements be redesigned?** No. The recent Theorem 2 surfaces are canonical for this refactor.
3. **Should the DK single-angle paper theorem be redesigned?** No. Preserve the new presentation/audit-facing theorem.
4. **Should every DK `paper*` declaration be renamed?** No.
5. **Should every source file under DK leave the `TauCeti` namespace immediately?** No. That is a later ownership migration.
6. **Should compatibility aliases remain forever to reduce churn?** No. They may be temporary inside a dependency-ordered migration, but final architecture has one canonical spelling.
7. **Should historical logs be rewritten?** No.
8. **Should `lake env lean <file>` be the main validation for module moves?** No. Use `lake build <target>` because moves change `.olean` dependencies.

---

# 9. Completion criteria

The naming campaign is complete when all of the following are true:

- YWS has no live `DavisKahanTheory` namespace.
- YWS has no live declaration beginning `yuWangSamworth_`.
- YWS uses published `Theorem3` and `LemmaA1` module/declaration numbering.
- YWS supporting theory is under `Theory`, and the public aggregate is `PaperSurface`.
- DK production imports contain no `FullSineTheta`, `FullPartIII`, `FullPartIIIExtensions`, `GeneralSinThetaExtensions`, or `RemainingSourceSurface` modules.
- DK's old single-angle supporting theorem is named as a generic certificate/engine, not as the canonical headline.
- Public DK theorem surfaces use the clean `UnitaryInvariantNorm` spelling without forcing a global underlying-type migration.
- Source census/inventory and semantic-review locators resolve to the new declaration names.
- `check_declaration_name_drift.py` passes.
- comparator preflight passes.
- `lake build YuWangSamworth2015`, `lake build DavisKahan`, `lake build Challenge`, and final `lake build` pass.
- No compatibility aliases remain solely to preserve the old names.

## Suggested commit decomposition

Use roughly these commits so failures are local and reviewable:

1. `Reorganize YuWangSamworth2015 modules`
2. `Normalize YuWangSamworth2015 declaration names`
3. `Clean YuWangSamworth2015 audit vocabulary`
4. `Normalize DavisKahan1970 source facade names`
5. `Move open DK source endpoints to Frontier`
6. `Rename the DK generic sine certificate`

Do not combine the deferred `Paper*`/namespace ownership migration with these commits.
