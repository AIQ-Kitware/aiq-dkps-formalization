# Yu--Wang--Samworth: source-version and mathematical-correction record

**Investigation date:** 23 October 2026  
**Repository revision inspected:** `1c5805c013c7c4f051c49bd3bfe5f4a484f1f4f7`  
**Status:** edition-specific comparison; **no complete later-print audit**.

This record captures the sources and precise limitations behind the paper's restrained discussion of YWS. It is working scientific evidence for editors and formalizers; keep extended version-history narrative out of the journal abstract.

## Verified source versions

| Code | Source | What was inspected | Stable access |
| --- | --- | --- | --- |
| YWS-V1 | Yu, Wang, Samworth, *A useful variant of the Davis--Kahan theorem for statisticians*, arXiv:1405.0680v1, dated 4 May 2014, 12 PDF pages | Preprint text and original numbering; Theorem 1 uses `hat(lambda)_{s-1}` and `hat(lambda)_{r+1}` endpoints (as recorded in the repo's 13 August comparison) | https://arxiv.org/pdf/1405.0680 ; https://arxiv.org/abs/1405.0680 |
| YWS-VA | Author-accepted manuscript, 2015, 9 PDF pages (UCL Discovery) | Visual pages 4 and 6: equation (4) and Theorem 3; same two problematic formulas found in the 2015 advance-access copy | https://discovery.ucl.ac.uk/id/eprint/10055409/1/DKvariant_FA.pdf |
| YWS-VP | *Biometrika* **102** (2015), 315--323, DOI 10.1093/biomet/asv008; advance-access typesetting, published 28 April 2015, 9 PDF pages numbered 1--9 | Visual pages 4 and 6, and extracted source text; still has the missing square and terminal rank convention | https://archive.ymsc.tsinghua.edu.cn/pacm_download/344/9095-Biometrika-2015-Yu-biomet_asv008.pdf ; https://doi.org/10.1093/biomet/asv008 |

**What these checks do *not* prove:** A later replacement of the journal PDF, publisher correction notice, revised printing or corrected author manuscript has **not** been located and compared exhaustively. Claims below are qualified to **YWS-VA and YWS-VP**, with V1 where specifically cited. No correction notice was found by targeted title, DOI, erratum and corrigendum searches on 23 October; negative search is not proof of absence.

Printed page number `4`/`6` of YWS-VP is PDF viewer page **4**/**6** (zero-indexed PDF pages 3/5). The accepted manuscript has the corresponding items on its printed pp. 4 and 6; other page numbering may differ from the eventual journal bound issue (pp. 315--323).

## Source findings and precise consequences

### YWS-01: equation (4), double-angle identity

YWS-VP printed p. 4 and YWS-VA p. 4 give the right-hand side with only the first power of `2 - ||vhat-v||^2`; for unit vectors it requires the **second** power:

```text
(2 <v,u>)^2 (1 - <v,u>^2)
  = (1/4) ||v-u||^2 (2 - ||v-u||^2)^2 (4 - ||v-u||^2).
```

The correction is algebraic; the error does not negate the article's main Theorem 2 population-gap inequality. Formal evidence:
`YuWangSamworth2015/YuWangSamworth2015/Symmetric/AngleIdentity.lean`,
`yuWangSamworth_equation4` and `yuWangSamworth_equation4_printed_counterexample`.
The revised manuscript gives the precise equation in `appendix_process.tex` with anchor `eq:yws-equation4-corrected`.

### YWS-02: Theorem 3, rank-boundary convention

YWS-VP printed p. 6 and YWS-VA p. 6 put `sigma^2_{rank(A)+1} = -infinity`. For `A` with rank below an ambient dimension, the Gram spectrum continues with **zero** eigenvalues through that ambient dimension. When a block ends at the rank, the printed convention can give an infinite gap and hence a false zero upper bound. The intended proof through `A^T A` uses the ambient spectrum, not a sequence terminated immediately after `rank(A)`.

Lean evidence: `YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankBoundary.lean`, `yuWangSamworth_theorem3_printed_rankBoundary_refutation`, its Euclidean two-dimensional instance, and the corrected Gram-spectrum theorem surface. The precise correction depends on whether left or right subspaces are compared and on the ambient Gram matrix; avoid replacing the rank by an unexplained `min(p,q)` in every statement.

### YWS-03: preprint-to-journal changes in Theorem 1 indexing

The repository's direct source comparison, `dev/yu-wang-samworth-2015-full-source-census.json` (primary-source audit, 13 August 2026), records that the 2014 preprint has the wrong sample indices `s-1` and `r+1` in the exterior separation. The 2015 journal corrects those **indices** to `s+1` and `r-1`. Therefore it would be wrong to say that the preprint and printed journal are identical or that *nothing* was corrected in publication. This is a verified example of a preprint discrepancy fixed in the 2015 article.

**Separate remaining issue:** YWS-VP's Theorem 1 uses the correct exterior *indices* but assigns `hat(lambda)_0=-infinity`, `hat(lambda)_{p+1}=+infinity`, which invert the endpoint conventions for exterior rays. At `r=1` or `s=p`, one exterior ray covers the whole line, forcing the separation infimum to zero and making a positive-gap hypothesis impossible. This is a boundary-applicability problem in the printed baseline Theorem 1. The Lean development's interval/exterior spectral-gap hypothesis does not use the inverted conventions. See census gap `theorem1-sample-endpoint-conventions`.

### YWS-04: Corollary 1, standalone vector normalization

YWS-VP p. 4 (continuing onto p. 5) omits an explicit hypothesis that the displayed eigenvectors `v`, `vhat` have unit norm. The theorem is introduced as the `d=1` specialization of Theorem 2, whose frame columns are orthonormal, so unit vectors are clearly intended. As a *standalone literal statement*, its vector-distance bound can fail on scaling even when the matrix perturbation is zero: choose `vhat=2v` and the same matrix. The Lean statement states the normalization and has a counterexample to the unnormalized literal reading:
`YuWangSamworth2015/YuWangSamworth2015/Symmetric/Corollary1.lean`,
`corollary1_printed_unnormalized_counterexample`. This omission should be distinguished from the separate missing square and rank-boundary convention, and from an error in the population-gap theorem itself.

### YWS-05: other differences that do not count as errors

The 2015 journal organizes its results as Theorems 1--3, Corollary 1, Lemma A1, while the 2014 arXiv version has Theorems 1, 2, 4, Corollary 3, Lemma 5. The printed sharpness example is a middle spectral block, rather than the preprint top block; the published text also adds a numerical illustration. These differences are accounted for in `dev/yu-wang-samworth-2015-full-source-census.json`; they are **not independent source defects** and must not be counted as such.

## Crosswalk to repository evidence

| Source question | Repository evidence | Review state |
| --- | --- | --- |
| Which principal YWS results have formal proofs? | `YuWangSamworth2015/YuWangSamworth2015/CitationSurface.lean`, `Symmetric/Theorem2.lean`, `Rectangular/`, `dev/yu-wang-samworth-2015-full-source-census.json` | The user/repository's recorded Lean builds establish the indicated declarations; verify any change to the specific theorem signature. |
| Are corrected-row counts equal to independent errors? | `papers/dk_formalization_journal/snapshots/census_macros.tex`, `dev/yu-wang-samworth-2015-full-source-census.json` | No. Counts classify source comparison and formalization entries, not distinct mistakes. |
| Which original texts were actually read this turn? | YWS-VP and YWS-VA viewer pages 4 and 6, plus versioned arXiv v1 opening and the source comparison already maintained in the census | Later editions and the issue-level publisher replacement PDF remain unchecked. |
| Is there a published corrigendum/erratum? | Targeted title, DOI, `erratum`/`corrigendum`/`correction` searches, 23 October 2026 | None located in this search. This is **unresolved** rather than an assertion that none exists. |

## Editorial rule and continuation

The article can state that the **inspected 2015 advance-access and author-accepted versions** contain the two checked display-level problems. The introduction and abstract should emphasize the formalized perturbation inequalities instead. Detailed source-variation evidence belongs in this document and the YWS census, with only the mathematically relevant correction formulas in the journal appendix. To settle the later-print question, obtain the present OUP issue PDF (not an abstract landing page), establish its modification/edition information, inspect equation (4), Theorem 3, Theorem 1 endpoints, and Corollary 1 against YWS-VP, and search any publisher correction history.
