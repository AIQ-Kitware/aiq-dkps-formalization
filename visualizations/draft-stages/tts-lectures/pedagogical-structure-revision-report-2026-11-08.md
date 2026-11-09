# DKPS transcript-first course: pedagogical structure revision

**Date:** 8 November 2026  
**Scope:** 150 numbered TTS drafts, `000000–149000`  
**Baseline:** the completed standalone-listening revision (`dkps-tts-standalone-overlay-2026-11-08.zip`), **not** the original pre-revision repository snapshot  
**Deliverable:** edited narration, updated style guidance and README, and a full [per-lecture disposition ledger](pedagogical-structure-by-lecture-2026-11-08.tsv)

## Outcome

All 150 lecture scripts were screened for their opening mathematical problem, ordering of sections, local conceptual context, example cues, proof transitions, and concluding result. Eighty recordings were revised; seventy were screened and left unchanged. The edits are concentrated in the spoken narration. Every display-only appendix is byte-for-byte identical to the completed standalone-revision baseline.

The [per-lecture ledger](pedagogical-structure-by-lecture-2026-11-08.tsv) records edited and unchanged recordings, section-level screening cues, and follow-up review priorities.

## Changes by problem class

- **Mathematical motivation and local setup.** Openings for the exact-versus-trial subspace problem (`107000–110000`), direct-rotation and doubled-angle theorems (`114000–116000`), and transport optimization (`130000`, `134000`) now identify the operative objects and the problem before presenting machinery. The malformed principal-plane opening in `045000` was repaired.
- **Prerequisite restoration within individual recordings.** Replaced references to other recordings with the actual ingredients: the parallelogram identity (`011000`), adjoints (`015000`), characteristic-polynomial roots (`026000`), compact Rayleigh maximizers (`051000`), singular-value min–max (`130000`), and the ordered-gap Sylvester estimate (`108000`, `129000`). Restated source/target frames and directed projection blocks where needed.
- **Proof progression and claim boundaries.** Clarified domain preservation for unbounded operators, norm ideal membership, branch selection in doubled-angle bounds (`116000`), and the difference between restricted and whole-space displacement (`124000`, `130000`, `135000`). The closing of `005000` formerly called bounded operators “linear functionals”; it now identifies the bounded-operator Banach algebra and the Neumann-series consequence.
- **Conclusions and episode independence.** Replaced endings that forecast another lecture with conclusions about the theorem actually established. Removed spelled-out lecture-number references and named episode callbacks, including “lecture seventy-two” and references to an “earlier Sylvester unit.” The course introduction `000000` remains a legitimate orientation to the collection.
- **Mathematical speech correction.** The spoken trace-norm counterexample in `134000` omitted the *outer* square root in the half-angle formula even though its appendix gave the right expression. It now says “the square root of the quantity two minus square root of two” for `2 sin(22.5°) = √(2−√2)`. The exact comparison is `4√(2−√2) > 2√2`. The square-comparison wording was also clarified. A fragmentary infinite-dimensional norm-scope sentence was repaired in `135000`.
- **General editorial policy.** Updated `visualizations/LECTURE_STYLE_RULES.md` and the TTS README with the second-pass criteria, including checks for spelled-out episode references, mathematical premise restoration, norm/branch distinction, and limits of keyword scans. Visualization and presentation work remains out of scope.

## Representative before/after comparisons

| Recording | Before | After and reason |
| --- | --- | --- |
| `005000` | “Such maps are called linear functionals” following a description of bounded operators. | “The bounded operators on a Banach space form a complete normed algebra.” Corrects an incorrect mathematical category and concludes with Neumann-series inversion. |
| `011000` | “the parallelogram identity from the inner-product lecture becomes decisive” | States the parallelogram identity in words and explains how it controls two approximate minimizers, allowing the proof to stand alone. |
| `045000` | “We have learned to compare subspaces by their principal angles., we discovered…” | Defines the role of principal angles and two-dimensional planes directly, then distinguishes finite-dimensional principal planes from the infinite-dimensional generic part. Repairs broken grammar and restores the local mathematical question. |
| `108000` | “Let E be an orthonormal frame for a trial subspace, let F zero span…” | Introduces the self-adjoint operator, its exact reducing subspace U, trial subspace V, and their three orthonormal frames *before* invoking the projected residual/Sylvester equation. |
| `116000` | “The maximal angle will stay strictly below forty-five degrees…” | Says that a doubled-sine bound does not alone choose an acute angle branch; a tangent bound requires extra spectral-selection and off-diagonal hypotheses. Removes an overstrong implication. |
| `134000` | “Two sine of twenty-two point five degrees equals the square root of two minus square root of two.” | “... equals the square root of the quantity two minus square root of two.” Corrects mathematical grouping in spoken delivery; the display-only exact formula was already correct. |
| `135000` | “For compact-angle sequences in a Hilbert space and accounts for matched crossed defects…” | Complete explanation: approximation numbers replace finite singular-value lists, while compact-angle and crossed-defect hypotheses must be retained. |

## Verification performed

1. **Narration extraction:** the repository's `extract_narration.py --check` exits successfully on all **150/150** numbered recordings after this pass.
2. **Marker boundaries:** every recording has one `BEGIN SPOKEN LECTURE` marker and one `END SPOKEN LECTURE` marker.
3. **Companion preservation:** for all 150 files, every byte after the `END SPOKEN LECTURE` marker matches the preceding standalone revision, including Lean declarations, references, and LaTeX.
4. **Episode-reference screening:** no residual matches for the selected literal patterns “previous/next/earlier/following/later lecture/lesson/episode/recording/unit” or “lecture/lesson/unit” followed by digits or the explicitly screened spelled-out number forms. Context-sensitive references were also reviewed during editing.
5. **Numerical spot check:** the half-angle value and comparison in `134000` were evaluated algebraically and numerically. This checks that corrected example, not all numerical exercises in the course.
6. **Scope control:** changed content is the 80 spoken regions, two guidance files, and the new report/ledger. No Lean files, mathematical source code, or display-only appendices were altered.

The ledger's word counts and phrase signals identify candidates for editorial review. Next checks: theorem-by-theorem source comparison and synthesized-audio listening. Visualizations and presentations are deferred.

## Remaining follow-up, after this editing pass

- **Mathematical fidelity:** compare the proof arguments systematically against the actual formalization and the original Davis–Kahan hypotheses, including distinctions between results developed within DKPS and later contributed upstream to TauCeti. This is the next substantive audit.
- **Cognitive load:** two recordings (`002000`, `003000`) exceed the ledger's 2,200-word screening threshold. Their length was not arbitrarily shortened because mathematical content must be assessed before cutting. The absence of an explicit “for example” phrase in several recordings is a weak lexical signal; `134000`, for instance, has a full concrete four-dimensional counterexample despite being flagged by that phrase scanner.
- **Additional listening review:** live or synthesized listening can later detect ambiguous pronunciation and mental bookkeeping not captured by the extractor, while retaining the current text-first editing scope. Visualizations and accompanying presentations are planned only after the lecture structure stabilizes.

## Overlay application

This overlay is **incremental**: it contains the changes made *after* the earlier standalone-listening revision. Apply that earlier ZIP first to a matching source snapshot if it has not already been applied. Inspect `git status` before extracting; `unzip -o` overwrites matching files. The included TSV gives a per-lecture disposition, with all seventy screened-but-unchanged files named explicitly.
