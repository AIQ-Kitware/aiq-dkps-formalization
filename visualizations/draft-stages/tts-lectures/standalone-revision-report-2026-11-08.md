# Standalone TTS lecture revision — completion and validation

**Revision date:** 2026-11-08  
**Input:** uploaded `aiq-dkps-formalization-source-2026-11-08T135904-5-2deee28d14f6.tar.gz` snapshot  
**Scope:** `visualizations/draft-stages/tts-lectures/000000–149000`

## Delivery summary

- **150 of 150 lecture transcripts inspected** using the original audit inventories and the spoken-region text.
- **144 lectures revised**, **6 reviewed without changes**. The exact filenames, spoken-word counts, and status are in [`standalone-revision-by-lecture-2026-11-08.tsv`](standalone-revision-by-lecture-2026-11-08.tsv).
- The Markdown title and all existing numbering and filenames were retained. `000000` gained narration markers; the other 149 marker pairs and **all 149 existing display-only appendices were preserved byte-for-byte** after the closing marker.
- **315 audit candidates disposed** in [`standalone-review-disposition-2026-11-08.tsv`](standalone-review-disposition-2026-11-08.tsv). 302 audited passages were rewritten or removed; 12 candidates were retained as valid technical uses of the word *source*; 1 was retained as a reference to a calculation within the same recording.
- The original standalone-review Markdown and TSV audits are unchanged and remain historical evidence, not the current to-do list.
- Updated [`visualizations/LECTURE_STYLE_RULES.md`](../../LECTURE_STYLE_RULES.md) and the local [`README.md`](README.md) with independent-listening standards, mathematical-example requirements, and limits of narration validation.

### Coverage by coherent review batch

| Lecture numbers | Revised | Reviewed without modification |
| --- | ---: | ---: |
| 000000–049000 | 49 | 1 |
| 050000–099000 | 46 | 4 |
| 100000–149000 | 49 | 1 |

## Editorial changes

1. Replaced references to former, later, and numbered recordings with local statements of the definitions, lemmas, and hypotheses needed for the current argument.
2. Removed or mathematically rephrased spoken remarks about source-code declarations, repository structure, formalization, and authoring history, while preserving mathematical history and theorem-scope distinctions.
3. Reworked openings and conclusions that presupposed another recording or announced a future installment; preserved useful intermediate proof transitions.
4. Supplied numerical data and domain conditions in examples that had reused setup from earlier lectures.
5. Kept the narration/appendix division intact, with a separate display-only space for exact Lean correspondence and source details.

## Before and after: representative repairs

### Lecture 020000 — redundant Parseval-frame example

**Before:** “In the last lecture we had a Parseval frame with three selected vectors in a plane.” The independent listener did not know which vectors were meant.

**After:** Defines the three vectors directly: two copies of the horizontal unit vector divided by √2, and the vertical unit vector. It gives analysis coefficients `(p/√2, p/√2, q)` for `(p,q)` and checks that their squared magnitudes sum to `p²+q²`. This establishes why the ambient synthesis–analysis composite is the identity while the coefficient-space composite is a projection.

### Lecture 025000 — defective matrix and Jordan chain

**Before:** “Let's return to the defective matrix from our previous lecture.”

**After:** States the actual matrix with rows `(2,1)` and `(0,2)`, chooses the horizontal eigenvector `v` and vertical generalized eigenvector `w`, and verifies `(A−2I)w=v` and `(A−2I)v=0` before the self-adjointness contradiction.

### Lecture 036000 — singular-value worked example

**Before:** Refers back to an operator without reproducing enough matrix data to reconstruct its Gram operator.

**After:** Explicitly sets `A(x,y)=(x+y,0,0)` and computes `A* A(x,y)=(x+y,x+y)`, giving the Gram matrix with both rows `(1,1)` so the singular values can be checked from its eigenvalues.

### Lecture 113000 — residual in a rotated Ritz line

**Before:** Reuses the two-dimensional matrix and rotated vector with abbreviated setup.

**After:** Gives `A=diag(0,5)`, exact selected axis, trial vector `e=(cos θ,sin θ)`, Ritz value `5 sin² θ`, and the residual obtained by subtracting that Ritz value times `e` from `Ae`. The norm follows as `5 sin θ cos θ` in the acute-angle range.

### Lectures 138000–140000 — free-beam computation

**Before:** Later recordings assume the free-beam domain, its affine kernel, its trial functions, and the perturbation from earlier recordings.

**After:** Restores the fourth-derivative operator on `[0,1]`, the self-adjoint free boundary conditions `u''=u'''=0` at both ends, the two-dimensional affine kernel, the complementary spectral lower bound exceeding `500`, and multiplication by `εt` with `0<ε<100`. Later calculations repeat the needed orthonormal affine trial basis and residual/gap data for independently checkable Ritz estimates.

### Endings

**Before:** A number of lectures ended by anticipating a later recording, sometimes after giving the current mathematical conclusion.

**After:** Endings emphasize the theorem established, the applicable hypotheses, or the remaining mathematical limitation without announcing another recording. Sixty endings received this targeted pass.

## Validation and status

**Completed:**

- Narration extraction: all 150 inputs pass `extract_narration.py --check` (rerun against the overlay after unpacking).
- Markers: exactly one ordered begin/end marker pair in each of the 150 lectures, including `000000`.
- Editorial scan: zero narrated references matching previous/preceding/earlier/last/next/following + lecture/lesson/episode/recording/unit, “last time”, or “next time”.
- Process scan: zero narrated occurrences of “the repository”, “the prompt”, or “proof assistant”. The remaining isolated technical uses of “source” and natural uses of “next” were not treated as errors.
- Mathematical spot checks: tested a two-dimensional Ritz residual identity and free-beam trial-frame Gram/residual identities algebraically. Other substantive changes were constrained to the uploaded mathematical exposition; no stronger replacement theorem was introduced intentionally.
- Appendix integrity: the display-only region following each original closing narration marker was compared byte-for-byte against the uploaded archive for all 149 corresponding lectures.

**Not completed / separate acceptance checks:**

- No Lean build was run, so there is **no new proof-compilation claim**.
- The 150 spoken texts were not all independently mathematically re-proved or checked against every Lean declaration. A specialist mathematical pass remains appropriate before publication.
- There was no synthesized-audio listening test. TTS diction and pacing should be evaluated with actual generated audio before releasing recordings.
- The retained historical source-versus-project provenance in appendices was preserved, not reaudited.

## Applying the ZIP overlay

Extract only into the expected repository, after inspecting local changes:

```bash
cd ~/code/aiq-dkps-formalization
git status --short
unzip -o ~/Downloads/dkps-tts-standalone-overlay-2026-11-08.zip -d .
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check visualizations/draft-stages/tts-lectures/[0-9]*-*.md
unzip -Z1 ~/Downloads/dkps-tts-standalone-overlay-2026-11-08.zip | while IFS= read -r path; do git add -- "$path"; done
git commit -m "Revise DKPS lectures for standalone listening" -m "Co-authored-by: GPT-6 <noreply@openai.com>"
```

The `unzip -o` command overwrites matching working-tree files. Inspect any concurrent edits before running it. The `git add` loop stages only files present in this overlay; inspect the staged diff before committing.
