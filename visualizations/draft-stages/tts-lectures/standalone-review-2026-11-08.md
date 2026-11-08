# TTS lecture standalone-narration review — 2026-11-08

## Scope and decision

Reviewed the **150 Markdown drafts `000000`–`149000`** in the supplied `aiq-dkps-formalization-source-2026-11-08T132755-5-7ff46e7550da.tar.gz` snapshot, focusing on what a listener hears. This is an **editorial review only**: the transcript files are unchanged. A separate tab-separated candidate ledger accompanies this review so later editing can proceed lecture by lecture, without a generic global rewrite.

**Decision: revision is warranted before treating these recordings as independently listenable.** Many arguments are intelligible when heard consecutively, but the scripts repeatedly invoke earlier episodes, use next-episode teasers, and sometimes discuss the project formalization instead of presenting the mathematical statement. These can largely be repaired locally while retaining the mathematical content and source fidelity.

### Audit inventory

| Check | Finding | Interpretation |
| --- | --- | --- |
| Files present | 150 of 150 (`000000`–`149000`) | Complete numbered draft set in this snapshot |
| Explicit earlier/later lecture wording | **204 candidate lines in 120 lectures** | Strong editorial finding. Includes a few context-dependent phrases such as “the next time you encounter”; review before replacing |
| Lean, repository, or formalization context in speech | **64 candidate lines in 46 lectures** | Many should move to the display-only appendix, though course orientation may legitimately mention formalization |
| “The source” speaking as editorial authority | **34 candidate lines in 30 lectures** | Often interrupts mathematical exposition; use a named theorem and its hypotheses instead. These counts overlap with the previous category |
| Sequence-dependent openings not caught above | **12 candidate lines in 12 lectures** | “So far,” “we have learned,” and similar framing. Some are fine as recaps if stated independently |
| Literal prompt/production phrases | **0 matches** for the audited phrase list | No direct “the prompt says,” “as requested,” “TTS instructions,” etc. detected. This does not prove the absence of every unnatural phrase |
| Narration extractor | 149 of 150 files pass | `000000` has no spoken-region markers and is rejected by the ordinary extractor; intentional conceptual exemption from a Lean appendix does not imply extraction exemption |

The counts are **candidate occurrences**, not 204 independently confirmed substantive defects. The ledger contains matched text and exact line numbers, permitting contextual triage. Automated text matching cannot determine whether a definition is adequately taught, whether a proof is valid, or whether the synthesized voice sounds natural. Those need editorial and mathematical reading, and eventually listening.

## Findings and representative corrections

### 1. Do not identify the episode before or after this one

The principal defect is chronology in speech, not the reuse of established mathematics. The script should work when played by itself or out of order.

- **`003000`, line 6:** Opens “In the previous lesson, we used a norm…” The replacement should define induced distance in one sentence, then introduce Cauchy sequences. It need not repeat the previous lecture's proof.
- **`016000`, line 5:** Opens with “In the last lecture…” Replace with the mathematical premise: a reducing subspace and its orthogonal complement yield an operator block decomposition.
- **`112000`, line 9:** Opens “The preceding lecture described a trial subspace as the graph…” Start instead by defining a graph subspace and explaining why its slope measures tangent angles.
- **`136000`, opening:** “Our last lectures compared…” is unnecessary to the classification problem. State the classification question directly.
- **`149000`, opening:** “This is the course's final proof practicum” is harmless as course orientation but fails the strict independent-listening test. “We will reconstruct the Davis–Kahan perturbation argument from its assumptions” is sufficient.
- **`001000`, line 116; `017000`, closing; `123000`, closing:** Replace next-lecture announcements with an intrinsic takeaway, an application, or a well-defined question the current lesson has equipped a listener to pursue.

**Allowed:** “The spectral theorem states …” with the setting and relevant conclusion; “Recall that an orthogonal projection is self-adjoint and idempotent.” **Disallowed:** “As we proved three lectures ago …” or “We will prove that next time.” Ordinary transitions between sections *within the same recording* are fine.

### 2. Self-contained recaps require the actual data, not a pointer to an old example

Some lecture references carry needed numerical or geometric inputs. Removing “last lecture” alone is insufficient.

- **`020000`, around line 97:** Reuses a three-vector Parseval frame from the preceding lecture. Restate its vectors and what makes it Parseval, or introduce a self-contained new example.
- **`025000`, around line 65:** Invokes the previously seen defective matrix. Give its explicit two-by-two entries or define the Jordan-chain relation in the present lesson before exploiting it.
- **`027000`, line 27:** The two-by-two symmetric matrix is described and can be recomputed locally, but “we know from the previous lecture” should become a quick eigenvalue calculation.
- **`036000`, around line 68:** Reuses a previously computed Gram matrix. Give the underlying map and show one calculation so the matrix is justified locally.
- **`113000`, around line 38:** References an already calculated Ritz residual. Recalculate the two-dimensional residual where it is used, rather than relying on the previous recording.
- **`138000–140000` beam case study:** The numerical model spans several lectures. Each recording should state the beam operator, trial subspace, perturbation parameter, essential gap and the numerical quantities needed for *that recording* before comparing estimates. It should not repeat the full differential-operator derivation every time.
- **`145000`, opening:** The four-dimensional counterexample is introduced as previously learned. Restate the conclusion and the relevant objective (unsquared ambient Schatten displacement) before motivating matching.

For mathematical prerequisites, short local statements are enough when the omitted proof is standard or lengthy: give the exact lemma, hypotheses, and role. The standalone requirement does **not** demand re-proving the finite spectral theorem in every subsequent lecture.

### 3. Keep implementation provenance out of ordinary mathematical narration

The display-only appendix is already the designated place for declaration names, source locations, imports, donor lineage, and formal proof scope. Spoken math needs the **mathematical** scope, but does not generally need to mention how the repository encodes it.

- **`007000`, line 80:** “A Lean type for a real-linear map…” should become a mathematical explanation that real linearity does not imply complex linearity; put the Lean type distinction in the appendix.
- **`016000`, line 66:** “In the DKPS Lean development, the diagonal operation is called pinch.” Define block pinching mathematically without citing the implementation.
- **`067000`, line 96:** “The specific Lean theorem used in our appendix…” should state directly that a circle-contour argument requires a separating circle; the broader disjoint-spectra case needs an appropriate contour.
- **`096000`, line 22:** Zero-based indexing of Lean singular values belongs in the appendix. The spoken proof can choose one-based indexing and keep it consistent.
- **`117000`, line 28; `127000`, around lines 76–78:** Replace discussion of what “the formalization” or “Lean” proves with exact theorem statements and their mathematical domain of validity; preserve the distinctions among rank and norm hypotheses.
- **`145000`, lines 34, 58, 68:** The involution model and global minimization are valuable mathematics. Explain fixed points, pairs, and attainment directly; relocate the Lean encoding and a heading about “what the Lean result actually says” to the appendix.
- **`147000`, line 82:** A source-correction remark can be appropriate when it concerns a *printed mathematical identity*, but state the erroneous formula and corrected identity (or make it a display-only note). “The repository's grounding audit identifies…” is an internal-process reference.

Mentioning Davis, Kahan, Yu, Wang, Samworth, or a numbered theorem as genuine **mathematical attribution** is fine. This rule is about unnecessary authoring/tool commentary, not the removal of history or precise hypotheses.

### 4. Make openings, transitions, and conclusions independent

Across the set, openings often start with “Last time,” “So far,” or “We have now learned”; endings often advertise the next topic. The mathematical narratives generally contain a proper object, a construction, and a result, so the repair is usually to change the first and last paragraphs rather than rewrite the proof.

Use this local pattern, without making it a rigid template:

1. Name one mathematical problem and its setting.
2. Give any required definitions or theorem premises in the current recording.
3. Present the argument, showing why each step is useful.
4. Work through a numerical or geometric example when it clarifies a mechanism.
5. Finish with what is now established, when the claim holds, and one optional self-contained reconstruction question.

A recap is useful if it states a fact. Avoid “we have seen this before” without restating the fact. Avoid repeatedly presenting the course's full intellectual itinerary in the middle of a focused topic.

### 5. Spoken notation and section labels

Most scripts use spoken-English mathematics. The marker extractor strips Markdown heading markers but does **not** review the semantics or pronounceability of technical names. For example, `111000` includes a literal `P_{U perpendicular}` in the spoken portion (around line 58), which reads like source notation rather than a phrase. Prefer “the projection onto U perpendicular” in speech and put the exact notation in the appendix.

The scripts can use small verbal formulas (“A adjoint times A”), but long typeclass or source declarations should remain outside the spoken region. Exercise prompts should test the mathematical idea directly; “before the next lecture, try…” needs only the temporal phrase removed.

## Priority editing queue

This is an **editing order**, not a recommendation to alter the mathematical content automatically.

| Priority | Targets | Action |
| --- | --- | --- |
| P1 | All 120 lectures with explicit sequence references | Remove former/next-episode language; repair any referenced example or lemma locally. The attached TSV lists exact lines. |
| P1 | `020000`, `025000`, `036000`, `113000`, `138000`–`140000`, `145000` | Reconstruct reused example data before the explanation relies on it. |
| P1 | `007000`, `016000`, `042000`, `067000`, `096000`, `117000`, `127000`, `145000`, `147000` | Remove Lean/source-audit commentary from spoken mathematics while retaining scope in narration and provenance in appendices. |
| P2 | Other 46 lectures flagged for Lean/repository vocabulary; 30 flagged for source-editorial language | Judge context and replace narration-first; don't replace the historical paper or mathematical attribution. |
| P2 | `000000` | Add speech markers around the course introduction so the normal extractor accepts it; leave the introduction's conceptual-only Lean exemption intact. |
| P3 | All 150 after targeted revision | Human listen-through for cadence, jargon, ambiguous spoken variables, and excessive repetition. Then independent proof-scope spot checks. |

The source snapshot is a self-consistent editorial basis, but no modifications to the 150 lecture files were made in this review. The `candidate-lines` TSV contains **315 category-tagged candidate findings**, possibly multiple categories on one source line; its tags are not verdicts. The `per-lecture` TSV gives a complete 150-row inventory, including lectures without flags. Existing mathematical correctness and Lean typechecking were **not** re-verified by this editorial audit.

## Acceptance criteria for revisions

A revised script passes the independence test if a listener can start at the title with no earlier recording and still identify the objects, assumptions, question, proof strategy and conclusion. Background results may be quoted by name with their relevant statement. No sentence should refer to a different episode or to work the listener is supposed to have just heard elsewhere. All worked examples must supply their inputs in the present script. The main narration should read as a mathematical lecture rather than a description of how a course, repository, or proof assistant was assembled. Historical attributions and exact theorem limitations remain intact. The display-only Lean companion stays available to readers who want the formal correspondence.

This should be checked by reading the extracted spoken text **without** its preamble, prerequisites, sequel metadata, or Lean appendix; those support editors, not an independent listener. A final synthesized-audio pass is necessary to assess pronunciation and cadence.
