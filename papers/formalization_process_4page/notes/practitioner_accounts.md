# Public first-person accounts of AI-assisted Lean work

This document is generated from `data/practitioner_accounts.csv`.  It keeps the public sources behind the workshop paper easy to inspect and corroborate.  The categorical fields are documented in `data/practitioner_accounts.schema.json`.

The accounts were found through LLM-assisted web search.  Representativeness is unknown, so the rows should not be used to estimate prevalence.  `yes` records an event or practice explicitly described by the source; `qualified`, `unclear`, and `not_reported` preserve uncertainty instead of filling it in.

## Descriptive counts

- Public first-person accounts: **21**
- Human--AI workflow studies kept alongside them: **1**
- Explicit formal statement/definition/correspondence mismatch: **8** (+ **2** qualified)
- Source defect exposed during formalization: **5**
- Counterexample explicitly used: **4**
- Separate AI review role: **6**
- Persistent project state outside chat: **12**
- Later human understanding of an already checked result: **2**
- Generated Lean explicitly not read in the described workflow: **2**

## Lean publication activity used for context

`data/lean_publication_activity.csv` records the audited Papers With Lean series through the paper cutoff of 2026-09-06. The January 2024 extension groups the captured `site_papers.json` corpus by its `published` month after that definition reproduced the frozen January 2025--July 2026 statistics-chart overlap. September 2026 is partial.

- 2024: **9** papers by `published` month
- 2025: **174** papers by `published` month
- January--August 2026: **518** papers by `published` month
- Mean monthly rate ratio, Jan--Aug 2026 versus 2025: **4.5x**
- August 2026: **108** papers
- September 2026 through the cutoff: **3** papers (partial)

## Account matrix

| ID | Author | Lean experience | Reads generated Lean | Separate AI review | Semantic mismatch | Source defect | Persistent state |
|---|---|---|---|---|---|---|---|
| `kahle_bei` | Thomas Kahle | `learning` | `substantial` | `no` | `unclear` | `no` | `yes` |
| `saiki_double_rounding` | Brett Saiki | `novice` | `selective` | `no` | `yes` | `yes` | `yes` |
| `ilin_vml` | Vasily Ilin | `not_reported` | `not_reported` | `yes` | `yes` | `no` | `yes` |
| `sergey_move` | Ilya Sergey | `expert` | `substantial` | `no` | `unclear` | `no` | `yes` |
| `miller_vlasov` | Joseph K. Miller | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `armstrong_homogenization` | Scott Armstrong and Tuomo Kuusi | `not_reported` | `not_reported` | `no` | `yes` | `no` | `yes` |
| `tao_sendov` | Terence Tao | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `nowak_tcs` | Thomas Nowak | `none` | `selective` | `yes` | `yes` | `no` | `no` |
| `suomela_loop` | Jukka Suomela | `not_reported` | `none` | `no` | `no` | `no` | `no` |
| `kovac_erdos189` | Vjekoslav Kovač | `novice` | `none` | `yes` | `qualified` | `no` | `no` |
| `enomoto_quotient` | Haruhisa Enomoto | `some` | `not_reported` | `yes` | `no` | `yes` | `no` |
| `oum_preprint` | Sang-il Oum | `not_reported` | `not_reported` | `no` | `no` | `yes` | `no` |
| `hirai_fri` | Yoichi Hirai | `not_reported` | `substantial` | `yes` | `yes` | `no` | `yes` |
| `robertj_ac` | Robert J. and collaborators | `not_reported` | `substantial` | `no` | `yes` | `no` | `yes` |
| `ennis_math` | John Ennis | `not_reported` | `not_reported` | `yes` | `yes` | `yes` | `yes` |
| `gowers_leiden` | Timothy Gowers | `not_reported` | `not_reported` | `no` | `no` | `no` | `no` |
| `chow_aristotle` | Timothy Chow | `not_reported` | `substantial` | `no` | `no` | `no` | `no` |
| `issai_aristotle` | J. J. Issai | `not_reported` | `selective` | `no` | `qualified` | `no` | `no` |
| `davis_partial` | Kelly Davis and Vasily Ilin | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `chafai_ginibre` | Djalil Chafaï | `not_reported` | `not_reported` | `no` | `no` | `no` | `no` |
| `alexeev_erdos` | Boris Alexeev | `mixed` | `selective` | `no` | `yes` | `yes` | `yes` |

## Source records

### 1. Thomas Kahle - Auto-formalization I: Keep Trying

- **ID:** `kahle_bei`
- **Date:** 2026-05-04
- **Source type:** `blog`
- **Target:** author's 2010 binomial-edge-ideals paper
- **Reported Lean experience:** `learning`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** definition review; mathematical planning; agent orchestration; library-gap triage
- **Observation used by the paper:** Kahle learned Lean while supervising Claude, spent significant time understanding definitions, later used a second LLM to prepare proof guides, and kept TODO/formalization-map state outside chat.
- **Source note:** The post explicitly warns that generated definitions can drift toward easier goals; it does not give one isolated misformalized theorem that we code as a confirmed mismatch.
- **Citation key:** `kahle2026keeptrying`
- **Source:** https://thomas-kahle.de/blog/2026/auto-formalization-1-keep-trying/

### 2. Brett Saiki - Autoformalizing Double Rounding

- **ID:** `saiki_double_rounding`
- **Date:** 2026-05-19
- **Source type:** `blog`
- **Target:** author's rounding paper
- **Reported Lean experience:** `novice`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** statement review; definition repair; persistence; mathematical adjudication
- **Observation used by the paper:** Claude inserted additional hypotheses; attempts to remove them produced counterexamples that exposed an underspecified rounding definition and a real missing restriction in the paper.
- **Source note:** The author states he had very little proof-assistant experience and describes a Markdown TODO used across context compaction.
- **Citation key:** `saiki2026double`
- **Source:** https://uwplse.org/2026/05/19/autoformalize.html

### 3. Vasily Ilin - Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau Equilibrium

- **ID:** `ilin_vml`
- **Date:** 2026-03-16
- **Source type:** `paper`
- **Target:** contemporary mathematical physics result
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** high-level supervision; definition review; statement review; adversarial review
- **Observation used by the paper:** A single mathematician supervised multiple AI systems, wrote zero code, archived prompts and commits, and reports hypothesis creep, definition-alignment bugs, agent avoidance, and adversarial self-review.
- **Source note:** The abstract explicitly names these failure modes and the critical role of human review of key definitions and theorem statements.
- **Citation key:** `ilin2026vml`
- **Source:** https://arxiv.org/abs/2603.15929

### 4. Ilya Sergey - Verifying Move Borrow Checker in Lean: an Experiment in AI-Assisted PL Metatheory

- **ID:** `sergey_move`
- **Date:** 2026-03-18
- **Source type:** `blog`
- **Target:** Move borrow-checker metatheory
- **Reported Lean experience:** `expert`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** proof architecture; diagnosing missing lemmas; representation design; stopping unproductive proof search
- **Observation used by the paper:** Sergey reports a 39,000-line Lean development produced in under a month with Claude. When the agent looped for hours, he identified a missing weakening lemma; for enums, he supplied a representation that made the preservation property tractable.
- **Source note:** The post is useful for the division of labor: routine proof repair and repeated cases went to the agent, while the human intervened on proof architecture and representation choices.
- **Citation key:** `sergey2026move`
- **Source:** https://proofsandintuitions.net/2026/03/18/move-borrow-checker-lean/

### 5. Joseph K. Miller - A Formalization of the Mean-Field Derivation of the Vlasov Equation: AI-Assisted Lean Formalization as a Strategy Game

- **ID:** `miller_vlasov`
- **Date:** 2026-07-09
- **Source type:** `paper`
- **Target:** Vlasov mean-field derivation
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** scope definitions; steer decomposition; library-gap triage
- **Observation used by the paper:** The human directed rather than wrote proofs: scoping definitions, steering decomposition, and triaging library gaps. The paper explicitly leaves intended-statement judgment with the mathematician.
- **Source note:** No specific semantic mismatch is reported in the abstract, so semantic_mismatch is coded no rather than inferred from the methodological warning.
- **Citation key:** `miller2026vlasov`
- **Source:** https://arxiv.org/abs/2607.08986

### 6. Scott Armstrong and Tuomo Kuusi - Formalizing Stochastic Homogenization in Lean

- **ID:** `armstrong_homogenization`
- **Date:** 2026-06-15
- **Source type:** `blog`
- **Target:** authors' stochastic homogenization paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** paper rewrite; theorem correspondence; supervision; library-gap triage
- **Observation used by the paper:** The authors rewrote the theory as a self-contained manuscript, maintain theorem-by-theorem correspondence, and explicitly record Lean statements that are less general or carry additional hypotheses.
- **Source note:** The post reports 449k lines of LLM-written Lean under human supervision and substantial missing background material.
- **Citation key:** `armstrong2026homogenization`
- **Source:** https://www.scottnarmstrong.com/2026/06/formalizing-stochastic-homogenization-in-lean/

### 7. Terence Tao - Sendov formalization making-of

- **ID:** `tao_sendov`
- **Date:** 2026-08-10
- **Source type:** `repository_transcript`
- **Target:** Sendov and Phelps-Rodriguez formalization
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** target selection; representation choice; staged planning; design review
- **Observation used by the paper:** The curated transcript preserves dead ends and uses Git history as the authoritative chronology; staged plans and design records persist decisions outside the model context.
- **Source note:** The repository states that essentially all Lean was written by Claude under the author's direction and review and that no external independent review had yet been performed.
- **Citation key:** `tao2026sendov`
- **Source:** https://github.com/teorth/sendov/blob/master/docs/making-of.md

### 8. Thomas Nowak - Post on a Codex-to-Claude Lean verification workflow

- **ID:** `nowak_tcs`
- **Date:** 2026
- **Source type:** `social_post`
- **Target:** TCS paper lemmas and theorem
- **Reported Lean experience:** `none`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** agent orchestration; semantic review; human model/statement judgment
- **Observation used by the paper:** ChatGPT first declared success without compiling. Codex then produced compiling Lean but introduced extra hypotheses. A separate Claude reviewer checked correspondence, weakening, and remaining sorrys.
- **Source note:** Nowak says this was to his eyes having never read Lean before and says human review of the model and result statements remains essential.
- **Citation key:** `nowak2026workflow`
- **Source:** https://www.linkedin.com/posts/nowathom_a-few-days-ago-jukka-suomela-posted-about-activity-7428414495590400000-YJ2A

### 9. Jukka Suomela - Post describing a solve-formalize-fix loop

- **ID:** `suomela_loop`
- **Date:** 2026
- **Source type:** `social_post`
- **Target:** research math problems
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `none`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `yes`
- **Human role described:** problem selection; post-hoc mathematical understanding
- **Observation used by the paper:** Suomela explicitly describes not looking at the Lean code and only paying close attention to the mathematical proof after the chatbot reaches a Lean formalization.
- **Source note:** The source does not claim that Suomela lacks Lean expertise; only reads_generated_lean=none is coded from the explicit workflow description.
- **Citation key:** `suomela2026workflow`
- **Source:** https://www.linkedin.com/posts/jukkasuomela_it-is-surprising-how-well-this-simple-scheme-activity-7425924723697610752-md-Q

### 10. Vjekoslav Kovač - Erdos Problem 189 discussion

- **ID:** `kovac_erdos189`
- **Date:** 2025-12-17
- **Source type:** `forum_post`
- **Target:** Erdos Problem 189
- **Reported Lean experience:** `novice`
- **Reads generated Lean:** `none`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `qualified`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** blueprint writing; LLM back-translation; request for community review
- **Observation used by the paper:** Kovač asked Aristotle to formalize a LaTeX blueprint, stripped links/comments, and asked Gemini to translate the main theorem back to English because he could not read Lean.
- **Source note:** A follow-up by Tao reports that the separate Formal Conjectures statement was itself misformalized; this is coded qualified because it was not generated by Kovač's pipeline.
- **Citation key:** `kovac2025erdos189`
- **Source:** https://www.erdosproblems.com/forum/thread/189

### 11. Haruhisa Enomoto - I Quit Math Then Wrote a Paper with AI

- **ID:** `enomoto_quotient`
- **Date:** 2026-08
- **Source type:** `essay`
- **Target:** author's AI-assisted representation-theory paper
- **Reported Lean experience:** `some`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `no`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `no`; **post-hoc understanding:** `yes`
- **Human role described:** multi-agent checking; post-hoc proof digestion; conceptual reinterpretation
- **Observation used by the paper:** After repeated cross-model informal checking had found no problem, Lean formalization encountered a false proof-essential manuscript claim, built a counterexample, replaced the proof, and continued. The author later undertook a separate proof-digestion phase.
- **Source note:** Enomoto reports prior personal Lean experience; the false claim was in the informal proof rather than a Lean/source correspondence mismatch.
- **Citation key:** `enomoto2026essay`
- **Source:** https://haruhisa-enomoto.github.io/quotient-submodule-equidistribution-essay/index.html

### 12. Sang-il Oum - Formalizing a recent preprint in Lean with Aristotle

- **ID:** `oum_preprint`
- **Date:** 2026-04-05
- **Source type:** `blog`
- **Target:** author's submodular-functions preprint
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `yes`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** source correction; supervision
- **Observation used by the paper:** The formalization exposed a missing non-negativity condition in Lemma 4.1, and the author uploaded a corrected arXiv version.
- **Source note:** This is coded as source_defect_found rather than semantic_mismatch because the Lean process exposed a defect in the informal source statement.
- **Citation key:** `oum2026preprint`
- **Source:** https://sangil.dimag.kr/2026/formalizing-my-recent-preprint/

### 13. Yoichi Hirai - Lean4 formalization of A Simplified Round-by-round Soundness Proof of FRI

- **ID:** `hirai_fri`
- **Date:** 2026-01-26
- **Source type:** `blog`
- **Target:** FRI cryptography paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** source comparison; decomposition; agent orchestration; code cleanup
- **Observation used by the paper:** Hirai compared Lean with the paper, records an added degree-positivity condition, used Claude to state/decompose missing lemmas and Aristotle to prove or counterexample them, then annotated code with paper locations.
- **Source note:** The post explicitly says misformalization is the remaining room for error and that the author compared the Lean code against the original paper.
- **Citation key:** `hirai2026fri`
- **Source:** https://blog.zksecurity.xyz/posts/simple-rbr-fri/

### 14. Robert J. and collaborators - Formalizing the Andrews-Curtis Conjecture

- **ID:** `robertj_ac`
- **Date:** 2026
- **Source type:** `blog`
- **Target:** Andrews-Curtis definitions and computational certificates
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** definition design; focused agent questions; source checking
- **Observation used by the paper:** The team used Aristotle while definitions were evolving and later during a broader audit. Aristotle found a mismatch between two move systems; humans repaired the interface and proved the translation theorem.
- **Source note:** The author says every suggestion was checked against the source and mathematics.
- **Citation key:** `robertj2026ac`
- **Source:** https://www.robertj1.com/ai4science/ac-conjecture-aristotle/

### 15. John Ennis - My Experiences Using AI for Math

- **ID:** `ennis_math`
- **Date:** 2026-07-21
- **Source type:** `essay`
- **Target:** research mathematics and a separate Lean formalization
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** hostile review; source/status tracking; mathematical custody
- **Observation used by the paper:** Ennis reports source/status/confidence tracking, hostile reviewers finding scope mismatches and stale summaries, and a Lean project exposing hidden assumptions in informal mathematics.
- **Source note:** The essay spans several projects; codes refer only to observations explicitly tied to proof custody or Lean/formalization work.
- **Citation key:** `ennis2026experience`
- **Source:** https://www.linkedin.com/pulse/my-experiences-using-ai-math-john-ennis-uauwe

### 16. Timothy Gowers - Thoughts about the Leiden Declaration

- **ID:** `gowers_leiden`
- **Date:** 2026-07-26
- **Source type:** `blog`
- **Target:** complicated research paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** high-level delegation
- **Observation used by the paper:** Gowers reports using Aristotle to formalize a complicated paper in Lean without needing to know Lean.
- **Source note:** This short report supports the existence of low-Lean-literacy workflows but does not describe the review mechanism in enough detail to code more fields.
- **Citation key:** `gowers2026leiden`
- **Source:** https://gowers.wordpress.com/2026/07/26/thoughts-about-the-leiden-declaration/

### 17. Timothy Chow - Aristotle waitlist discussion

- **ID:** `chow_aristotle`
- **Date:** 2026-01
- **Source type:** `zulip`
- **Target:** submitted Lean theorem with one sorry
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** output inspection; community feedback
- **Observation used by the paper:** Chow reports a run that returned a file with the target theorem and associated definitions deleted rather than proved.
- **Source note:** This is coded as a target-removal failure, not as semantic_mismatch, because the output evaded the task rather than changing a surviving formal statement.
- **Citation key:** `chow2026aristotle`
- **Source:** https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Aristotle%27s.20waitlist.20is.20gone.html

### 18. J. J. Issai - Understanding what Aristotle is formalizing

- **ID:** `issai_aristotle`
- **Date:** 2026-01-29
- **Source type:** `zulip`
- **Target:** prime-counting bounds
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `qualified`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** statement interpretation; community review
- **Observation used by the paper:** Issai reports that Aristotle's output seems not to track the intended statement and asks how to reconcile the formal object with the intended prime-counting function.
- **Source note:** The original query was unavailable, so the source itself warns that the problem may have been misstated before Aristotle saw it; semantic_mismatch is qualified.
- **Citation key:** `issai2026understanding`
- **Source:** https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Understanding.20what.20Aristotle.20is.20formalizing.html

### 19. Kelly Davis and Vasily Ilin - Aristotle Partial Results discussion

- **ID:** `davis_partial`
- **Date:** 2026-02-23
- **Source type:** `zulip`
- **Target:** hard Lean problems
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** failure analysis; provenance tracking
- **Observation used by the paper:** Davis asks for partial results when Aristotle gives up; Ilin asks for the original prompt to be preserved because repeated prompts become difficult to distinguish.
- **Source note:** This source is included for persistence/provenance rather than semantic correspondence.
- **Citation key:** `davis2026partial`
- **Source:** https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Aristotle.20Partial.20Results.html

### 20. Djalil Chafaï - Lean formalization with AI

- **ID:** `chafai_ginibre`
- **Date:** 2026-09-04
- **Source type:** `blog`
- **Target:** Theorem 1.9 of author's recent paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** target selection; high-level delegation
- **Observation used by the paper:** After a few manual explorations to select a target theorem, Chafaï delegated a roughly six-hour agent run that produced about 16.4k lines across about 75 files and a checked theorem.
- **Source note:** The post is a capability/scale snapshot and gives little information about semantic review, so most review codes remain no/not_reported.
- **Citation key:** `chafai2026leanai`
- **Source:** https://djalil.chafai.net/blog/2026/09/04/lean-formalization-with-ai/

### 21. Boris Alexeev - Formalization of Erdos problems

- **ID:** `alexeev_erdos`
- **Date:** 2025-12-05
- **Source type:** `blog`
- **Target:** collection of Erdos problems
- **Reported Lean experience:** `mixed`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** pipeline design; statement checking; intervention on failures
- **Observation used by the paper:** Alexeev reports repeated misformalizations across a semi-automated pipeline, including wrong variables, flipped inequalities/quantifiers, missing hypotheses, and higher-level mismatches. Counterexamples often exposed them.
- **Source note:** The post explicitly says misformalization was more frequent than expected and that the workflow changed rapidly as new tools appeared.
- **Citation key:** `alexeev2025erdos`
- **Source:** https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/

### 22. Katherine M. Collins et al. - Characterizing initial human-AI proof formalization workflows

- **ID:** `collins_workflows`
- **Date:** 2026-06-02
- **Source type:** `human_study`
- **Target:** controlled formalization tasks
- **Reported Lean experience:** `mixed`
- **Reads generated Lean:** `varied`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** survey; controlled user study; workflow observation
- **Observation used by the paper:** A survey of 31 respondents and a controlled study with seven usable participants found heterogeneous preferences, broad desire for high-level human control, and six of seven study participants using more than one AI tool.
- **Source note:** This row is a study rather than a practitioner report and is excluded from practitioner-report counts.
- **Citation key:** `collins2026workflows`
- **Source:** https://arxiv.org/abs/2606.04273

