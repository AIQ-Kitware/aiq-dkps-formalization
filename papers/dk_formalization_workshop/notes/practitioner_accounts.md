# Public first-person project accounts of AI-assisted Lean work

This document is generated from `data/practitioner_accounts.csv`, `data/practitioner_account_sources.csv`, and `data/practitioner_account_screening.csv`. The account table is one row per project/workflow episode; URLs are separate source records so follow-up evidence does not inflate the account denominator. The categorical fields are documented in the corresponding schema files.

The accounts were found through LLM-assisted web search. Representativeness is unknown, so the rows should not be used to estimate prevalence. `yes` records an event or practice explicitly described by the source; `qualified`, `unclear`, and `not_reported` preserve uncertainty instead of filling it in.

`practitioner_cluster` records overlap between project accounts when a practitioner appears more than once; it is an overlap component, not a count of unique people. `project_cluster` can group multiple workflow episodes from one project. Primary, supplemental, and corroborating sources are kept separately.

The screening log was introduced on 2026-09-08. It records the preexisting included snapshot and candidates reviewed during the current expansion; it does not reconstruct every source encountered in earlier searches and should not be read as an exhaustive search record.

## Descriptive counts

- Public first-person project/workflow accounts: **42**
- Practitioner-overlap clusters: **40**
- Public source records attached to practitioner accounts: **47**
- Supplemental/corroborating source records: **5**
- Human--AI workflow studies kept alongside them: **1**
- Explicit formal statement/definition/correspondence mismatch: **14** (+ **3** qualified)
- Source defect exposed during formalization: **8**
- Counterexample explicitly used: **8**
- Separate AI review role: **9**
- Persistent project state outside chat: **28**
- Later human understanding of an already checked result: **3**
- Generated Lean explicitly not read in the described workflow: **3**

## Screening log

- Candidates recorded: **54**
- Included project accounts: **42**
- Supplemental/corroborating sources: **5**
- Structured studies: **2**
- Related-work-only sources: **2**
- Holds awaiting stronger first-person evidence: **3**
- True duplicates: **0**
- Excluded: **0**

| Candidate | Decision | Account | Discovery route | Reason |
|---|---|---|---|---|
| `kahle_bei` | `include_account` | `kahle_bei` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `saiki_double_rounding` | `include_account` | `saiki_double_rounding` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `ilin_vml` | `include_account` | `ilin_vml` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `sergey_move` | `include_account` | `sergey_move` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `miller_vlasov` | `include_account` | `miller_vlasov` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `armstrong_homogenization` | `include_account` | `armstrong_homogenization` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `tao_sendov` | `include_account` | `tao_sendov` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `nowak_tcs` | `include_account` | `nowak_tcs` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `suomela_loop` | `include_account` | `suomela_loop` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `kovac_erdos189` | `include_account` | `kovac_erdos189` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `enomoto_quotient` | `include_account` | `enomoto_quotient` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `oum_preprint` | `include_account` | `oum_preprint` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `hirai_fri` | `include_account` | `hirai_fri` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `robertj_ac` | `include_account` | `robertj_ac` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `ennis_math` | `include_account` | `ennis_math` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `gowers_leiden` | `include_account` | `gowers_leiden` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `chow_aristotle` | `include_account` | `chow_aristotle` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `issai_aristotle` | `include_account` | `issai_aristotle` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `davis_partial` | `include_account` | `davis_partial` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `chafai_ginibre` | `include_account` | `chafai_ginibre` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `alexeev_erdos` | `include_account` | `alexeev_erdos` | `preexisting_snapshot` | Public first-person account already present in the pre-expansion paper snapshot. |
| `deng_shum_probability` | `include_account` | `deng_shum_probability` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `dedios_banach_phase` | `include_account` | `dedios_banach_phase` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `chen_huang_ripple` | `include_account` | `chen_huang_ripple` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `swaminathan_quartic` | `include_account` | `swaminathan_quartic` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `lau_grasshopper` | `include_account` | `lau_grasshopper` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `freer_definetti` | `include_account` | `freer_definetti` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `zhang_slt` | `include_account` | `zhang_slt` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `cook_partial_fractions` | `include_account` | `cook_partial_fractions` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `douglas_qft` | `include_account` | `douglas_qft` | `web_search_2026-09-08` | Public first-person account with source-grounded observations relevant to AI-assisted Lean practice; added in the 8 September search. |
| `treleaven_pile_shuffle` | `include_account` | `treleaven_pile_shuffle` | `web_search_2026-09-08` | Public first-person account with source-grounded observations on novice use, proof readability, and human supervision. |
| `collins_workflows` | `structured_study` | `collins_workflows` | `preexisting_snapshot` | Structured human--AI workflow study retained alongside the first-person accounts but excluded from the practitioner-account count. |
| `ilin_nugent_sorries` | `structured_study` | `` | `web_search_2026-09-08` | Purpose-designed before/after expert-review case study. It is cited as related evidence rather than counted as an ordinary practitioner account. |
| `paglieri_swarm` | `related_work` | `` | `user_suggested_2026-09-08` | Controlled multi-agent experiment about verifier and specification gaming, not a first-person practitioner account. |
| `garg_econcs` | `related_work` | `` | `preexisting_related_work` | Methodology and system paper already cited as adjacent work; kept outside the first-person account count. |
| `munozlahoz_banach_library` | `supplemental_source` | `dedios_banach_phase` | `citation_chain_2026-09-08` | Companion paper from the same Banach-lattice project; retained as corroborating evidence for the existing project account rather than counted as a new account. |
| `yadav_gpu_verification` | `include_account` | `yadav_gpu_verification` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `warren_tessera` | `include_account` | `warren_tessera` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `zaliva_bc_semantics` | `include_account` | `zaliva_bc_semantics` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `vergo_chebyshev` | `include_account` | `vergo_chebyshev` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `bernier_class_field` | `include_account` | `bernier_class_field` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `schmitt_extremal_descendants` | `include_account` | `schmitt_extremal_descendants` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `schildep_polygon` | `include_account` | `schildep_polygon` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `davis_gradient_descent` | `include_account` | `davis_gradient_descent` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `paik_optimization` | `include_account` | `paik_optimization` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `armstrong_kempe_degiorgi` | `include_account` | `armstrong_kempe_degiorgi` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `aslyan_priority_methods` | `include_account` | `aslyan_priority_methods` | `targeted_citation_chain_2026-09-08` | First-person project/workflow account with source-grounded evidence relevant to supervision, semantic checking, provenance, or human review boundaries. |
| `kahle_bei_followup` | `supplemental_source` | `kahle_bei` | `targeted_citation_chain_2026-09-08` | Adds workflow or review evidence to an existing project account without changing the project-account denominator. |
| `nowak_tcs_eatcs` | `supplemental_source` | `nowak_tcs` | `targeted_citation_chain_2026-09-08` | Adds workflow or review evidence to an existing project account without changing the project-account denominator. |
| `freer_lean_skill` | `supplemental_source` | `freer_definetti` | `targeted_citation_chain_2026-09-08` | Adds workflow or review evidence to an existing project account without changing the project-account denominator. |
| `aslyan_sacks_followup` | `supplemental_source` | `aslyan_priority_methods` | `targeted_citation_chain_2026-09-08` | Adds workflow or review evidence to an existing project account without changing the project-account denominator. |
| `peters_socialchoicelean` | `hold` | `` | `targeted_citation_chain_2026-09-08` | Substantial public AI-assisted artifact, but the current first-person material gives less detail about supervision and semantic checking than required for account coding. |
| `luccioli_erdos_reports` | `hold` | `` | `targeted_citation_chain_2026-09-08` | Useful first-person Aristotle completion and performance reports, but current sources are too status-oriented to support the detailed workflow fields used by this survey. |
| `dvorak_littlewood` | `hold` | `` | `targeted_citation_chain_2026-09-08` | Substantial Claude/Codex/Aristotle-assisted artifact, but a richer first-person source is needed before coding the project workflow. |

## Lean publication activity used for context

`data/lean_publication_activity.csv` records the audited Papers With Lean series through the paper cutoff of 2026-09-06. The January 2024 extension groups the captured `site_papers.json` corpus by its `published` month after that definition reproduced the frozen January 2025--July 2026 statistics-chart overlap. September 2026 is partial.

- 2024: **9** papers by `published` month
- 2025: **174** papers by `published` month
- January--August 2026: **518** papers by `published` month
- Mean monthly rate ratio, Jan--Aug 2026 versus 2025: **4.5x**
- August 2026: **108** papers
- September 2026 through the cutoff: **3** papers (partial)

## Account matrix

| Account | Practitioner cluster | Author | Lean experience | Reads generated Lean | Separate AI review | Semantic mismatch | Source defect | Persistent state |
|---|---|---|---|---|---|---|---|---|
| `kahle_bei` | `kahle_bei` | Thomas Kahle | `learning` | `substantial` | `no` | `unclear` | `no` | `yes` |
| `saiki_double_rounding` | `saiki_double_rounding` | Brett Saiki | `novice` | `selective` | `no` | `yes` | `yes` | `yes` |
| `ilin_vml` | `vasily_ilin` | Vasily Ilin | `not_reported` | `not_reported` | `yes` | `yes` | `no` | `yes` |
| `sergey_move` | `sergey_move` | Ilya Sergey | `expert` | `substantial` | `no` | `unclear` | `no` | `yes` |
| `miller_vlasov` | `miller_vlasov` | Joseph K. Miller | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `armstrong_homogenization` | `scott_armstrong` | Scott Armstrong and Tuomo Kuusi | `not_reported` | `not_reported` | `no` | `yes` | `no` | `yes` |
| `tao_sendov` | `tao_sendov` | Terence Tao | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `nowak_tcs` | `nowak_tcs` | Thomas Nowak | `none` | `selective` | `yes` | `yes` | `no` | `no` |
| `suomela_loop` | `suomela_loop` | Jukka Suomela | `not_reported` | `none` | `no` | `no` | `no` | `no` |
| `kovac_erdos189` | `kovac_erdos189` | Vjekoslav Kovač | `novice` | `none` | `yes` | `qualified` | `no` | `no` |
| `enomoto_quotient` | `enomoto_quotient` | Haruhisa Enomoto | `some` | `not_reported` | `yes` | `no` | `yes` | `no` |
| `oum_preprint` | `oum_preprint` | Sang-il Oum | `not_reported` | `not_reported` | `no` | `no` | `yes` | `no` |
| `hirai_fri` | `hirai_fri` | Yoichi Hirai | `not_reported` | `substantial` | `yes` | `yes` | `no` | `yes` |
| `robertj_ac` | `robertj_ac` | Robert J. and collaborators | `not_reported` | `substantial` | `no` | `yes` | `no` | `yes` |
| `ennis_math` | `ennis_math` | John Ennis | `not_reported` | `not_reported` | `yes` | `yes` | `yes` | `yes` |
| `gowers_leiden` | `gowers_leiden` | Timothy Gowers | `not_reported` | `not_reported` | `no` | `no` | `no` | `no` |
| `chow_aristotle` | `chow_aristotle` | Timothy Chow | `not_reported` | `substantial` | `no` | `no` | `no` | `no` |
| `issai_aristotle` | `issai_aristotle` | J. J. Issai | `not_reported` | `selective` | `no` | `qualified` | `no` | `no` |
| `davis_partial` | `vasily_ilin` | Kelly Davis and Vasily Ilin | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `chafai_ginibre` | `chafai_ginibre` | Djalil Chafaï | `not_reported` | `not_reported` | `no` | `no` | `no` | `no` |
| `alexeev_erdos` | `alexeev_erdos` | Boris Alexeev | `mixed` | `selective` | `no` | `yes` | `yes` | `yes` |
| `deng_shum_probability` | `deng_shum_probability` | Shuo Deng and Kenneth W. Shum | `not_reported` | `selective` | `unclear` | `yes` | `yes` | `yes` |
| `dedios_banach_phase` | `dedios_banach_phase` | Jaume de Dios Pont, Lukas Liehr, David Muñoz-Lahoz, Mitchell A. Taylor, and Pedro Tradacete | `mixed` | `selective` | `unclear` | `qualified` | `no` | `unclear` |
| `chen_huang_ripple` | `chen_huang_ripple` | Ho-Lin Chen and Xiang Huang | `not_reported` | `not_reported` | `yes` | `no` | `yes` | `yes` |
| `swaminathan_quartic` | `swaminathan_quartic` | Ashvin Swaminathan | `not_reported` | `selective` | `no` | `no` | `yes` | `yes` |
| `lau_grasshopper` | `lau_grasshopper` | Gabriel Rongyang Lau | `not_reported` | `substantial` | `no` | `no` | `no` | `yes` |
| `freer_definetti` | `freer_definetti` | Cameron Freer | `not_reported` | `not_reported` | `no` | `no` | `no` | `yes` |
| `zhang_slt` | `zhang_slt` | Yuanhe Zhang, Jason D. Lee, and Fanghui Liu | `not_reported` | `selective` | `no` | `yes` | `unclear` | `yes` |
| `cook_partial_fractions` | `cook_partial_fractions` | John D. Cook | `not_reported` | `selective` | `no` | `no` | `no` | `no` |
| `douglas_qft` | `douglas_qft` | Michael R. Douglas, Sarah Hoback, Anna Mei, and Ron Nissim | `not_reported` | `selective` | `yes` | `yes` | `no` | `yes` |
| `treleaven_pile_shuffle` | `treleaven_pile_shuffle` | Kyle Treleaven | `none` | `none` | `no` | `no` | `no` | `yes` |
| `yadav_gpu_verification` | `rohan_yadav` | Rohan Yadav | `some` | `selective` | `no` | `yes` | `no` | `unclear` |
| `warren_tessera` | `john_p_warren` | John P. Warren | `not_reported` | `not_reported` | `no` | `yes` | `no` | `yes` |
| `zaliva_bc_semantics` | `leonid_zaliva` | Leonid Zaliva | `not_reported` | `selective` | `yes` | `yes` | `no` | `yes` |
| `vergo_chebyshev` | `eric_vergo` | Eric Vergo | `learning` | `not_reported` | `no` | `unclear` | `no` | `unclear` |
| `bernier_class_field` | `david_bernier` | David Bernier | `not_reported` | `selective` | `no` | `unclear` | `no` | `yes` |
| `schmitt_extremal_descendants` | `johannes_schmitt` | Johannes Schmitt | `none` | `selective` | `no` | `unclear` | `no` | `yes` |
| `schildep_polygon` | `schildep` | schildep | `not_reported` | `selective` | `no` | `no` | `no` | `yes` |
| `davis_gradient_descent` | `damek_davis` | Damek Davis | `some` | `selective` | `no` | `no` | `no` | `yes` |
| `paik_optimization` | `seunghoon_paik` | Seunghoon Paik | `none` | `substantial` | `no` | `no` | `no` | `unclear` |
| `armstrong_kempe_degiorgi` | `scott_armstrong` | Scott Armstrong and Julia Kempe | `novice` | `not_reported` | `no` | `no` | `no` | `yes` |
| `aslyan_priority_methods` | `ara_aslyan` | Ara Aslyan | `not_reported` | `selective` | `no` | `unclear` | `no` | `yes` |

## Account and source records

### 1. Thomas Kahle - Auto-formalization I: Keep Trying

- **Account ID:** `kahle_bei`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `kahle_bei`
- **Project cluster:** `kahle_bei`
- **Date:** 2026-05-04
- **Target:** author's 2010 binomial-edge-ideals paper
- **Reported Lean experience:** `learning`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** definition review; mathematical planning; agent orchestration; library-gap triage
- **Observation used by the paper:** Kahle learned Lean while supervising Claude, spent significant time understanding definitions, later used a second LLM to prepare proof guides, and kept TODO/formalization-map state outside chat.
- **Account note:** The post explicitly warns that generated definitions can drift toward easier goals; it does not give one isolated misformalized theorem that we code as a confirmed mismatch.
- **Sources:**
  - `kahle_bei` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Auto-formalization I: Keep Trying; citation `kahle2026keeptrying`; https://thomas-kahle.de/blog/2026/auto-formalization-1-keep-trying/
    Evidence scope: primary account coding. Primary source for the account row.
  - `kahle_bei_followup` (`supplemental`; `blog`; first-person `yes`; public artifact `yes`; build/provenance `unclear`): Auto-formalization II: Now what?; citation `kahle2026nowwhat`; https://thomas-kahle.de/blog/2026/auto-formalization-2-now-what/
    Evidence scope: abstraction; proof bloat; statement-meaning boundary. Follow-up source for the existing BEI account; does not increment the project-account denominator.

### 2. Brett Saiki - Autoformalizing Double Rounding

- **Account ID:** `saiki_double_rounding`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `saiki_double_rounding`
- **Project cluster:** `saiki_double_rounding`
- **Date:** 2026-05-19
- **Target:** author's rounding paper
- **Reported Lean experience:** `novice`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** statement review; definition repair; persistence; mathematical adjudication
- **Observation used by the paper:** Claude inserted additional hypotheses; attempts to remove them produced counterexamples that exposed an underspecified rounding definition and a real missing restriction in the paper.
- **Account note:** The author states he had very little proof-assistant experience and describes a Markdown TODO used across context compaction.
- **Sources:**
  - `saiki_double_rounding` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Autoformalizing Double Rounding; citation `saiki2026double`; https://uwplse.org/2026/05/19/autoformalize.html
    Evidence scope: primary account coding. Primary source for the account row.

### 3. Vasily Ilin - Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau Equilibrium

- **Account ID:** `ilin_vml`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `vasily_ilin`
- **Project cluster:** `ilin_vml`
- **Date:** 2026-03-16
- **Target:** contemporary mathematical physics result
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** high-level supervision; definition review; statement review; adversarial review
- **Observation used by the paper:** A single mathematician supervised multiple AI systems, wrote zero code, archived prompts and commits, and reports hypothesis creep, definition-alignment bugs, agent avoidance, and adversarial self-review.
- **Account note:** The abstract explicitly names these failure modes and the critical role of human review of key definitions and theorem statements.
- **Sources:**
  - `ilin_vml` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau Equilibrium; citation `ilin2026vml`; https://arxiv.org/abs/2603.15929
    Evidence scope: primary account coding. Primary source for the account row.

### 4. Ilya Sergey - Verifying Move Borrow Checker in Lean: an Experiment in AI-Assisted PL Metatheory

- **Account ID:** `sergey_move`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `sergey_move`
- **Project cluster:** `sergey_move`
- **Date:** 2026-03-18
- **Target:** Move borrow-checker metatheory
- **Reported Lean experience:** `expert`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** proof architecture; diagnosing missing lemmas; representation design; stopping unproductive proof search
- **Observation used by the paper:** Sergey reports a 39,000-line Lean development produced in under a month with Claude. When the agent looped for hours, he identified a missing weakening lemma; for enums, he supplied a representation that made the preservation property tractable.
- **Account note:** The post is useful for the division of labor: routine proof repair and repeated cases went to the agent, while the human intervened on proof architecture and representation choices.
- **Sources:**
  - `sergey_move` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Verifying Move Borrow Checker in Lean: an Experiment in AI-Assisted PL Metatheory; citation `sergey2026move`; https://proofsandintuitions.net/2026/03/18/move-borrow-checker-lean/
    Evidence scope: primary account coding. Primary source for the account row.

### 5. Joseph K. Miller - A Formalization of the Mean-Field Derivation of the Vlasov Equation: AI-Assisted Lean Formalization as a Strategy Game

- **Account ID:** `miller_vlasov`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `miller_vlasov`
- **Project cluster:** `miller_vlasov`
- **Date:** 2026-07-09
- **Target:** Vlasov mean-field derivation
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** scope definitions; steer decomposition; library-gap triage
- **Observation used by the paper:** The human directed rather than wrote proofs: scoping definitions, steering decomposition, and triaging library gaps. The paper explicitly leaves intended-statement judgment with the mathematician.
- **Account note:** No specific semantic mismatch is reported in the abstract, so semantic_mismatch is coded no rather than inferred from the methodological warning.
- **Sources:**
  - `miller_vlasov` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): A Formalization of the Mean-Field Derivation of the Vlasov Equation: AI-Assisted Lean Formalization as a Strategy Game; citation `miller2026vlasov`; https://arxiv.org/abs/2607.08986
    Evidence scope: primary account coding. Primary source for the account row.

### 6. Scott Armstrong and Tuomo Kuusi - Formalizing Stochastic Homogenization in Lean

- **Account ID:** `armstrong_homogenization`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `scott_armstrong`
- **Project cluster:** `armstrong_homogenization`
- **Date:** 2026-06-15
- **Target:** authors' stochastic homogenization paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** paper rewrite; theorem correspondence; supervision; library-gap triage
- **Observation used by the paper:** The authors rewrote the theory as a self-contained manuscript, maintain theorem-by-theorem correspondence, and explicitly record Lean statements that are less general or carry additional hypotheses.
- **Account note:** The post reports 449k lines of LLM-written Lean under human supervision and substantial missing background material.
- **Sources:**
  - `armstrong_homogenization` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Formalizing Stochastic Homogenization in Lean; citation `armstrong2026homogenization`; https://www.scottnarmstrong.com/2026/06/formalizing-stochastic-homogenization-in-lean/
    Evidence scope: primary account coding. Primary source for the account row.

### 7. Terence Tao - Sendov formalization making-of

- **Account ID:** `tao_sendov`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `tao_sendov`
- **Project cluster:** `tao_sendov`
- **Date:** 2026-08-10
- **Target:** Sendov and Phelps-Rodriguez formalization
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** target selection; representation choice; staged planning; design review
- **Observation used by the paper:** The curated transcript preserves dead ends and uses Git history as the authoritative chronology; staged plans and design records persist decisions outside the model context.
- **Account note:** The repository states that essentially all Lean was written by Claude under the author's direction and review and that no external independent review had yet been performed.
- **Sources:**
  - `tao_sendov` (`primary`; `repository_transcript`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Sendov formalization making-of; citation `tao2026sendov`; https://github.com/teorth/sendov/blob/master/docs/making-of.md
    Evidence scope: primary account coding. Primary source for the account row.

### 8. Thomas Nowak - Post on a Codex-to-Claude Lean verification workflow

- **Account ID:** `nowak_tcs`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `nowak_tcs`
- **Project cluster:** `nowak_tcs`
- **Date:** 2026
- **Target:** TCS paper lemmas and theorem
- **Reported Lean experience:** `none`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** agent orchestration; semantic review; human model/statement judgment
- **Observation used by the paper:** ChatGPT first declared success without compiling. Codex then produced compiling Lean but introduced extra hypotheses. A separate Claude reviewer checked correspondence, weakening, and remaining sorrys.
- **Account note:** Nowak says this was to his eyes having never read Lean before and says human review of the model and result statements remains essential.
- **Sources:**
  - `nowak_tcs` (`primary`; `social_post`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Post on a Codex-to-Claude Lean verification workflow; citation `nowak2026workflow`; https://www.linkedin.com/posts/nowathom_a-few-days-ago-jukka-suomela-posted-about-activity-7428414495590400000-YJ2A
    Evidence scope: primary account coding. Primary source for the account row.
  - `nowak_tcs_eatcs` (`supplemental`; `paper`; first-person `yes`; public artifact `yes`; build/provenance `unclear`): Adding “Verified” Badges to Our Paper, One Lemma at a Time; citation `fuegger2026verifiedbadges`; https://bulletin.eatcs.org/index.php/beatcs/index
    Evidence scope: two-agent generator/reviewer workflow; faithfulness checking; novice Lean use. Durable Bulletin of the EATCS account supplementing the earlier social post.

### 9. Jukka Suomela - Post describing a solve-formalize-fix loop

- **Account ID:** `suomela_loop`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `suomela_loop`
- **Project cluster:** `suomela_loop`
- **Date:** 2026
- **Target:** research math problems
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `none`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `yes`
- **Human role described:** problem selection; post-hoc mathematical understanding
- **Observation used by the paper:** Suomela explicitly describes not looking at the Lean code and only paying close attention to the mathematical proof after the chatbot reaches a Lean formalization.
- **Account note:** The source does not claim that Suomela lacks Lean expertise; only reads_generated_lean=none is coded from the explicit workflow description.
- **Sources:**
  - `suomela_loop` (`primary`; `social_post`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Post describing a solve-formalize-fix loop; citation `suomela2026workflow`; https://www.linkedin.com/posts/jukkasuomela_it-is-surprising-how-well-this-simple-scheme-activity-7425924723697610752-md-Q
    Evidence scope: primary account coding. Primary source for the account row.

### 10. Vjekoslav Kovač - Erdos Problem 189 discussion

- **Account ID:** `kovac_erdos189`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `kovac_erdos189`
- **Project cluster:** `kovac_erdos189`
- **Date:** 2025-12-17
- **Target:** Erdos Problem 189
- **Reported Lean experience:** `novice`
- **Reads generated Lean:** `none`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `qualified`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** blueprint writing; LLM back-translation; request for community review
- **Observation used by the paper:** Kovač asked Aristotle to formalize a LaTeX blueprint, stripped links/comments, and asked Gemini to translate the main theorem back to English because he could not read Lean.
- **Account note:** A follow-up by Tao reports that the separate Formal Conjectures statement was itself misformalized; this is coded qualified because it was not generated by Kovač's pipeline.
- **Sources:**
  - `kovac_erdos189` (`primary`; `forum_post`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Erdos Problem 189 discussion; citation `kovac2025erdos189`; https://www.erdosproblems.com/forum/thread/189
    Evidence scope: primary account coding. Primary source for the account row.

### 11. Haruhisa Enomoto - I Quit Math Then Wrote a Paper with AI

- **Account ID:** `enomoto_quotient`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `enomoto_quotient`
- **Project cluster:** `enomoto_quotient`
- **Date:** 2026-08
- **Target:** author's AI-assisted representation-theory paper
- **Reported Lean experience:** `some`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `no`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `no`; **post-hoc understanding:** `yes`
- **Human role described:** multi-agent checking; post-hoc proof digestion; conceptual reinterpretation
- **Observation used by the paper:** After repeated cross-model informal checking had found no problem, Lean formalization encountered a false proof-essential manuscript claim, built a counterexample, replaced the proof, and continued. The author later undertook a separate proof-digestion phase.
- **Account note:** Enomoto reports prior personal Lean experience; the false claim was in the informal proof rather than a Lean/source correspondence mismatch.
- **Sources:**
  - `enomoto_quotient` (`primary`; `essay`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): I Quit Math Then Wrote a Paper with AI; citation `enomoto2026essay`; https://haruhisa-enomoto.github.io/quotient-submodule-equidistribution-essay/index.html
    Evidence scope: primary account coding. Primary source for the account row.

### 12. Sang-il Oum - Formalizing a recent preprint in Lean with Aristotle

- **Account ID:** `oum_preprint`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `oum_preprint`
- **Project cluster:** `oum_preprint`
- **Date:** 2026-04-05
- **Target:** author's submodular-functions preprint
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `yes`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** source correction; supervision
- **Observation used by the paper:** The formalization exposed a missing non-negativity condition in Lemma 4.1, and the author uploaded a corrected arXiv version.
- **Account note:** This is coded as source_defect_found rather than semantic_mismatch because the Lean process exposed a defect in the informal source statement.
- **Sources:**
  - `oum_preprint` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Formalizing a recent preprint in Lean with Aristotle; citation `oum2026preprint`; https://sangil.dimag.kr/2026/formalizing-my-recent-preprint/
    Evidence scope: primary account coding. Primary source for the account row.

### 13. Yoichi Hirai - Lean4 formalization of A Simplified Round-by-round Soundness Proof of FRI

- **Account ID:** `hirai_fri`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `hirai_fri`
- **Project cluster:** `hirai_fri`
- **Date:** 2026-01-26
- **Target:** FRI cryptography paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** source comparison; decomposition; agent orchestration; code cleanup
- **Observation used by the paper:** Hirai compared Lean with the paper, records an added degree-positivity condition, used Claude to state/decompose missing lemmas and Aristotle to prove or counterexample them, then annotated code with paper locations.
- **Account note:** The post explicitly says misformalization is the remaining room for error and that the author compared the Lean code against the original paper.
- **Sources:**
  - `hirai_fri` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Lean4 formalization of A Simplified Round-by-round Soundness Proof of FRI; citation `hirai2026fri`; https://blog.zksecurity.xyz/posts/simple-rbr-fri/
    Evidence scope: primary account coding. Primary source for the account row.

### 14. Robert J. and collaborators - Formalizing the Andrews-Curtis Conjecture

- **Account ID:** `robertj_ac`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `robertj_ac`
- **Project cluster:** `robertj_ac`
- **Date:** 2026
- **Target:** Andrews-Curtis definitions and computational certificates
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** definition design; focused agent questions; source checking
- **Observation used by the paper:** The team used Aristotle while definitions were evolving and later during a broader audit. Aristotle found a mismatch between two move systems; humans repaired the interface and proved the translation theorem.
- **Account note:** The author says every suggestion was checked against the source and mathematics.
- **Sources:**
  - `robertj_ac` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Formalizing the Andrews-Curtis Conjecture; citation `robertj2026ac`; https://www.robertj1.com/ai4science/ac-conjecture-aristotle/
    Evidence scope: primary account coding. Primary source for the account row.

### 15. John Ennis - My Experiences Using AI for Math

- **Account ID:** `ennis_math`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `ennis_math`
- **Project cluster:** `ennis_math`
- **Date:** 2026-07-21
- **Target:** research mathematics and a separate Lean formalization
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** hostile review; source/status tracking; mathematical custody
- **Observation used by the paper:** Ennis reports source/status/confidence tracking, hostile reviewers finding scope mismatches and stale summaries, and a Lean project exposing hidden assumptions in informal mathematics.
- **Account note:** The essay spans several projects; codes refer only to observations explicitly tied to proof custody or Lean/formalization work.
- **Sources:**
  - `ennis_math` (`primary`; `essay`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): My Experiences Using AI for Math; citation `ennis2026experience`; https://www.linkedin.com/pulse/my-experiences-using-ai-math-john-ennis-uauwe
    Evidence scope: primary account coding. Primary source for the account row.

### 16. Timothy Gowers - Thoughts about the Leiden Declaration

- **Account ID:** `gowers_leiden`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `gowers_leiden`
- **Project cluster:** `gowers_leiden`
- **Date:** 2026-07-26
- **Target:** complicated research paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** high-level delegation
- **Observation used by the paper:** Gowers reports using Aristotle to formalize a complicated paper in Lean without needing to know Lean.
- **Account note:** This short report supports the existence of low-Lean-literacy workflows but does not describe the review mechanism in enough detail to code more fields.
- **Sources:**
  - `gowers_leiden` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Thoughts about the Leiden Declaration; citation `gowers2026leiden`; https://gowers.wordpress.com/2026/07/26/thoughts-about-the-leiden-declaration/
    Evidence scope: primary account coding. Primary source for the account row.

### 17. Timothy Chow - Aristotle waitlist discussion

- **Account ID:** `chow_aristotle`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `chow_aristotle`
- **Project cluster:** `chow_aristotle`
- **Date:** 2026-01
- **Target:** submitted Lean theorem with one sorry
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** output inspection; community feedback
- **Observation used by the paper:** Chow reports a run that returned a file with the target theorem and associated definitions deleted rather than proved.
- **Account note:** This is coded as a target-removal failure, not as semantic_mismatch, because the output evaded the task rather than changing a surviving formal statement.
- **Sources:**
  - `chow_aristotle` (`primary`; `zulip`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Aristotle waitlist discussion; citation `chow2026aristotle`; https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Aristotle%27s.20waitlist.20is.20gone.html
    Evidence scope: primary account coding. Primary source for the account row.

### 18. J. J. Issai - Understanding what Aristotle is formalizing

- **Account ID:** `issai_aristotle`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `issai_aristotle`
- **Project cluster:** `issai_aristotle`
- **Date:** 2026-01-29
- **Target:** prime-counting bounds
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `qualified`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** statement interpretation; community review
- **Observation used by the paper:** Issai reports that Aristotle's output seems not to track the intended statement and asks how to reconcile the formal object with the intended prime-counting function.
- **Account note:** The original query was unavailable, so the source itself warns that the problem may have been misstated before Aristotle saw it; semantic_mismatch is qualified.
- **Sources:**
  - `issai_aristotle` (`primary`; `zulip`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Understanding what Aristotle is formalizing; citation `issai2026understanding`; https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Understanding.20what.20Aristotle.20is.20formalizing.html
    Evidence scope: primary account coding. Primary source for the account row.

### 19. Kelly Davis and Vasily Ilin - Aristotle Partial Results discussion

- **Account ID:** `davis_partial`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `vasily_ilin`
- **Project cluster:** `davis_partial`
- **Date:** 2026-02-23
- **Target:** hard Lean problems
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** failure analysis; provenance tracking
- **Observation used by the paper:** Davis asks for partial results when Aristotle gives up; Ilin asks for the original prompt to be preserved because repeated prompts become difficult to distinguish.
- **Account note:** This source is included for persistence/provenance rather than semantic correspondence.
- **Sources:**
  - `davis_partial` (`primary`; `zulip`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Aristotle Partial Results discussion; citation `davis2026partial`; https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Aristotle.20Partial.20Results.html
    Evidence scope: primary account coding. Primary source for the account row.

### 20. Djalil Chafaï - Lean formalization with AI

- **Account ID:** `chafai_ginibre`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `chafai_ginibre`
- **Project cluster:** `chafai_ginibre`
- **Date:** 2026-09-04
- **Target:** Theorem 1.9 of author's recent paper
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** target selection; high-level delegation
- **Observation used by the paper:** After a few manual explorations to select a target theorem, Chafaï delegated a roughly six-hour agent run that produced about 16.4k lines across about 75 files and a checked theorem.
- **Account note:** The post is a capability/scale snapshot and gives little information about semantic review, so most review codes remain no/not_reported.
- **Sources:**
  - `chafai_ginibre` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Lean formalization with AI; citation `chafai2026leanai`; https://djalil.chafai.net/blog/2026/09/04/lean-formalization-with-ai/
    Evidence scope: primary account coding. Primary source for the account row.

### 21. Boris Alexeev - Formalization of Erdos problems

- **Account ID:** `alexeev_erdos`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `alexeev_erdos`
- **Project cluster:** `alexeev_erdos`
- **Date:** 2025-12-05
- **Target:** collection of Erdos problems
- **Reported Lean experience:** `mixed`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** pipeline design; statement checking; intervention on failures
- **Observation used by the paper:** Alexeev reports repeated misformalizations across a semi-automated pipeline, including wrong variables, flipped inequalities/quantifiers, missing hypotheses, and higher-level mismatches. Counterexamples often exposed them.
- **Account note:** The post explicitly says misformalization was more frequent than expected and that the workflow changed rapidly as new tools appeared.
- **Sources:**
  - `alexeev_erdos` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Formalization of Erdos problems; citation `alexeev2025erdos`; https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/
    Evidence scope: primary account coding. Primary source for the account row.

### 22. Shuo Deng and Kenneth W. Shum - From Lecture Notes to Lean: Formalizing a Textbook on Probability Theory

- **Account ID:** `deng_shum_probability`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `deng_shum_probability`
- **Project cluster:** `deng_shum_probability`
- **Date:** 2026-07-29
- **Target:** measure-theoretic probability textbook
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `unclear`
- **Semantic mismatch:** `yes`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** statement approval; source-error adjudication; source-to-Lean review
- **Observation used by the paper:** An initial variance declaration compiled while imposing weaker domain discipline than the textbook intended. The workflow separately reviews candidates against source passages; formalization also exposed a missing textbook hypothesis and produced a counterexample.
- **Account note:** The paper explicitly separates successful builds from source-fidelity review. It describes manual semantic checking but does not identify the read-only reviewer as a distinct AI role, so separate_ai_review is unclear.
- **Sources:**
  - `deng_shum_probability` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): From Lecture Notes to Lean: Formalizing a Textbook on Probability Theory; citation `deng2026probability`; https://arxiv.org/abs/2607.27298
    Evidence scope: primary account coding. Primary source for the account row.

### 23. Jaume de Dios Pont, Lukas Liehr, David Muñoz-Lahoz, Mitchell A. Taylor, and Pedro Tradacete - Banach lattices and phase retrieval: A case study for the use of AI in mathematics

- **Account ID:** `dedios_banach_phase`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `dedios_banach_phase`
- **Project cluster:** `banach_phase_retrieval`
- **Date:** 2026-08-07
- **Target:** Banach-lattice and phase-retrieval research formalizations
- **Reported Lean experience:** `mixed`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `unclear`
- **Semantic mismatch:** `qualified`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `unclear`; **post-hoc understanding:** `yes`
- **Human role described:** statement and definition review; mathematical interpretation; post-certificate proof digestion; library curation
- **Observation used by the paper:** The group concentrated intensive review on theorem statements and their definitions rather than generated proof bodies, warns that LLMs can alter definitions in ways that simplify proofs, and describes revisiting an argument after obtaining a Lean certificate in order to understand and generalize it.
- **Account note:** The definition-drift statement is a reported recurring risk rather than one isolated mismatch in a named theorem, so semantic_mismatch is qualified. The group includes both experienced formalizers and a contributor reported to have had no Lean experience three months earlier.
- **Sources:**
  - `dedios_banach_phase` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Banach lattices and phase retrieval: A case study for the use of AI in mathematics; citation `dedios2026banach`; https://arxiv.org/abs/2608.07396
    Evidence scope: primary account coding. Primary source for the account row.
  - `munozlahoz_banach_library` (`corroborating`; `paper`; first-person `yes`; public artifact `yes`; build/provenance `unclear`): The Banach lattice Lean library; citation `munozlahoz2026banachlibrary`; https://arxiv.org/abs/2608.07388
    Evidence scope: companion artifact and workflow context for the Banach-lattice project. Companion paper from the same project; retained as corroborating evidence rather than treated as a duplicate account.

### 24. Ho-Lin Chen and Xiang Huang - Ripple: An Open, AI-Formalized Lean 4 Framework for Computing with CRNs

- **Account ID:** `chen_huang_ripple`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `chen_huang_ripple`
- **Project cluster:** `chen_huang_ripple`
- **Date:** 2026-07-21
- **Target:** chemical reaction network computation framework
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `no`; **source defect found:** `yes`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** direction and review; construction design; counterexample-first checking; framework curation
- **Observation used by the paper:** The project reports source gaps exposed during formalization and a playbook that checks residual goals for counterexamples before proof attempts, with cross-verification by a second independent model. Planning and assumption state are retained outside model context.
- **Account note:** The paper reports genuine gaps in published arguments and several defenses against vacuous or false targets. We do not code those source gaps as a source-to-Lean semantic mismatch.
- **Sources:**
  - `chen_huang_ripple` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Ripple: An Open, AI-Formalized Lean 4 Framework for Computing with CRNs; citation `chen2026ripple`; https://arxiv.org/abs/2607.13531
    Evidence scope: primary account coding. Primary source for the account row.

### 25. Ashvin Swaminathan - On the Quartic Invariant of Odd Degree Binary Forms

- **Account ID:** `swaminathan_quartic`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `swaminathan_quartic`
- **Project cluster:** `swaminathan_quartic`
- **Date:** 2026-03-25
- **Target:** quartic invariant of odd-degree binary forms
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `yes`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** mathematical review and correction; target selection; proof-strategy judgment
- **Observation used by the paper:** Claude Code and Codex completed parts of the proof and Aristotle discharged Lean obligations under author review. Formal verification uncovered a sign error in an earlier draft of Proposition 5.3, which the author corrected.
- **Account note:** The reported defect was in an earlier manuscript draft rather than a mismatch between a source theorem and its Lean statement. The project retained the author's notes and modular Lean companion materials.
- **Sources:**
  - `swaminathan_quartic` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): On the Quartic Invariant of Odd Degree Binary Forms; citation `swaminathan2026quartic`; https://arxiv.org/abs/2603.24330
    Evidence scope: primary account coding. Primary source for the account row.

### 26. Gabriel Rongyang Lau - Using Aristotle API for AI-Assisted Theorem Proving in Lean 4: A Formalisation Case Study of the Grasshopper Problem

- **Account ID:** `lau_grasshopper`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `lau_grasshopper`
- **Project cluster:** `lau_grasshopper`
- **Date:** 2026-05-19
- **Target:** IMO 2009 Grasshopper problem
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** artifact inspection; verification-status auditing; separation of local lemmas from headline completion
- **Observation used by the paper:** The generated artifact contained four verified helper lemmas while the main theorem remained closed directly by one unresolved sorry. The paper analyzes the verified and unverified parts of the artifact separately.
- **Account note:** This is an incompleteness/admission-state example rather than a source-correspondence mismatch. Reproducible Lean artifacts are provided with the paper.
- **Sources:**
  - `lau_grasshopper` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Using Aristotle API for AI-Assisted Theorem Proving in Lean 4: A Formalisation Case Study of the Grasshopper Problem; citation `lau2026grasshopper`; https://arxiv.org/abs/2605.20120
    Evidence scope: primary account coding. Primary source for the account row.

### 27. Cameron Freer - Three Roads to de Finetti's Theorem in Lean 4

- **Account ID:** `freer_definetti`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `freer_definetti`
- **Project cluster:** `freer_definetti`
- **Date:** 2026-07-16
- **Target:** de Finetti--Ryll-Nardzewski theorem
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** proof-route design; common interface selection; independent-route cross-checking
- **Observation used by the paper:** Three independently formalized proof routes were required to reach the same finite conditional-factorization interface before the common conclusion, providing a cross-check during extensive Claude- and GPT-assisted development.
- **Account note:** The cross-check is between independent mathematical proof routes, not a separately assigned AI review role. The paper also reports a reusable Lean proof-engineering skill developed during the project.
- **Sources:**
  - `freer_definetti` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Three Roads to de Finetti's Theorem in Lean 4; citation `freer2026definetti`; https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.34
    Evidence scope: primary account coding. Primary source for the account row.
  - `freer_lean_skill` (`supplemental`; `zulip`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Lean Skill for Claude Code; citation `freer2025leanskill`; https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Lean.20Skill.20for.20Claude.20Code.html
    Evidence scope: agent guardrails against premature success, axioms, and sorries. Supplemental workflow evidence from the same practitioner/project context.

### 28. Yuanhe Zhang, Jason D. Lee, and Fanghui Liu - AI4SLT: Empirical Processes in Lean 4 for Formal Statistical Learning Theory

- **Account ID:** `zhang_slt`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `zhang_slt`
- **Project cluster:** `zhang_slt`
- **Date:** 2026-06-10
- **Target:** statistical learning theory and empirical processes
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `unclear`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** proof-strategy design; theorem decomposition; target-statement verification; supervised cleanup
- **Observation used by the paper:** The authors report three misformalized target statements that survived multiple rounds of AI self-judgment and were detected by humans constructing explicit counterexamples. The workflow preserved structured TASK.md specifications for proof tasks.
- **Account note:** The paper also reports resolving implicit assumptions and missing textbook details, but it does not identify all of these as defects in one fixed source, so source_defect_found remains unclear.
- **Sources:**
  - `zhang_slt` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): AI4SLT: Empirical Processes in Lean 4 for Formal Statistical Learning Theory; citation `zhang2026slt`; https://arxiv.org/abs/2602.02285
    Evidence scope: primary account coding. Primary source for the account row.

### 29. John D. Cook - Formalizing a ring theorem with Lean 4 and Claude

- **Account ID:** `cook_partial_fractions`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `cook_partial_fractions`
- **Project cluster:** `cook_partial_fractions`
- **Date:** 2026-06-17
- **Target:** partial fraction decomposition over a principal ideal domain
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** compiler-feedback relay; output inspection; admission-state checking
- **Observation used by the paper:** After eleven iterations driven by compiler errors, Claude produced an artifact that the author initially described as a proof but that still contained five sorry placeholders; attempts to remove them had not succeeded by the end of the experiment.
- **Account note:** This is a partial experiment rather than a completed formalization. It is included because the author explicitly inspects and reports the remaining admissions.
- **Sources:**
  - `cook_partial_fractions` (`primary`; `blog`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Formalizing a ring theorem with Lean 4 and Claude; citation `cook2026rings`; https://www.johndcook.com/blog/2026/06/17/rings-with-lean-claude/
    Evidence scope: primary account coding. Primary source for the account row.

### 30. Michael R. Douglas, Sarah Hoback, Anna Mei, and Ron Nissim - Formalization of QFT

- **Account ID:** `douglas_qft`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `douglas_qft`
- **Project cluster:** `douglas_qft`
- **Date:** 2026-03-16
- **Target:** free bosonic Euclidean quantum field theory
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** definition design; high-level decomposition; cross-model review; assumption tracking
- **Observation used by the paper:** The project cross-validated conjectured helper lemmas and proof plans among Claude, Gemini, and GPT, tracked active assumptions in auxiliary documents, and reports correcting several project definitions, including its original rendition of the Osterwalder--Schrader axioms.
- **Account note:** The definition errors were internal to the formalization project rather than defects in an external source. The original release carried three named assumptions that later work proved or avoided.
- **Sources:**
  - `douglas_qft` (`primary`; `paper`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Formalization of QFT; citation `douglas2026qft`; https://arxiv.org/abs/2603.15770
    Evidence scope: primary account coding. Primary source for the account row.

### 31. Kyle Treleaven - Post on AI-assisted Lean formalization of a pile-shuffle reduction

- **Account ID:** `treleaven_pile_shuffle`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `treleaven_pile_shuffle`
- **Project cluster:** `treleaven_pile_shuffle`
- **Date:** 2026
- **Target:** first reduction in an NP-hardness proof for pile-shuffle sorting
- **Reported Lean experience:** `none`
- **Reads generated Lean:** `none`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** conceptual steering; iterative supervision; artifact integration
- **Observation used by the paper:** Treleaven reports starting with no Lean experience, using mostly Claude Code with some Codex, and being unable to meaningfully read the generated proof code while relying on Lean to check it; he also reports substantial ongoing supervision of the agents.
- **Account note:** The public LinkedIn activity item links both the paper and Lean repository. It describes proof readability and supervision but no separate semantic-review role.
- **Sources:**
  - `treleaven_pile_shuffle` (`primary`; `social_post`; first-person `yes`; public artifact `unclear`; build/provenance `unclear`): Post on AI-assisted Lean formalization of a pile-shuffle reduction; citation `treleaven2026lean`; https://www.linkedin.com/in/kyle-treleaven-58586a22
    Evidence scope: primary account coding. Primary source for the account row.

### 32. Katherine M. Collins et al. - Characterizing initial human-AI proof formalization workflows

- **Account ID:** `collins_workflows`
- **Account kind:** `human_study`
- **Practitioner-overlap cluster:** `collins_workflows`
- **Project cluster:** `collins_workflows`
- **Date:** 2026-06-02
- **Target:** controlled formalization tasks
- **Reported Lean experience:** `mixed`
- **Reads generated Lean:** `varied`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `no`; **post-hoc understanding:** `no`
- **Human role described:** survey; controlled user study; workflow observation
- **Observation used by the paper:** A survey of 31 respondents and a controlled study with seven usable participants found heterogeneous preferences, broad desire for high-level human control, and six of seven study participants using more than one AI tool.
- **Account note:** This row is a study rather than a practitioner report and is excluded from practitioner-report counts.
- **Sources:**
  - `collins_workflows` (`primary`; `human_study`; first-person `no`; public artifact `unclear`; build/provenance `unclear`): Characterizing initial human-AI proof formalization workflows; citation `collins2026workflows`; https://arxiv.org/abs/2606.04273
    Evidence scope: primary account coding. Primary source for the account row.

### 33. Rohan Yadav - Experience Report: Leveraging LLMs for Formal Verification

- **Account ID:** `yadav_gpu_verification`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `rohan_yadav`
- **Project cluster:** `yadav_gpu_verification`
- **Date:** 2026-06-26
- **Target:** formal semantics and race-detection proofs for high-performance GPU programs
- **Reported Lean experience:** `some`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `unclear`; **post-hoc understanding:** `no`
- **Human role described:** definition review; theorem-statement review; mathematical supervision
- **Observation used by the paper:** Yadav reports painstakingly examining every definition and theorem statement because modeling errors would not be caught merely by type checking, while largely ignoring proof implementations; he also reports Claude attempts to weaken a theorem by adding a hypothesis.
- **Account note:** The mismatch coding concerns explicit attempted theorem weakening caught during supervision, not a claim that a bad statement survived into the final artifact.
- **Sources:**
  - `yadav_gpu_verification` (`primary`; `blog`; first-person `yes`; public artifact `yes`; build/provenance `unclear`): Experience Report: Leveraging LLMs for Formal Verification; citation `yadav2026verification`; https://rohany.github.io/blog/llm-verification-experience/
    Evidence scope: definition and theorem-statement review; attempted hypothesis weakening. First-person experience report.

### 34. John P. Warren - Tessera: a machine-checked false-alarm guarantee for GPU fleets

- **Account ID:** `warren_tessera`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `john_p_warren`
- **Project cluster:** `warren_tessera`
- **Date:** 2026-07-27
- **Target:** statistical false-discovery guarantees for GPU fleet health verdicts
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `yes`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** statement design; numerical validation; proof-driven audit; counterexample analysis
- **Observation used by the paper:** Five AI-written formal statements passed the type checker and the author's numerical validation but were wrong; proof attempts exposed missing summability, measurability, independence, a bad quantifier domain, and a placeholder assumption encoded as True.
- **Account note:** The failures and their replacements are retained in public repository history; the account distinguishes well-formed statements from proved statements.
- **Sources:**
  - `warren_tessera` (`primary`; `blog`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Tessera: a machine-checked false-alarm guarantee for GPU fleets; citation `warren2026tessera`; https://johnpwarren.dev/blog/tessera-lean/
    Evidence scope: five wrong formal statements; counterexamples; repository history. First-person post documents each failed statement and why validation missed it.

### 35. Leonid Zaliva - Extracting a Formal Semantics with AI Agents

- **Account ID:** `zaliva_bc_semantics`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `leonid_zaliva`
- **Project cluster:** `zaliva_bc_semantics`
- **Date:** 2026-06-12
- **Target:** executable Lean semantics for the POSIX subset of bc
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `yes`
- **Semantic mismatch:** `yes`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** semantic architecture; boundary setting; human review; multi-agent review
- **Observation used by the paper:** A different-agent review found parser and semantic defects; human review forced a redesign of the small-step semantics; and the first progress theorem proved a property of the wrong execution model despite a green, sorry-free build.
- **Account note:** The author explicitly treats correctness as open pending further human review even after the final build and tests pass.
- **Sources:**
  - `zaliva_bc_semantics` (`primary`; `blog`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Extracting a Formal Semantics with AI Agents; citation `zaliva2026semantics`; https://zaliva.org/blog/2026/06/semantics-extraction.html
    Evidence scope: different-agent review; semantic redesign; wrong progress property. First-person report with explicit final-review qualification.

### 36. Eric Vergo - AI-written Chebyshev / roots-of-unity Lean experiment

- **Account ID:** `vergo_chebyshev`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `eric_vergo`
- **Project cluster:** `vergo_chebyshev`
- **Date:** 2025-11-15
- **Target:** Chebyshev-polynomial and roots-of-unity arguments
- **Reported Lean experience:** `learning`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `unclear`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `unclear`; **post-hoc understanding:** `no`
- **Human role described:** prompting; build checking; public solicitation of mathematical and Lean review
- **Observation used by the paper:** Vergo reports more than 3000 lines of AI-written Lean that build and type-check while explicitly declining to claim that the repository captures the intended mathematics because he lacks the expertise to judge that correspondence.
- **Account note:** This is evidence about the limits of a compiling artifact for a novice reviewer, not a confirmed semantic mismatch.
- **Sources:**
  - `vergo_chebyshev` (`primary`; `zulip`; first-person `yes`; public artifact `yes`; build/provenance `unclear`): Discussion: AI-written mathematical proofs; citation `vergo2025aiproofs`; https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs.html
    Evidence scope: compiling artifact; reviewer inability to judge intended correspondence. Public Lean community discussion linked to the ChebyshevCircles repository.

### 37. David Bernier - Formalizing a conjecture in explicit Class Field Theory

- **Account ID:** `bernier_class_field`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `david_bernier`
- **Project cluster:** `bernier_class_field`
- **Date:** 2026-02-08
- **Target:** explicit class-field-theory special cases related to cubic Frobenius behavior
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `no`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** problem selection; artifact preservation; community solicitation for statement review
- **Observation used by the paper:** Bernier reports roughly a dozen Aristotle proofs that compile without errors and contain no sorries, while specifically asking the Lean community to check whether the question itself had been misformalized.
- **Account note:** The source raises misformalization as an unresolved review question rather than documenting a confirmed mismatch.
- **Sources:**
  - `bernier_class_field` (`primary`; `zulip`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Formalizing a conjecture in explicit Class Field Theory; citation `bernier2026classfield`; https://leanprover-community.github.io/archive/stream/116395-maths/topic/Formalizing.20a.20conjecture.20in.20explicit.20Class.20Field.20Theory.html
    Evidence scope: sorry-free special cases; request for misformalization review. Public Lean community discussion links the preserved Aristotle files.

### 38. Johannes Schmitt - Extremal descendant integrals on moduli spaces of curves: An inequality discovered and proved in collaboration with AI

- **Account ID:** `schmitt_extremal_descendants`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `johannes_schmitt`
- **Project cluster:** `schmitt_extremal_descendants`
- **Date:** 2025-12-16
- **Target:** extremal psi-class descendant integrals on moduli spaces of curves
- **Reported Lean experience:** `none`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** mathematical checking; AI workflow supervision; public solicitation of formalization review
- **Observation used by the paper:** Schmitt began the formalization with no prior Lean experience; the Lean was AI-generated, the mathematical result received human checking, and he publicly solicited experienced review for possible formalization problems.
- **Account note:** The account is coded as unclear rather than yes for semantic mismatch because it requests review without reporting a confirmed statement defect.
- **Sources:**
  - `schmitt_extremal_descendants` (`primary`; `paper`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Extremal descendant integrals on moduli spaces of curves: An inequality discovered and proved in collaboration with AI; citation `schmitt2025extremal`; https://arxiv.org/abs/2512.14575
    Evidence scope: AI-authorship transparency; Lean experience and review workflow. Paper records the AI-assisted formalization workflow and supporting prompts/logs.

### 39. schildep - Verified Polygon Intersection

- **Account ID:** `schildep_polygon`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `schildep`
- **Project cluster:** `schildep_polygon`
- **Date:** 2026
- **Target:** verified polygon-intersection implementation
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `unclear`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** specification review; trust-boundary design; build verification
- **Observation used by the paper:** The project makes a short human-reviewed specification the trust boundary: reviewers inspect 87 lines of specification while AI-written implementation and proof files are deliberately not reviewed line by line.
- **Account note:** This is a software-verification account included to broaden the corpus beyond theorem formalization; no semantic defect is claimed.
- **Sources:**
  - `schildep_polygon` (`primary`; `repository_readme`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Verified Polygon Intersection; citation `schildep2026polygon`; https://github.com/schildep/verified-polygon-intersection
    Evidence scope: 87-line human-reviewed specification; unread AI implementation/proofs. Repository README explicitly states the intended human review boundary.

### 40. Damek Davis - gd-lean: gradient-descent convergence formalization

- **Account ID:** `davis_gradient_descent`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `damek_davis`
- **Project cluster:** `davis_gradient_descent`
- **Date:** 2026-02-08
- **Target:** convergence rate for gradient descent on smooth convex functions
- **Reported Lean experience:** `some`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** proof-blueprint generation; artifact preservation; reproducible handoff across models
- **Observation used by the paper:** Davis preserves the exact GPT-5.2 proof-blueprint transcript, unedited handoff to Aristotle, raw Aristotle output, Codex cleanup diff, final artifact, and pinned Lean environment.
- **Account note:** Included as provenance-positive evidence rather than as a semantic-failure case.
- **Sources:**
  - `davis_gradient_descent` (`primary`; `repository_readme`; first-person `yes`; public artifact `yes`; build/provenance `yes`): gd-lean; citation `davis2026gdlean`; https://github.com/damek/gd-lean
    Evidence scope: exact blueprint transcript; raw output; cleanup diff; pinned toolchain. Repository retains the full generation flow and provenance artifacts.

### 41. Seunghoon Paik - Lean notes from formalizing optimization research

- **Account ID:** `paik_optimization`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `seunghoon_paik`
- **Project cluster:** `paik_optimization`
- **Date:** 2026
- **Target:** formalization of optimization research results
- **Reported Lean experience:** `none`
- **Reads generated Lean:** `substantial`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `unclear`; **post-hoc understanding:** `no`
- **Human role described:** learning Lean and Mathlib; reviewing generated code; mathematical supervision
- **Observation used by the paper:** Paik describes LLMs generating most of the Lean while he invested substantial effort in understanding Lean and Mathlib, and explicitly asks how much of a generated proof a human needs to understand once Lean has checked it.
- **Account note:** The account is retained for the novice-review question; it does not report a confirmed semantic failure.
- **Sources:**
  - `paik_optimization` (`primary`; `essay`; first-person `yes`; public artifact `yes`; build/provenance `unclear`): Lean; citation `paik2026lean`; https://seunghoonpaik.com/docs/notes/lean/
    Evidence scope: novice workflow; generated-code understanding; Lean/Mathlib learning. Personal notes on LLM-assisted Lean work.

### 42. Scott Armstrong and Julia Kempe - Formalizing De Giorgi-Nash-Moser Theory in Lean

- **Account ID:** `armstrong_kempe_degiorgi`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `scott_armstrong`
- **Project cluster:** `armstrong_kempe_degiorgi`
- **Date:** 2026-04-07
- **Target:** De Giorgi-Nash-Moser regularity theory
- **Reported Lean experience:** `novice`
- **Reads generated Lean:** `not_reported`
- **Multiple AI tools:** `yes`; **separate AI review:** `no`
- **Semantic mismatch:** `no`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** detailed proof blueprints; architecture; mathematical decision-making; agent supervision
- **Observation used by the paper:** Armstrong and Kempe report roughly 56,000 lines of entirely LLM-written Lean produced without humans editing the Lean files, while they supplied detailed proof blueprints and architectural guidance.
- **Account note:** This is a distinct project account from Armstrong and Kuusi's stochastic-homogenization account but shares the scott_armstrong practitioner-overlap cluster.
- **Sources:**
  - `armstrong_kempe_degiorgi` (`primary`; `blog`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Formalizing De Giorgi-Nash-Moser Theory in Lean; citation `armstrong2026degiorgi`; https://www.scottnarmstrong.com/2026/04/formalizing-de-giorgi-nash-moser-theory-in-lean/
    Evidence scope: 56K LLM-written lines; human blueprints and architecture. Distinct project from the later stochastic-homogenization account.

### 43. Ara Aslyan - AI-assisted Friedberg-Muchnik and Sacks splitting formalization

- **Account ID:** `aslyan_priority_methods`
- **Account kind:** `practitioner_account`
- **Practitioner-overlap cluster:** `ara_aslyan`
- **Project cluster:** `aslyan_priority_methods`
- **Date:** 2026-07-26
- **Target:** Friedberg-Muchnik theorem and Sacks splitting theorem
- **Reported Lean experience:** `not_reported`
- **Reads generated Lean:** `selective`
- **Multiple AI tools:** `unclear`; **separate AI review:** `no`
- **Semantic mismatch:** `unclear`; **source defect found:** `no`; **counterexample used:** `no`
- **Persistent project state:** `yes`; **post-hoc understanding:** `no`
- **Human role described:** problem selection; symbol and architecture choices; modeling review; redirection at mathematical decision points
- **Observation used by the paper:** Aslyan describes choosing the problem, symbols, architecture, and alternative approaches, challenging modeling decisions and redirecting the agent while the agent performs the Lean implementation; the completed developments are reported sorry-free and explicitly offered for independent review.
- **Account note:** Modeling choices are described as actively challenged and redirected, but the posts do not isolate one accepted semantic mismatch; the field is therefore unclear.
- **Sources:**
  - `aslyan_priority_methods` (`primary`; `social_post`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Formalizing Friedberg-Muchnik Theorem with Lean 4 AI; citation `aslyan2026friedberg`; https://www.linkedin.com/posts/ara-aslyan-b823554_github-aaslyanfriedberg-muchnik-lean-activity-7487165343233167360-Bn11
    Evidence scope: human architecture and modeling decisions; independent-review request. Primary post for the project/workflow account.
  - `aslyan_sacks_followup` (`supplemental`; `social_post`; first-person `yes`; public artifact `yes`; build/provenance `yes`): Formalizing Friedberg-Muchnik theorem in Lean 4; citation `aslyan2026sacks`; https://www.linkedin.com/posts/ara-aslyan-b823554_github-aaslyanfriedberg-muchnik-lean-activity-7489112983865065473-8Kag
    Evidence scope: Sacks splitting extension; direct human decision role; zero-sorry status; review request. Follow-up on the same project foundation; does not increment the account denominator.

