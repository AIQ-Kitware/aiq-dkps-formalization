# Workshop-paper writing constraints

This directory contains the workshop paper **Did We Really Formalize
Davis--Kahan?** and the source notes used while drafting it.

Before editing prose, read and follow:

- `../formalization_draft2/STYLE_GUIDE.md`
- `../formalization_draft2/BANNED_WORDS_AND_PHRASES.md`
- `../formalization_draft2/SPECIFIC_NEGATIVE_PROMPTS.md`

Additional constraints:

1. Related work belongs in Section 2.
2. Ground claims about human practice in the public source notes or the
   Davis--Kahan case study. Avoid generic advice generated from what an LLM
   would like a reviewer to do.
3. Describe `data/practitioner_accounts.csv` plainly as public first-person
   accounts found through LLM-assisted web search. Do not call this small
   collection a corpus, survey, systematic review, or methodology.
4. Record only practices and events the source actually reports. Preserve
   `not_reported`, `unclear`, and `qualified`.
5. Run `make sources` after editing the account table to regenerate
   `notes/practitioner_accounts.md` and
   `generated/practitioner_account_macros.tex`.
6. `data/lean_publication_activity.csv` contains the monthly Papers With Lean
   counts used for the short growth statistic in the introduction.
7. Keep disagreements between practitioners visible. Some read generated Lean
   closely; some use another model to translate or challenge it; some let the
   prover run ahead and study the result later.
8. Treat the Git chronology as a description of this project. In the main paper,
   describe concrete source-to-Lean mismatches and repairs rather than internal
   status transitions or ledger vocabulary.
9. The current 29/29 state is provisional. Say that we think all 29 Davis--Kahan
   source results are covered at the intended scope, or are very close. Do not
   turn the current accepted rows into a certainty claim.
10. Keep the workflow figure as Figure 1. Binary render outputs (PNG, PDF,
    ZIP, etc.) are local artifacts only and must never be staged or committed.
    The dashboard screenshot is an untracked appendix render.
11. Figure 1 names Tau Ceti as a possible destination for reusable foundations,
    so retain a brief accurate explanation and citation.
12. The worked example is the historical directed sin-2-Theta correspondence
    failure: one checked theorem had the printed trial residual but only bounded
    complex scope, while another had unbounded scope but a reflection residual
    rather than the printed trial residual. The main text may show a compact
    generated scope comparison, but full historical Lean signatures stay in the
    candidate note. The historical witness comes from commit `7001ed05`; current
    source-facing endpoints use `NormalizedUnitaryInvariantNorm`, while internal
    proof theorems may use `SymmetricNormingFunction`.
13. Present EconCSLib, Lean Atlas, ShadowBench, LeanMarathon, FormaTheoria, and
    related systems as adjacent work without priority claims for the local
    dashboard.
14. Keep detailed Davis--Kahan mathematics in `../formalization_draft2/`.
15. Use numeric citations.
16. Main text must fit four workshop pages under the submission template;
    references may follow.
17. The live project repository identifies the authors. Keep the default
    `paper.tex` build anonymous; use `paper_public.tex` for a public preprint or
    camera-ready copy.
18. `brainstorm.md` preserves the original notes and a verbatim human prompt
    log. Never clean up spelling, punctuation, capitalization, or wording inside
    those prompt blocks. Add only short bracketed context when the prompt would
    otherwise be unintelligible. Do not reconstruct missing prompts from
    summaries.
19. Avoid LLM stock contrasts such as “X is not Y; it is Z,” generic taxonomies,
    checklist prose, slogans, and rhetorical claims of novelty.
20. Do not include the review-stopping Poisson/Bayesian model unless a future
    study records comparable review exposure. The current historical logs do not
    support fitting that model to this project.
21. Chow's doohickey example is illustrative. Do not describe it as silly or
    otherwise belittle the example.
22. Keep full historical Lean signatures in the generated candidate note rather
    than forcing a large Unicode-heavy listing into the four-page PDF. A compact
    generated scope table is acceptable in the main text when it makes the
    mismatch visible without fragile Lean notation.
23. Section titles should describe their contents directly. Avoid evaluative or
    slogan-like headings such as "still too narrow" and rhetorical mini-lessons.

- `notes/SEMANTIC_ALIGNMENT_CANDIDATES.md` is generated evidence. Do not hand-edit its Lean snippets; update `scripts/build_semantic_alignment_candidates.py` and run `make sources`.
