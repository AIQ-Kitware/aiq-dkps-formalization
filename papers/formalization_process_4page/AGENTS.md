# Workshop-paper writing constraints

This directory contains the workshop paper **Did We Really Formalize
Davis--Kahan? Semantic Alignment for LLM-Assisted Lean Formalization** and the source notes used while drafting it.

Before editing prose, read and follow:

- `../formalization_draft2/STYLE_GUIDE.md`
- `../BANNED_WORDS_AND_PHRASES.md`
- `../SPECIFIC_NEGATIVE_PROMPTS.md`

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
8. Treat the detailed Git chronology as supporting evidence rather than the
   organizing spine of the main paper. Use a specific review episode only when
   it directly supports a manuscript claim. The result ledger may be introduced
   as an organizational tool for fixing counted source targets, intended scope,
   Lean evidence, and review state; avoid internal Git status jargon.
9. Keep the current source-review state accurate without turning a successful
   review into a semantic-completeness claim. Distinguish the latest review
   result from independent replication when that distinction affects a claim.
10. Keep the workflow figure as Figure 1. Binary render outputs (PNG, PDF,
    ZIP, etc.) are local artifacts only and must never be staged or committed.
    The dashboard screenshot is an untracked appendix render.
11. Figure 1 names Tau Ceti as a possible destination for reusable foundations,
    so retain a brief accurate explanation and citation.
12. The worked example is the historical directed sin-2-Theta correspondence
    failure: one checked theorem had the printed trial residual but only bounded
    complex scope, while another had unbounded scope but a reflection residual
    rather than the printed trial residual. Show the historical theorem statement
    in the paper, generated from commit `7001ed05`; names may be adjusted for
    readability when the transformation is verified and documented in the
    generator. Full exact historical signatures stay in the candidate note.
    `PaperUnitaryInvariantNorm` was renamed to `SymmetricNormingFunction` in
    commit `a905bd4c`; current source-facing endpoints use
    `NormalizedUnitaryInvariantNorm`.
13. Present EconCSLib, Lean Atlas, ShadowBench, LeanMarathon, FormaTheoria, and
    related systems as adjacent work without priority claims for the local
    dashboard.
14. Keep detailed Davis--Kahan mathematics in `../formalization_draft2/`.
15. Use numeric citations.
16. The VeriCodeGen main text must be 4--9 pages under the supplied
    `neurips_2026_vericode.sty`; references, checklist, and optional technical
    appendices do not count toward that limit. Do not modify the supplied style.
17. The live project repository identifies the authors. Keep the default
    `paper.tex` build anonymous with the VeriCodeGen submission style; use
    `paper_public.tex` with the style's `preprint` option for a public preprint.
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
22. Keep the exact historical Lean signature in the generated candidate note and
    generate the shorter theorem statement shown in the paper from that evidence.
    Avoid fragile Unicode notation in the PDF by using verified readability-only
    identifier/notation adjustments in the generated display.
23. Section titles should describe their contents directly. Avoid evaluative or
    slogan-like headings such as "still too narrow" and rhetorical mini-lessons.

- `notes/SEMANTIC_ALIGNMENT_CANDIDATES.md` is generated evidence. Do not hand-edit its Lean snippets; update `scripts/build_semantic_alignment_candidates.py` and run `make sources`.

24. Keep the Theorem 8.1(ii) over-correction grounded in the recorded review sequence. Do not promote it into a generic failure taxonomy or novelty claim.
25. The workshop checklist is required. Keep its questions and guideline text unchanged; update only answers and justifications as the paper changes.
