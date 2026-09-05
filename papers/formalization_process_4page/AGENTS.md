# Workshop-paper writing constraints

This directory contains the workshop paper **Who Checks the Formalization?
Human Supervision in LLM-Assisted Lean** and the source notes behind its public
practitioner-account snapshot.

Before editing prose, read and follow:

- `../formalization_draft2/STYLE_GUIDE.md`
- `../formalization_draft2/BANNED_WORDS_AND_PHRASES.md`
- `../formalization_draft2/SPECIFIC_NEGATIVE_PROMPTS.md`

Additional constraints:

1. Related work belongs in Section 2.
2. Ground claims about human practice in the public source notes or the
   Davis--Kahan case study. Avoid generic advice generated from what an LLM
   would like a reviewer to do.
3. Call the source collection a **snapshot of public first-person accounts**.
   Avoid `corpus`, `survey`, `systematic review`, and invented methodology
   labels in the paper.
4. Record only practices and events the source actually reports. Preserve
   `not_reported`, `unclear`, and `qualified`.
5. `data/practitioner_accounts.csv` is the editable account table. Run
   `make sources` to regenerate `notes/practitioner_accounts.md` and
   `generated/practitioner_account_macros.tex`.
6. `data/lean_publication_activity.csv` contains the monthly Papers With Lean
   counts used for the short growth statistic in the introduction.
7. Keep disagreements between practitioners visible. Some read generated Lean
   closely; some use another model to translate or challenge it; some let the
   prover run ahead and study the result later.
8. Treat Git-history counts as a description of this project. Semantic-review
   reversals record reopened correspondence judgments.
9. Keep both author-provided figures and include them with `\includegraphics`.
   The dashboard image may be cropped using LaTeX `trim` / `clip`.
10. Figure 1 names Tau Ceti as a possible destination for reusable foundations,
    so retain a brief accurate explanation and citation.
11. Present EconCSLib, Lean Atlas, ShadowBench, LeanMarathon, FormaTheoria, and
    related systems as adjacent work without priority claims for the local
    dashboard.
12. Keep detailed Davis--Kahan mathematics in `../formalization_draft2/`.
13. Use numeric citations.
14. Main text must fit four workshop pages under the submission template;
    references may follow.
15. The live project repository identifies the authors. Keep
    `\showartifacturlfalse` for double-blind review; switch it on for a public
    preprint or camera-ready copy.
16. Avoid LLM stock contrasts such as “X is not Y; it is Z,” generic taxonomies,
    checklist prose, and rhetorical claims of novelty.
