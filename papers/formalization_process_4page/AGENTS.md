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
5. Record additions considered for `data/practitioner_accounts.csv` in
   `data/practitioner_account_screening.csv`. Keep structured studies,
   related-work-only sources, duplicates, and exclusions in the screening log
   without forcing them into the practitioner count. The screening log begins
   on 8 September 2026 and is not claimed to reconstruct earlier rejected
   candidates.
6. Run `make sources` after editing the account table or screening log to regenerate
   `notes/practitioner_accounts.md` and
   `generated/practitioner_account_macros.tex`.
7. `data/lean_publication_activity.csv` contains the monthly Papers With Lean
   counts retained as appendix context. Do not spend main-text space on the
   growth statistic unless it becomes necessary to the argument.
8. Keep disagreements between practitioners visible. Some read generated Lean
   closely; some use another model to translate or challenge it; some let the
   prover run ahead and study the result later.
9. Treat the detailed Git chronology as supporting evidence rather than rendered
   exposition. Use a specific review episode only when it directly supports a
   manuscript claim. Do not render a commit-by-commit chronology table merely
   because the data are available; keep the detailed sequence in
   `data/review_timeline.csv` and source comments. The result ledger may be
   introduced as an organizational tool for fixing counted source targets,
   intended scope, Lean evidence, and review state; avoid internal Git status jargon.
10. Keep the current source-review state accurate without turning a successful
   review into a semantic-completeness claim. Distinguish the latest review
   result from independent replication when that distinction affects a claim.
11. Keep the existing formalization workflow figure as Figure 1. Preserve its
    design and content; do not redraw or replace it merely to make prose labels
    match. The paper uses the existing `figures/formalization_workflow.png`
    artifact. The dashboard screenshot is an untracked appendix render.
12. Figure 1 should remain project-neutral and should not name Tau Ceti or local
    helper tools. Introduce Tau Ceti later in the main text, with an accurate
    explanation and citation, when the reusable foundations are discussed.
13. The worked example is the historical ambient sin-2-Theta semantic
    mismatch present at the 17 August 2026 checkpoint. Real and complex directed
    residual witnesses already covered the unbounded scope, and real and complex
    ambient witnesses existed, but the ambient witnesses were bounded. The old
    certificate combined unbounded scope from the directed clause with the ambient
    conclusion from a different bounded theorem. Show the historical complex
    ambient theorem with its bounded section context; do not describe scalar
    coverage as the defect. Keep the 12/17/31 August review chronology, Palomar
    reorganization, later gap-placement repair, and exact commit provenance in
    source comments, appendix evidence, or generated metadata unless a rendered
    claim specifically depends on them. `PaperUnitaryInvariantNorm` was renamed
    to `SymmetricNormingFunction` in commit `a905bd4c`; current source-facing
    endpoints use `NormalizedUnitaryInvariantNorm`.
14. Present EconCSLib, Lean Atlas, ShadowBench, LeanMarathon, FormaTheoria, and
    related systems as adjacent work without priority claims for the local
    dashboard.
15. Keep detailed Davis--Kahan mathematics in `../formalization_draft2/`.
16. Use numeric citations.
17. The VeriCodeGen main text must be 4--9 pages under the supplied
    `neurips_2026_vericode.sty`; references, checklist, and optional technical
    appendices do not count toward that limit. Do not modify the supplied style.
18. The live project repository identifies the authors. Keep the default
    `paper.tex` build anonymous with the VeriCodeGen submission style; use
    `paper_public.tex` with the style's `preprint` option for a public preprint.
19. `brainstorm.md` preserves the original notes and a verbatim human prompt
    log. Never clean up spelling, punctuation, capitalization, or wording inside
    those prompt blocks. Add only short bracketed context when the prompt would
    otherwise be unintelligible. Do not reconstruct missing prompts from
    summaries.
20. Avoid LLM stock contrasts such as “X is not Y; it is Z,” generic taxonomies,
    checklist prose, slogans, and rhetorical claims of novelty.
21. Do not include the review-stopping Poisson/Bayesian model unless a future
    study records comparable review exposure. The current historical logs do not
    support fitting that model to this project.
22. Chow's doohickey example is illustrative. Do not describe it as silly or
    otherwise belittle the example.
23. Keep the exact historical Lean signature as a generated sidecar and generate
    the shorter theorem statement shown in the paper from that exact evidence.
    The file consumed by `listings` must use unique ASCII `LeanLit...` sentinels
    for display-sensitive Lean Unicode; `paper.tex` maps those sentinels to LaTeX
    with `literate=`. Do not put literal Lean Unicode on the left-hand side of
    `literate=`, and do not replace Lean notation by verbose ASCII API spellings
    merely to make `listings` work. The generated presentation file must point to
    the exact sidecar and state that it is presentation-only. This indirection is
    deliberate: it preserves auditable exact Lean while avoiding listings/Overleaf
    Unicode failure modes that have previously been reintroduced by automated edits.
24. Section titles should describe their contents directly. Avoid evaluative,
    causal, or slogan-like headings such as "still too narrow" or "How X passed
    review too early". For a worked mismatch, prefer a literal title such as
    "Example of a semantically misaligned statement."

- `notes/SEMANTIC_ALIGNMENT_CANDIDATES.md` is generated evidence. Do not hand-edit its Lean snippets; update `scripts/build_semantic_alignment_candidates.py` and run `make sources`.

25. Keep the Theorem 8.1(ii) over-correction grounded in the recorded review sequence. Do not promote it into a generic failure taxonomy or novelty claim.
26. The workshop checklist is required. Keep its questions and guideline text unchanged; update only answers and justifications as the paper changes.
27. Describe the formalization procedure in the main text from the researcher's
    point of view: how source targets were fixed, what the agents implemented,
    what Lean and scripts checked mechanically, what humans reviewed, and how
    correspondence decisions were retained. Prefer a short bullet sequence to a
    component/interface table. Put repository paths, exact dependency revisions,
    checker names, and other reproduction details in the appendix. Do not copy
    the workflow breakdown into the abstract or conclusion.

28. Do not announce importance before stating a fact. Delete sentences such as
    "The chronology is important here," "A key point is," or "It is important to
    note." If the sentence carries no information, remove it; otherwise state the
    concrete fact or consequence directly.
29. Use non-rendered LaTeX comments for editor-facing provenance that is useful
    during revision but not part of the scientific exposition: dates, commits,
    review-state transitions, why a wording changed, and alternative historical
    interpretations. Do not promote those notes into rendered prose by default.
30. Keep Section 2 as Related Work. The main formalization-process section comes
    after "What we formalized" and should refer back to Figure 1.
31. The process bullets correspond to Figure 1 without requiring one-to-one box
    labels. **Gather Context** summarizes the Inputs panel; **Decompose** and
    **Find Foundations** match their boxes; **Formalize** includes both the
    Formalize and Compile & Revise boxes; **Skeptical Review** corresponds to the
    Skeptical Critic. Preserve the existing figure rather than changing it to fit
    the prose.
32. In anonymous main-text prose, describe local maintenance/query tooling by
    function rather than product name. Exact helper-tool names and repository
    interfaces belong in the appendix or supplementary artifact.
33. For this project's model disclosure, do not distinguish the ChatGPT and
    Codex interfaces. Refer to them collectively as ChatGPT. Preserve product
    names when accurately reporting a cited practitioner's workflow.
34. Introduce Tau Ceti before naming it in rendered prose. Do not put Tau Ceti
    in Figure 1. The first main-text mention should identify it as an AI-authored
    Lean library downstream of Mathlib and cite it.
35. State the loop and exit criterion in prose after the five process bullets.
    Refactoring/reorganization is part of maintaining reusable foundations as
    the project grows, not another figure stage. Completion of a target requires
    both a checked formal treatment and a separate source-to-statement review;
    non-obvious representation correspondences must also be established.
