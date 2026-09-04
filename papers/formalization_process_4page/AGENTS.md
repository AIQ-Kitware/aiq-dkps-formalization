# Workshop-paper writing constraints

This directory contains a four-page workshop experience paper:

**Semantic Auditing for LLM-Assisted Formalization: Lessons from a Davis--Kahan Case Study**

The detailed Davis--Kahan mathematics belongs in `../formalization_draft2/`.

Before editing prose, read and follow:

- `../formalization_draft2/STYLE_GUIDE.md`
- `../formalization_draft2/BANNED_WORDS_AND_PHRASES.md`
- `../formalization_draft2/SPECIFIC_NEGATIVE_PROMPTS.md`

Additional constraints for this paper:

1. Related Work is Section 2. Keep it early in the paper.
2. The paper is a modest practical perspective / experience report for readers
   entering formalization through LLM-assisted tools. Do not turn it into a
   dashboard novelty paper or a controlled-model-evaluation paper.
3. `related_work_semantic_alignment.tex` is the detailed author-reference
   survey. Preserve nuance and close comparisons there.
   `related_work_condensed.tex` is the compact Section 2 used by `paper.tex`.
4. Refresh the detailed memo before making priority claims. The field is moving
   quickly.
5. Treat the Git-history counts as a single-project retrospective description.
   Do not turn them into an LLM error rate or a controlled producer/reviewer
   comparison.
6. Present EconCSLib, Lean Atlas / Compass, ATLAS / AutoformBot, ShadowBench,
   LeanMarathon, FormaTheoria, LeanArchitect, and similar systems as resources
   and comparisons. Some are designed more directly for semantic review than
   the local tooling described here.
7. Use Davis--Kahan as the running case study without reproducing the detailed
   mathematical results, proofs, Proposition 4.4 analysis, or YWS material from
   the longer paper.
8. The workflow emerged during the project. Do not describe it as a method that
   was designed prospectively and then experimentally evaluated.
9. In main-text prose, prefer direct descriptions such as "enumerated source
   results", "review record", "source passage", and "Lean statement" over
   repository bookkeeping labels.
10. The figure `figures/formalization_workflow.png` was provided by the author
    and should remain in the draft unless explicitly replaced.
11. Do not claim that semantic alignment, semantic critics, adversarial target
    review, provenance, blueprint synchronization, statement immutability, or
    semantic-review dashboards are new in general.
12. The local dashboard is one implementation of accumulated practical needs:
    source context, clause-level correspondence, compiler-derived Lean evidence,
    representation bridges, and review invalidation after source/statement
    changes. Describe those features concretely without implying priority.
