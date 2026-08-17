# Formalization paper style guide

This guide describes the prose and structure we want for the manuscript. It is affirmative: use it to decide how to write. See [BANNED_WORDS_AND_PHRASES.md](BANNED_WORDS_AND_PHRASES.md) for constructions and vocabulary to remove.

## Write for a mathematical reader

Write as the authors of the work, addressing readers who care about the mathematics, the formalization, and the evidence. State what we proved, formalized, adapted, measured, or found. Prefer the mathematical fact to the project-management story that produced it.

Use concrete nouns and verbs. Give the theorem, construction, counterexample, formal dependency, measurement, or limitation directly. A caveat should identify the assumption or missing observation that changes how a result is interpreted.

Keep the main text focused on the scientific claims. Put exact file paths, Lean declaration inventories, registry mechanics, generator details, and audit bookkeeping in the appendices.

## Organize around mathematical claims

Lead sections with the mathematical question or result. Let the source theorems provide the organizational spine of the exposition.

For theorem-to-Lean comparisons:

1. introduce shared mathematical notation before the theorem-specific subsection;
2. state the mathematical theorem or inequality;
3. place the corresponding Lean signature immediately after it;
4. explain only the Lean predicates whose mathematical meaning is not evident from the signature;
5. continue with the mathematical interpretation or consequence.

Keep the short general guide to Lean syntax in the appendix. Refer readers there before the first displayed Lean signature. Around each theorem, explain only the mathematical meaning specific to that theorem.

The Davis--Kahan and YWS coverage claims should be stated at the strongest scope supported by the source audit. Define detailed denominators and correspondence rules in the appendix.

## Explain Lean in mathematical language

Call a displayed declaration **code** or a **Lean signature**. Describe bundled predicates by the mathematical assumptions they encode. For example, explain that a predicate supplies an exact spectral decomposition or a residual relation.

Captions should say that surrounding Lean context is omitted when appropriate and should help a reader map the important arguments and hypotheses to the mathematical statement.

The main body should contain only Lean names needed for the displayed theorem signatures. Move additional declaration names and code-level evidence to the appendix.

## Present formalization coverage as a contribution

State the complete Davis--Kahan result coverage and the narrower YWS coverage explicitly. Explain what full generality means where needed: real or complex Hilbert spaces, infinite-dimensional settings, unbounded self-adjoint operators, or arbitrary unitarily invariant norms when those are part of the source statement.

Treat formalization as a source audit by explaining the mechanism briefly: each hypothesis, boundary convention, and intermediate identity must support a checked derivation, which can expose algebraic errors, boundary failures, and false extremal claims. Then discuss the actual defects found.

## Describe foundational work through the mathematics

When motivating the project, note that formalizing DK and YWS required substantial mathematical infrastructure that was absent from the available Lean library and can support later formalizations.

In the foundations section, begin with the gap between the source statements and the available formal library. Name the basic theory areas that were developed and describe their scope in mathematical terms. Use declaration graphs and module classifications as supporting evidence in the appendix.

Describe coverage with scoped qualitative language such as focused interface, focused development, substantial reusable development, or broad partial development. State known omissions when they affect the interpretation.

## Give formal ancestry directly

Credit prior formal work by saying what came from it. If part of the PVM or self-adjoint infrastructure was copied, ported, adapted, generalized, or used as a reference from Spectra or another Lean development, say so directly and cite the source.

Treat mathematical provenance and formal ancestry as ordinary scholarly attribution. The main text should contain the ancestry that affects credit or helps readers understand the development; declaration-level attribution tables can remain in the appendix.

## Keep source-audit bookkeeping in the appendix

Use the main text to state the coverage result and the mathematical consequences. Put census construction, exact source-unit counts, correction/extension bookkeeping, correspondence tables, and declaration-level evidence in a concise appendix section with explicit cross-references from the main text.

When referring readers to supplementary material, use an explicit section or appendix reference.

## Report resource use in layers

Separate directly observed telemetry from quantities inferred with a model and from project-scale extrapolations.

Use **lower bound** in the header and caption of every table containing incomplete observed telemetry so a skim reader cannot mistake those values for project totals. State the fraction of the project represented by the observations using transparent denominators such as commit coverage and cumulative Lean-line churn.

Keep modeled operational energy in kWh separate from observed token counts. Put model assumptions, cache pricing, ledger schema, and other reproduction details in the appendix. Keep coverage-scaled project estimates in columns or tables distinct from observed lower bounds and state the scaling assumption concisely.

The abstract should emphasize directly observed quantities and their coverage. Reserve modeled cost, emissions, energy, and extrapolated totals for the body unless they become sufficiently well established to support a headline claim.

## Describe the formalization process concisely

The methods appendix should state the tools and workflow in ordinary research language. The project used Lean 4 and Mathlib through the ChatGPT chat interface, Claude Code, and Codex.

Describe the recurring process as source transcription, decomposition into intermediate obligations, search for existing mathematical and formal results, Lean implementation, compiler-driven proof repair, and repeated source comparison by humans and LLMs. Explain that source-coverage tooling was added as the project grew.

Keep workflow detail only when it helps another researcher understand or reproduce the method.

## Use citations as part of the argument

Store bibliographic metadata in `references.bib` and use the real published record when available. Cite mathematical sources where their results enter the argument and formal sources where their Lean work was reused or adapted.

Related work should compare scientific approaches. When discussing alternative formalization frameworks such as MathCode or AutoLean, state the aspect of workflow that creates a useful comparison with this project.

## Handle uncertainty briefly

State the best-supported claim and the uncertainty that changes it. For a literature search, a concise formulation such as "To the best of our knowledge..." is enough when the search has not found a prior correction.

For incomplete telemetry, name the observed fraction and call the measured totals lower bounds. For modeled quantities, identify them as estimates and give the assumptions or sensitivity that governs interpretation.

State the evidence available at the manuscript date and phrase literature-search conclusions at that scope.

## End sections with results or questions

Use conclusions and transitions to summarize mathematical results, empirical findings, or research questions. The resource section can close by asking whether alternative AI formalization workflows reduce token and energy costs under comparable mathematical obligations. The conclusion should return to the formalized results, the defects exposed, the reusable theory developed, and the open efficiency question in compact form.
