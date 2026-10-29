# Formalization paper style guide

Use [../STYLE_GUIDE.md](../STYLE_GUIDE.md) for the shared affirmative guidance,
[../BANNED_WORDS_AND_PHRASES.md](../BANNED_WORDS_AND_PHRASES.md) for rhetorical
habits to remove, and [../SPECIFIC_NEGATIVE_PROMPTS.md](../SPECIFIC_NEGATIVE_PROMPTS.md)
for recurring review failures. [AUTHORING_NOTES.md](AUTHORING_NOTES.md) records
this paper's current author decisions and evidence locations.

## Give the abstract and body their own jobs

The abstract summarizes the formalization, foundations, correction, and
follow-on result for a mathematical audience. It can name established theories
and make broad connections concisely. Define the objects and explain the
attribution in the body. Preserve the author's acceptance of that level of
abstraction when applying a request for clearer definitions elsewhere.

Introduce the mathematical problem accessibly in the body. The motivation is
that a perturbation result was needed for DKPS, after which the project pursued
the original Davis--Kahan theorem's generality. Keep that motivation concrete.
The discussion is a possible home for an account of AI's role; its wording and
placement remain an author decision.

## State the formalization contribution plainly

Say what we formalized and what we reused or adapted. Explain the mathematical
content: principal angles, projections, operator ideals, spectral calculus,
and Sylvester estimates. Credit Mathlib, Spectra, and Tau Ceti through their
actual mathematical and formal contributions. Consult the evidence links in
[AUTHORING_NOTES.md](AUTHORING_NOTES.md) when making those statements.

Use a heading such as “Formalized operator-theoretic foundations” when it
identifies the section's contribution. The author also accepts the current
follow-on section heading. Choose each heading for its function.

The selection criterion is the four unnumbered Section 2 headline theorems and
every named theorem, proposition, lemma, and corollary that Davis and Kahan
establish in the 1970 paper. This gives 29 targets: 28 proved statements and
Proposition 4.4 refuted as printed. State that criterion in ordinary language
and refer to the result table. Keep source-correspondence review procedures
and verification bookkeeping in the repository's evidence documents.

## Define the mathematics through its use

Give brief definitions of trial vectors and spaces, intertwining, compression,
polar factors, displacement operators, and operator ideals where the body first
uses them. A reminder of singular values can be short. Explain why a defined
object is needed by the next equation or theorem. For an interval extending to
infinity, give an example showing its finite endpoint and infinite side.

For the correction, first explain full displacement and its difference from
restriction to a subspace. Introduce the competing transporters geometrically
before the block calculation. Give an example of a Q-norm when explaining the
repair. Repeat a short norm-membership reminder where the sine-theta theorem
needs it.

When introducing an acronym, use the full name followed by the acronym in
parentheses. Prefer “trace norm” consistently in this article. Use “range”,
“kernel”, and “domain” consistently; a notation macro can support later typographic choices.

## Keep notation and colors consistent

Use one convention for the original and perturbed operators across the
historical account and theorem statements, with an explicit translation to the
source where needed. Keep the symbol colors aligned with the Manim role
palette. The residual R and rotation R have different roles and can have
different colors. Each argument must also remain readable in monochrome.

Define notation before its substantive use and refer back to nearby definitions.
A short reminder later can help the reader resume a topic. Keep a notation
appendix useful to the current article rather than accumulating slide symbols
that the article does not use.

## Keep figures visual

Use figures for geometry, graphs, concise labels, and numerical comparisons.
Put explanatory sentences and derivations in the caption or adjacent text.
Use the manuscript's LaTeX lettering for mathematical labels and retain live
symbol macros so figure labels support the same glossary reminders as the body.

## State the theorem before its Lean signature

Introduce the shared notation, state the mathematical theorem, and place its
Lean signature immediately afterward. Number these displays “Formalization.”
Explain theorem-specific predicates in mathematical terms. Keep general Lean
syntax in the reader guide and refer to it before the first signature.

Explain the complementary block, its positive modulus, and equality of the
relevant norm values explicitly. Retain genuine scalar-field, domain,
spectral-separation, and norm hypotheses. Describe those hypotheses directly.

## Explain history and new results together

Put an external result's number inside the citation postnote when referring
to it in prose: for example,
`the printed claim \citep[Proposition~4.4]{davis1970rotation}`. Apply this convention to
theorems, propositions, lemmas, and examples from other works. Use
`\cref` for results numbered in this manuscript.

State each predecessor's actual contribution and cite its theorem, proposition,
example, or page when discussing a particular claim. Give publication years
where they support the historical account and its table. The language of an
old publication is unnecessary unless it changes the historical argument.

Distinguish the known complex-phase mechanism from the explicit refutation of
the printed real, small-angle Proposition 4.4. Present the best-supported claim
about an unpublished correction concisely, with the existing mathematical
precursors beside it. Keep exact evidence in author files or source comments.

For the follow-on theorem, explain its optimization objective, matching costs,
and relation to preceding results sufficiently for this paper to be assessed
on its own. Keep references to sibling working manuscripts in author notes.

## Match supporting material to the reader's task

A compact result table can use IDs mapped to Lean declarations in the artifact.
Explain the selection criterion and provide a path to that mapping. Include
columns because they help the reader, rather than because the underlying JSON
contains them. Implementation and source-review evidence remains accessible
through [AUTHORING_NOTES.md](AUTHORING_NOTES.md).

Keep optional resource reporting proportional to the scientific question. If
measurements are included, distinguish incomplete observed telemetry, backfills,
modeled quantities, and extrapolations, with their assumptions and coverage.
Technical measurement and reproduction details can live in artifact documents.

## Keep the AI account at the author's chosen level

Use “ChatGPT and Claude” when naming the systems in ordinary paper prose.
Develop an AI discussion only around the point the author wants to make. A
brief disclosure can remain brief or be consolidated with that discussion.
The previously proposed AI-role paragraph was rejected; preserve that decision
without inventing a more detailed substitute or assigning the author a motive.
