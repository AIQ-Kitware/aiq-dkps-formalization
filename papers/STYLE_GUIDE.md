# Paper writing style

Use this guide for affirmative writing choices throughout `papers/`. Read it
with [BANNED_WORDS_AND_PHRASES.md](BANNED_WORDS_AND_PHRASES.md) and
[SPECIFIC_NEGATIVE_PROMPTS.md](SPECIFIC_NEGATIVE_PROMPTS.md). A manuscript's
local guide adds its audience, scientific scope, and author decisions.

## Match the detail to the part of the paper

An abstract gives the research question, contributions, and high-level context.
It may name established mathematical objects without defining them and summarize
several contributions in one sentence. Technical accuracy applies throughout;
the body supplies definitions, hypotheses, proof explanations, and comparisons.

An introduction explains why we undertook the work and what the reader will
learn. Give enough mathematics to make that motivation intelligible. Develop
the historical account where it explains the results or their prerequisites.

A discussion interprets the results and considers questions supported by the
work. An acknowledgment or disclosure can be brief. An appendix has a specific
purpose, such as a notation reference or result table. Choose what belongs in
each part by what its reader needs there.

## Use ordinary, consistent language

Write as the authors: we proved, formalized, adapted, or used a result. Use the
same term for the same mathematical object. Repeating a precise word is useful;
varying it for rhetorical effect makes the reader check whether its meaning
changed. Prefer “we prove” to “we exhibit a proved reduction.”

State the actual relationship between results. For example, explain which
operator satisfies which equation, or which estimate bounds which error.
Connect paragraphs through those mathematical relationships. Use headings that
tell readers what a section contains; a heading may identify a formalization
contribution or a follow-on result when that is the section's purpose.

## Give definitions and enough intuition

Write for a mathematical reader whose specialty may differ from ours. Define
the technical objects used in the argument at their first substantive use in
the body. Pair a definition with a short explanation or example when that
makes its role clearer. A reminder of a standard concept may take one sentence.
Expand where the subsequent argument needs more understanding.

For example, an interval with one finite endpoint can be illustrated by
`(-infinity, a]`; switching between “half-line” and “half-infinite interval”
alone supplies no additional explanation. A trial vector can be introduced as
a proposed approximate eigenvector before stating its residual equation.

Keep notation consistent across sections and translate source notation when
necessary. Reuse a definition already established nearby. A short reminder
later can help readers resume an argument after a substantial interruption.
Introduce an acronym as “full name (ACRONYM).”

## Explain the contribution and its predecessors together

State what was formalized, what mathematical result was obtained, and which
earlier results make the comparison meaningful. Distinguish a known mechanism
from a newly identified error in a particular published claim. Cite the
relevant theorem, proposition, example, or page when discussing that claim.

Use a concise qualification such as “to the best of our knowledge” when it
accurately describes a literature finding. Support the comparison with evidence
in the author files. Keep the published mathematical account self-contained
at the level needed to understand and assess its included results.

## Keep supporting evidence accessible to authors

Use paper-directory notes and non-rendered LaTeX comments for exact provenance,
source locations, implementation details, and editorial decisions. Link to
existing evidence rather than making competing copies. The rendered paper
contains the mathematical facts and scholarly attribution supported by that
evidence. Include a table or appendix when it serves a reader's task; compact
IDs are useful when an artifact provides their mapping to the source and code.

## Apply review feedback with its context

Separate an author's lasting preference from a decision about one passage.
Record rejected suggestions and qualified agreements as carefully as accepted
ones. Preserve an accepted broad summary in the abstract while improving the
definitions in the body. A request to simplify some headings does not require
renaming every heading.

During a review round, use the requested comment macros and keep proposed
changes reviewable. Before removing notes, preserve the decisions and evidence
needed for the correction pass. Keep reusable macro definitions available for
later rounds when requested.
