# Banned words, phrases, and LLM writing habits

These rules apply to manuscript prose, captions, headings, and appendix prose. They are editorial constraints, not suggestions.

## Banned words

Do not use the following words as rhetorical emphasis:

- `matters` (or constructions that say a fact or distinction "matters")
- `silently`
- `quietly`
- `unusually`

Use a concrete consequence instead.

## Banned contrast template

Avoid the formula **"X is not Y; it is Z"** and close variants such as:

- "This is X, not Y."
- "The point is not X but Y."
- "Our contribution is not X; rather, it is Y."
- "This should not be understood as X, but as Y."

Ordinary mathematical negation remains fine when the sentence genuinely requires it. Prefer a direct affirmative description in expository prose.

## Banned slogan style

Avoid slogan-like sentences, taglines, and compressed rhetorical morals. Examples of patterns to replace include:

- dramatic one-line summaries of what the paper "really" shows;
- metaphorical labels for ordinary methodology when literal prose is available;
- punchy oppositions designed mainly for cadence;
- self-congratulatory adjectives about the scale, rigor, novelty, or instrumentation of the work.

State the observation, evidence, consequence, or limitation directly.

## Preferred manuscript style

- Use concrete mathematical nouns and verbs.
- State consequences instead of announcing importance.
- Keep claims proportional to the evidence and name uncertainty directly.
- Keep implementation names and file paths in appendices unless a displayed Lean theorem requires them.
- Use short transitions that describe logical relationships without rhetorical framing.
- When discussing coverage, describe the scoped theory that was developed and known gaps. Avoid field-level completeness percentages without a defensible denominator.
## Reader-facing prose

- Do not leave editorial instructions or future-agent reminders in manuscript prose. Avoid phrases such as "should be repeated before submission", "needs a final refresh", or "final reporting should". State the evidence available at the manuscript date.
- Prefer concrete descriptions of missing observations. Avoid abstract phrases such as "the missingness mechanism" when the omitted source can be named directly.
- Keep coordination-tool history, workflow anecdotes, and implementation provenance out of the paper unless they support a reported scientific result.
- Limit methodological caveats to the assumptions that change interpretation of a reported quantity. Use concise statements of scope.
## Lean code terminology

- Call displayed Lean declarations **code** or **Lean signatures**. Do not call them listings or surfaces.
- Do not call a Lean declaration canonical unless a mathematical uniqueness statement has actually established that term.
- Do not discuss glyph substitutions or other TeX rendering accommodations in manuscript prose.
- Explain non-obvious Lean predicates by stating the mathematical data or hypotheses they encode.
- Use `presentation` only when it denotes a mathematical representation or another substantive technical object; remove prose about choices made merely for the reader-facing layout.

