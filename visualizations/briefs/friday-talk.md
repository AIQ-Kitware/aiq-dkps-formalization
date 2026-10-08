# Friday talk brief

## Audience and outcome

The audience knows that a large mathematical paper was formalized with heavy LLM
assistance, but they do not yet understand the mathematics or what the
formalization establishes.  The talk should leave them able to explain:

1. the geometric question behind Davis--Kahan: how far can an eigenspace move?;
2. why angle/error, residual and spectral gap are the three quantities in the
   sine-theta theorem;
3. the intuitive content of `error <= residual / gap`;
4. what Lean's kernel checked and, separately, what source-fidelity review had
   to establish;
5. why the Proposition 4.4 episode is evidence that this distinction matters;
6. what confidence is justified by the project and what still requires human
   judgment.

This is not a claim that Lean proved the whole printed paper correct.  The
project itself contains a formally refuted printed proposition.

## Narrative spine

Treat `dkvis.decks.friday.FRIDAY` as a working hypothesis, not a sacred order.
A good progression is:

- what was attempted and how the formalization loop worked;
- a visual introduction to eigenvectors/eigenspaces;
- **perturbation motivation:** start with `A`, add `H`, and watch the eigenspace of `A + H` move;
- **general theorem language:** temporarily stop assuming an `H` exists and define principal angle, residual, and spectral gap for a matrix/operator `A~` and a trial subspace;
- state the general sine-theta inequality `error <= residual / gap`, explicitly noting that it does not require `A~ = A + H`;
- **return immediately to perturbations:** choose the old eigenspace of `A` as the trial for `A~ = A + H`, derive `R = H E0`, and state in words that `||R|| <= ||H||`; this is the bridge from residual-over-gap to perturbation-over-gap;
- explain why the general residual-over-gap theorem works;
- show the corresponding Lean statement;
- proof checking versus statement/source checking;
- evidence from reversals and re-review;
- Proposition 4.4: plausible printed claim, counterexample, repaired statement;
- careful conclusions about confidence.

Prefer a shorter coherent talk over touching every component.  Keep omitted
technical material available in the study/reference decks for questions.

## Epistemic language

Separate these claims:

- Lean accepted a formal proposition under its listed assumptions.
- The formal proposition was compared against a particular source statement.
- Numerical examples/visualizations agree with the theorem in tested cases.
- Repeated skeptical reviews failed to find another mismatch at a particular
  snapshot.

Do not collapse those into a single statement that "the paper was proven
correct."

## Visual standard

Use motion only where change communicates the idea: rotating subspaces,
closing a gap, adding a perturbation, decomposing a residual, or comparing two
statements.  Static explanations should be fully visible without waiting for a
sequence of decorative fades.  Every final build must be complete enough for a
handout page.

## Keep the two viewpoints visually distinct

The Friday deck deliberately switches viewpoints.  The audience should never have to infer which one is active.

- Slides motivating instability should visibly identify themselves as **PERTURBATION SETUP** and use `A`, `H`, and `A~ = A + H`.
- Slides defining angle, residual, gap, and the theorem should visibly identify themselves as **GENERAL THEOREM SETUP**.  These concepts apply to `A~` and a trial subspace without assuming that `A~` arose by adding an `H`.
- Immediately after the theorem, a **PERTURBATION SPECIALIZATION** slide must reconnect the two stories: old eigenspace of `A` as the trial, `R = H E0`, hence `||R|| <= ||H||`.

Use the centralized notation/color table for every mathematical object.  Do not color the same symbol ad hoc on individual slides.
