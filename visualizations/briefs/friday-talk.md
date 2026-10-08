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
- perturbation and instability without a gap;
- principal angle, residual and gap;
- the sine-theta inequality and why it works;
- the corresponding Lean statement;
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
