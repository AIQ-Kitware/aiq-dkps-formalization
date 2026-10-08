# Friday talk brief

## Audience and outcome

The audience knows that a large mathematical paper was formalized with heavy LLM
assistance, but they do not yet understand the mathematics or what the
formalization establishes.  The talk should leave them able to explain:

1. the geometric question behind Davis--Kahan: how far can an eigenspace move?;
2. why angle/error, residual and certified spectral separation are the three quantities in the
   sine-theta theorem;
3. the intuitive content of `error <= residual / separation`;
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
- **general theorem language:** temporarily stop assuming an `H` exists.  Use `Ahat` for the operator under study, the trial pair `(E0,A0)`, exact frames `F0,F1`, residual `R = Ahat E0 - E0 A0`, and spectral separation `delta`; do not add `U,V` names for the frame ranges;
- state `delta ||sin Theta0(E0,F0)|| <= ||R||`, explicitly noting that the general theorem does not require `Ahat = A + H`;
- **return immediately to perturbations:** keep `A` fixed as the original operator, set `Ahat = A + H`, choose `E0,A0` from an exact wanted eigensystem of original `A`, derive `R = H E0`, and state `||R|| <= ||H||`; this is the bridge from residual-over-separation to perturbation size over separation;
- explain why the general residual-over-separation theorem works;
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

- Slides motivating instability should visibly identify themselves as **PERTURBATION SETUP** and use `A`, `H`, and `A-hat = A + H`.
- Slides defining angle, residual, spectral separation, and the theorem should visibly identify themselves as **GENERAL THEOREM SETUP**.  `Ahat` is simply the operator under study there; `E0,A0` are the trial pair and `F0,F1` exact frames.  Do not imply an `H` exists.
- Immediately after the theorem, a **PERTURBATION SPECIALIZATION** slide must reconnect the stories without changing symbol meanings: original `A`, `Ahat = A + H`, `A E0 = E0 A0`, hence `R = H E0` and `||R|| <= ||H||`.
- Keep `g` and `delta` distinct: `g` is an original eigengap of `A`; `delta` is the Davis--Kahan separation between the trial spectrum and the exact unwanted spectrum of `Ahat`.

Use the centralized notation/color table for every mathematical object.  Do not color the same symbol ad hoc on individual slides.
