# Completed Kitware talk brief

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

## Opening overview

Immediately after the title, the Kitware manifest includes a single, static
`W00Overview` scene. It gives the audience the destination before teaching the
notation: Davis and Kahan's 1970 paper and a representative sine-theta bound;
DARPA AIQ's need for the theorem; the upstream-quality motivation for reaching
full operator-theoretic source scope; the timeline from January--May 2026
exploration, through serious progress in June and the intensive July--August
formalization push, to September--October polish; semantic alignment and agent orchestration as distinct
challenges; and the October 2026 status of Palomar, TauCetiRoadmap and ongoing
Hilbert-space operator-theory ports.
The Hilbert-space operator-theory ports are underway and first PRs have landed.
Treat the October statuses as dated, presenter-supplied snapshots, not permanent
repository facts. Keep the original presentation intact.

The overview now includes a **Developments** section: six classical operator-theory
prerequisite areas that required new or generalized Lean interfaces (not a claim
that every declaration in these areas was first-of-its-kind), and an
**What the foundations enable** section that explicitly identifies future
mathematical research in functional analysis (new Hilbert-space theorems) as
well as downstream applications such as statistical PCA and numerical
eigensolvers, and spectral reasoning about self-adjoint Hamiltonians in
mathematical physics. These are possibilities enabled by reusable foundations, not
claims that those downstream projects are completed. The source journal
identifies the six areas; some Spectra foundations were adapted or generalized,
with attribution retained. The formalization scope is the major statements
explicitly proved in the original paper. A separate **Challenges** box covers the
semantic-alignment problem and agent orchestration: multi-stage work,
handoffs, and review cycles.

## Narrative spine

The `dkvis.decks.kitware_talk.KITWARE_TALK` scene order is the completed October 2026 talk and must remain stable. Experimental or long-form changes belong in `comprehensive`.
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

The kitware-talk deck deliberately switches viewpoints.  The audience should never have to infer which one is active.

- Slides motivating instability should visibly identify themselves as **PERTURBATION SETUP** and use `A`, `H`, and `A-hat = A + H`.
- Slides defining angle, residual, spectral separation, and the theorem should visibly identify themselves as **GENERAL THEOREM SETUP**.  `Ahat` is simply the operator under study there; `E0,A0` are the trial pair and `F0,F1` exact frames.  Do not imply an `H` exists.
- Immediately after the theorem, a **PERTURBATION SPECIALIZATION** slide must reconnect the stories without changing symbol meanings: original `A`, `Ahat = A + H`, `A E0 = E0 A0`, hence `R = H E0` and `||R|| <= ||H||`.
- Keep `g` and `delta` distinct: `g` is an original eigengap of `A`; `delta` is the Davis--Kahan separation between the trial spectrum and the exact unwanted spectrum of `Ahat`.

Use the centralized notation/color table for every mathematical object.  Do not color the same symbol ad hoc on individual slides.

## Ending

The "What to take away" slide is organized around three lessons:

1. LLMs can sustain a serious Hilbert-space functional-analysis formalization:
   all 29 selected source results were addressed, 28 proved at the source scope,
   the remaining printed proposition refuted and repaired.
2. Sine-theta intuition: a small perturbation/residual gives a small eigenspace
   error *when there is adequate certified spectral separation*. This is useful
   even when the underlying true eigenspace is latent.
3. LLM-assisted source review located a counterexample to the 1970 paper's
   all-unitarily-invariant-norm version of Proposition 4.4. Its consequence is
   restricted: for acute pairs, direct rotation retains its full-displacement
   minimality for Q-norms such as the operator and Frobenius norms, without the
   printed 60-degree limit and also over complex spaces. Do not imply the
   full printed claim was commonly used incorrectly downstream.

The kitware-talk deck retains `S14Summary` and finishes with exactly one
`V01VTKFinale` scene: a full-frame looping VTK movie (the 3D sine-theta model,
not the 4D Proposition 4.4 witness). Its "Visualization rendered with VTK"
credit is burned into the movie itself. Do not add a still-image intro,
`FadeIn`, title card, or any other preliminary build to this scene; a
`next_slide(src=...)` is already one complete slide. The Manim 3D experiment
was removed from the Kitware presentation. The study and reference decks stay
unchanged.

The concluding sine-theta explanation should say "residual norm divided by
spectral separation" rather than a vague ratio slogan. In the theorem slide,
style "PERTURBATION SPECIALIZATION" with the same warm perturbation role color
as the corresponding specialization slide.

The 2D+2D Proposition 4.4 comparison owns the numerical counterexample; the
following `P04LeanRefutation` scene uses literal Lean source text and explains
the independently checked Q-norm repair. Do not duplicate the Lean repair note
on the numerical counterexample slide.
