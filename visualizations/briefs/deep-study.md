# Deep-study deck brief

The `study` deck is for learning, not for fitting a talk slot.  It should become
a coherent curriculum that makes the mathematics, the Lean formalization and
the evidence trail understandable without assuming the viewer already knows
operator perturbation theory.

## Goals

By the end, the maintainer should be able to:

- explain the finite-dimensional geometry behind principal angles;
- derive the role of the residual and the spectral gap in the sine-theta bound;
- understand the vector proof intuition and the Sylvester-equation proof
  mechanism;
- understand what changes in the tan-theta, sin-two-theta and tan-two-theta
  variants;
- read the important pieces of the Lean theorem statement and map them back to
  the mathematics;
- distinguish theorem proving from source-fidelity checking;
- explain the Proposition 4.4 failure and repair;
- state which parts are general operator theory and which pictures are
  finite-dimensional specializations used only for explanation.

## Authoring guidance

Add missing bridge slides when the current material assumes a fact that a
careful non-specialist would not know.  Presenter notes should teach: define the
object, explain why it exists, say what problem it solves, and connect it to the
next step.  Do not merely restate visible equations.

A long deck can still be modular.  Use sections and deck manifests rather than
building one monolithic scene file.  Keep the glossary as reference material,
but introduce notation locally before first use rather than forcing the viewer
to memorize the glossary in advance.
