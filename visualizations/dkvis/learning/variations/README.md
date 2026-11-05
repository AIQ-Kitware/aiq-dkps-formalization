# Feasible variations and stationarity

A lecture in [the prerequisite series](../PREREQUISITES.md).

**Audience:** the preceding two lectures, product-rule differentiation, and trace.
**Goal:** construct exact feasible motions through an arbitrary transporter and
derive the vanishing of both diagonal gradient compressions at a minimizer.

The eleven scenes in `scenes.py` use [lecture.md](../../../lectures/README.md#variations). A short context
introduces [Euler's 1744 calculus-of-variations work](https://scholarlycommons.pacific.edu/euler-works/65/).
The actual finite-matrix construction and trace-gradient argument are derived
in modern notation, following the manuscript matching proof. Numerical source
motions reuse `learning/matching/model.py` and its checked examples.

The narrative proceeds from the tangent velocity to its exponential, then
source preservation, feasible right composition, stationarity, the trace
pairing, and the tests `B = P G P` and `B = P^perp G P^perp`. The planar gradient
example spells out the negative sign and factor of two.

The recap explicitly separates conditions on B, G and W: neither `W P = P W`
nor global optimality follows merely from stationarity. The next step toward
matching is the common-block decomposition, taught in the full matching study.

Build with `make slides DECK=prereq-variations` from `visualizations/`.
