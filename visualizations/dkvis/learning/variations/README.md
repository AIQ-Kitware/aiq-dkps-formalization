# Feasible variations and stationarity

A lecture in [the prerequisite series](../PREREQUISITES.md).

**Audience:** the preceding two lectures, product-rule differentiation, and trace.
**Goal:** construct exact feasible motions through an arbitrary transporter and
derive the vanishing of both diagonal gradient compressions at a minimizer.

The scenes in `scenes.py` use [lecture.md](../../../lectures/README.md#variations). A short context
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


The final two slides collect reusable symbolic facts and then show their Lean
statements with short applications of the library declarations. See the
[Lean companions](../../../lectures/LEAN_FACTS.md) for copyable files, exact API
names, assumptions, attribution, and validation details. The code shown on the
slide is read directly from its companion file.


The computational coda connects exact exponential steps with numerical manifold
optimization and blockwise QR/polar retractions. The source constraint and the
difference between stationarity and global optimality stay explicit.
Primary papers and numerical-library documentation are linked in the transcript.
