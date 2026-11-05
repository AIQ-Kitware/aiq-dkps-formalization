# Singular values and displacement cost

A lecture in [the prerequisite series](../PREREQUISITES.md).

**Audience:** basic linear algebra and the projection lecture.
**Goal:** interpret the SVD geometrically, distinguish operator/Frobenius/trace
norms, compute rotation and reflection costs, and justify block additivity.

The ten scenes in `scenes.py` use [lecture.md](../../../lectures/README.md#singular_norms). `model.py` supplies
the ellipse, competing orthogonal displacements, direct-sum example, and
overlapping-image counterexample. The short historical context cites
[Eckart and Young (1936)](https://doi.org/10.1007/BF02288367) for low-rank
matrix approximation, without attributing the origin of the SVD to that paper.

The lesson distinguishes the Schatten norm from its power, and a scalar
smoothing illustration from the finite-matrix differentiability statement.
It ends by computing the three norms for singular values 3 and 4. The example
with overlapping images explains why separate domain restrictions cannot
automatically be charged as independent blocks.

Build with `make slides DECK=prereq-singular-norms` from `visualizations/`.


The final two slides collect reusable symbolic facts and then show their Lean
statements with short applications of the library declarations. See the
[Lean companions](../../../lectures/LEAN_FACTS.md) for copyable files, exact API
names, assumptions, attribution, and validation details. The code shown on the
slide is read directly from its companion file.
