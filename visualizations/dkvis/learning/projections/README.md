# Subspaces and projections

A lecture in [the prerequisite series](../PREREQUISITES.md).

**Audience:** knows vectors, inner products and matrix multiplication.
**Goal:** translate a subspace into its orthogonal projector, distinguish frames
from subspaces, read block coordinates, and derive the transport equation.

The nine scenes in `scenes.py` use [lecture.md](../../../lectures/README.md#projections) as their transcript.
`model.py` supplies the projection and rotating-frame examples. The historical
opening connects nearest-point geometry to
[Young's 1937 subspace-fitting paper](https://doi.org/10.1007/BF02287962).
It is not a history of the invention of orthogonal projections.

The concluding self-check asks whether rotating within a complementary plane
commutes with the source-line projector. The answer connects directly to the
source-preserving velocities in lecture 3. Equal-dimension orthogonal transport
is expressed as `Q = W P W^T`; no principal-plane restriction is imposed on W.

Build with `make slides DECK=prereq-projections` from `visualizations/`.
