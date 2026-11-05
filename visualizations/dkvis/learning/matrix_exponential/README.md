# The exponential of a matrix

An independent 13-slide lecture before feasible variations. Find the transcript,
slides, and handout in [the lecture library](../../../lectures/README.md#matrix_exponential).

Audience: matrix multiplication, power series, and single-variable calculus.
The lecture introduces the equation `x' = A x` locally. It builds the series,
explains the many-small-steps limit, and works through diagonal growth,
nilpotent shear, and rotation. The final steps derive the inverse and transpose
identities, explain the noncommuting-generator caveat, and prove orthogonality
and source preservation for the exponential curves used by the matching proof.

Historical context cites Cayley's 1858 matrix-algebra memoir and Higham's 2005
work on scaling and squaring; it does not assert that either originated every
concept in the lecture. Source links are in the transcript.

`model.py` supplies modest finite-matrix Taylor and Euler illustrations, checked
against independent closed forms in `tests/test_prerequisite_models.py`.
These helpers are for teaching, not production numerical recommendations.
Real finite matrices are the scope; this is not a lesson on unbounded generators.

Build from `visualizations/`: `make slides DECK=prereq-matrix-exponential`.
