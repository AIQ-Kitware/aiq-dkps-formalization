# Thinking about I minus P

A standalone lecture for someone who knows vectors and matrix products but wants
a geometric reading of complementary projections. It begins with the classical
least-squares fitting question, defines its own notation, and develops the
projection and motion pictures separately.

The main points are:

- For an **orthogonal** projection onto K, `(I-P)x = x-Px` is the component in
  the perpendicular subspace. Its norm is the distance to K. The actual move
  from x to Px has the opposite sign.
- With the manuscript's original-minus-output convention, `I-P` is indeed the
  displacement of P. Its extra complementary-projection structure comes from
  P being an orthogonal projection. A general `I-W` need not be a projection.
- In the unit-vector picture, projection error is `sin(theta)`. Rotating a unit
  vector through theta gives chord displacement `2 sin(theta/2)`.
- The unrestricted norm of a nonzero complementary projection is one. Small
  subspace error concerns its restriction to trial vectors, `(I-P) E0`.
- The paper's ambient error `S = (I-P) E0` and unwanted-coordinate error
  `X = F1^T E0` satisfy `S = F1 X`. They have equal operator norms because F1
  is isometric. The operator residual R is a distinct map.

The lecture has 16 slides: local setup, geometry and animated angle changes,
restriction to trial vectors, the paper's sine block, comparison with rotation,
summary, mathematical facts, two highlighted Lean cards, an optional numerical
bonus, and two multiple-choice study questions.

## Sources and scope

`facts.lean` applies Mathlib's `Submodule.starProjection_orthogonal` and
`Submodule.sub_starProjection_mem_orthogonal`. These are existing library facts,
not new formalization obligations. The examples are finite and real; the Lean
projection statements work in a real inner product space whenever the specified
orthogonal projection exists. They were checked with the available rc1 cache;
see [the companion validation notes](../../../lectures/LEAN_FACTS.md).

The paper's S/X terminology is taken from
`papers/dk_formalization_journal/math_symbol_colors.tex`.
The bonus follows [SciPy's QR documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.qr.html):
full QR supplies complementary columns; economy QR does not. It distinguishes
exact identities from floating-point cancellation when the error is very small.

`model.py` contains checked numerical examples without rendering dependencies.
`scenes.py` owns the Manim animations. The YAML organizer assigned the source
folder `001500_complementary_projection`, between projections and singular norms,
without renaming the other lectures.

From `visualizations/`:

```bash
make slides DECK=prereq-complementary-projection
make video DECK=prereq-complementary-projection TTS_PROFILE=crall SKIP_RENDER=1
```
