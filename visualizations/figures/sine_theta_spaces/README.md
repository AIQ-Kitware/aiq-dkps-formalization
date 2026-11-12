# Spaces and embeddings in the sine-theta setup

An **independent, spaces-first figure**, deliberately not included in the journal
paper. It focuses on Hilbert spaces, their coordinate embeddings, exact and
trial subspaces, the exact projections, and the placement of the spectral blocks.
It does not attempt to explain residual or Sylvester estimates.

- `render_spaces.py`: authoritative Python source, with linear-algebra and
  text-spacing checks; matplotlib does vector text/typesetting and SVG export.
- `sine_theta_spaces.svg`: generated, scalable text-based artwork (no fonts or
  bitmap image assets are vendored).
- A PNG can be made locally using `--png`, but should **not be committed**.

## Render / audit

From the repository root, for an environment with NumPy and Matplotlib:

```sh
python visualizations/figures/sine_theta_spaces/render_spaces.py --check
python visualizations/figures/sine_theta_spaces/render_spaces.py --png
```

The visualizations project's normal dependencies include NumPy but do not
include Matplotlib; to use its `uv` environment without changing its lockfile:

```sh
cd visualizations
uv run --with matplotlib python figures/sine_theta_spaces/render_spaces.py --check
uv run --with matplotlib python figures/sine_theta_spaces/render_spaces.py --png
```

`--check` asserts the example's mathematical identities and checks the actual
rendered bounds of text labels for overlap and canvas overflow. It also reads
the exact paper palette from
`papers/dk_formalization_journal/math_symbol_colors.tex`, failing if required
color roles are missing. SVG output uses the STIX text/math family as vector
outlines to keep the exported appearance stable across machines.

## Reading the figure

The model illustrates **one** ambient Hilbert space, `E = R^3`. The blue plane
and cyan line pass through the origin and represent the exact orthogonal
subspaces

\[
W=\operatorname{ran}(F_0),\quad U=\operatorname{ran}(F_1),\qquad E=W\oplus U.
\]

Here `F_ex = R^2`, `G = R`, and `F = R^2` are *abstract coordinate spaces*. They
need not be literal subsets of one another or of the ambient `E`. Their linear
isometric embeddings `F_0`, `F_1`, and `E_0` identify them with subspaces of
`E`. The amber trial plane `T = ran(E_0)` is shown only 12 degrees away from
`W`. In general `T` is a different subspace from `W`; neither need contain the
other. The gray arrows are an optional ambient coordinate reference, while the
short blue arrows show that even the basis used by `F_0` may be rotated within
`W`. There is no intrinsic coordinate frame of an abstract Hilbert space `E`.

The picture's blue and amber parallelograms are **finite patches of unbounded
vector subspaces**, not set-theoretic partition regions. The blue wanted plane and the cyan orthogonal line together span all of `E`.
The amber trial plane is another subspace of `E`, not part of that exact
decomposition.

For any trial coordinate vector `x in F`, the ambient vector `v = E_0 x`
splits into

\[
E_0x = P_{\mathrm{ex}}E_0x + (I-P_{\mathrm{ex}})E_0x
     = F_0(F_0^*E_0x) + F_1(F_1^*E_0x).
\]

The projection and exact spectral blocks live on the following spaces:

| Object | Type and role |
|---|---|
| `P_ex = F_0 F_0*` | `E -> E`, orthogonal projection onto `W` |
| `I - P_ex = F_1 F_1*` | `E -> E`, orthogonal projection onto `U` |
| `Lambda_0` | `F_ex -> F_ex`, self-adjoint exact wanted block |
| `Lambda_1` | `G -> G`, self-adjoint exact complementary block |
| `lambda_0` | Representative spectral value of `Lambda_0` |
| `lambda_1` | Representative spectral value of `Lambda_1` |
| `A_0` | `F -> F`, trial-coordinate operator (only lightly marked) |

The project also names an optional trial-complement frame `E_1`. Choosing it
would provide a *second* orthogonal decomposition, `E = ran(E_0) ⊕ ran(E_1)`.
The figure leaves that extra construction out to concentrate on the exact
spectral split and the trial approximation; no `E_1` is required to read the
sine-theta setting.

## Audited illustrative 3D model

The generator sets an illustrative self-adjoint ambient operator
`Ahat = diag(1.90, 1.65, 0.70)`, exact wanted space
`W = span(e_1, e_2)`, and exact complement `U = span(e_3)`.

- `F_0` identifies `R^2` with `W` using basis vectors rotated by **24 degrees**
  relative to the gray ambient reference axes.
- `F_1(g) = g e_3`.
- `T = span(e_1, cos(12°) e_2 + sin(12°) e_3)`.
- `E_0` identifies `R^2` with `T`, using a further **-17 degree** in-plane
  basis rotation.
- `Lambda_0 = F_0* Ahat F_0`: eigenvalues **1.90 and 1.65**. Because `F_0`
  uses a rotated basis, its matrix need not be diagonal.
- `Lambda_1 = F_1* Ahat F_1 = [0.70]`. Thus one may take `lambda_1=0.70`
  and a representative wanted eigenvalue `lambda_0=1.90`.

The generator checks `F_0*F_0 = I`, `F_1*F_1 = I`, `E_0*E_0 = I`,
`F_0*F_1 = 0`, `F_0F_0* + F_1F_1* = I`, invariance of both exact spectral
blocks, and the decomposition of the displayed trial vector. The model is a
**pedagogical 3D example** and is not a replacement for the manuscript's
separate 2D numerical example.

## Color meanings

Colors are parsed, never copied, from the journal semantic palette: blue is
exact wanted, cyan is exact complementary, amber is trial, and the projection
and spectral block labels use their corresponding same-family shades.
