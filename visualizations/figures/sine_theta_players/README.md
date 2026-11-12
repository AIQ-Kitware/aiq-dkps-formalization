# Geometry and notation of the sine-theta theorem

This is a **standalone, programmatically generated figure draft** for the
Davis--Kahan sine-theta theorem. It is not included in the journal paper or
its LaTeX build, and its SVG is text-based, not a binary image asset.

- `render.py` is the source of the SVG: named groups, explicit coordinates,
  formula labels, and checks, using only Python's standard library.
- `sine_theta_players.svg` is its editable vector output.
- No fonts, PNGs, or raster images are stored in this figure directory.

To regenerate and check from the repository root:

```bash
python visualizations/figures/sine_theta_players/render.py
python visualizations/figures/sine_theta_players/render.py --check
```

Optional preview outside the repository:

```bash
inkscape visualizations/figures/sine_theta_players/sine_theta_players.svg \
  --export-filename=/tmp/sine_theta_players.png --export-width=1800
```

## Visual interpretation

The exact wanted and complementary subspaces span the **whole ambient space**:

\[
E = \operatorname{ran}(F_0) \oplus \operatorname{ran}(F_1), \qquad
\operatorname{ran}(F_0)\perp\operatorname{ran}(F_1).
\]

The central panel depicts a two-dimensional example: the blue and cyan
**perpendicular directions span the plane**. They are not disjoint colored
regions; their direct sum means that every vector in E has a unique
orthogonal decomposition into their components. The amber trial subspace is
another direction in this same plane, with a 12-degree principal angle to the
blue wanted direction. A trial vector has an exact wanted projection and a
smaller complementary projection.

The separate coordinate Hilbert spaces do not need to be literal subspaces
of E:

| Coordinates | Isometric embedding into E | Image in E | Role |
| --- | --- | --- | --- |
| `F_ex` | `F_0: F_ex -> E` | `ran(F_0)` | Wanted exact coordinates |
| `G` | `F_1: G -> E` | `ran(F_1)` | Complementary exact coordinates |
| `F` | `E_0: F -> E` | `ran(E_0)` | Trial coordinates |

Thus **`F_ex + G` coordinates all of `E`**, up to the isometric direct-sum
identification. In contrast, `F` maps into an approximate trial subspace,
which need not coincide with `ran(F_0)`.

A trial vector `E_0 x` splits as

```text
E_0 x = F_0 (F_0* E_0 x) + F_1 (F_1* E_0 x).
```

`P_ex = F_0 F_0*` extracts the wanted part. The map
`X = F_1* E_0 : F -> G` extracts its complementary exact coordinates.
The rectangular complement `S = (I - P_ex) E_0` satisfies
`S = F_1 X` and `abs(X) = abs(S) = sin(Theta_0)`.

For the residual `R = Ahat E_0 - E_0 A_0`, the core equation is

```text
Lambda_1 X - X A_0 = F_1* R.
```

The theorem bounds `delta * N(sin(Theta_0)) <= N(R)` under its specified
spectral-separation, domain, and operator-ideal hypotheses.

## Numerical example and audit

This standalone figure intentionally uses a **12-degree trial angle** to make
its near-alignment evident. The journal manuscript's separate Figure 1 uses
**40 degrees**. Both use the same diagonal ambient operator, but their
trial Rayleigh values, residuals, and scalar gaps consequently differ.

```text
E = R^2;  F = F_ex = G = R
Ahat = diag(1.9, 0.7)
theta = 12 degrees
F_0(h) = (h, 0)                 exact wanted x-axis
F_1(g) = (0, g)                 exact complementary y-axis
v = (cos(theta), sin(theta))    trial unit vector
E_0(t) = t v
A_0(t) = rho t,   rho = <v, Ahat v>
Lambda_1(g) = 0.7 g
```

In this example, the trial vector decomposes as

```text
v = (cos(theta), 0) + (0, sin(theta))
X(1) = sin(theta)
S(1) = (0, sin(theta))
rho = 1.9 cos(theta)^2 + 0.7 sin(theta)^2 ~ 1.848127275
delta = rho - 0.7 ~ 1.148127275
R(1) = ((1.9-rho) cos(theta), (0.7-rho) sin(theta))
F_1* R(1) = (0.7-rho) sin(theta)
Lambda_1 X(1) - X A_0(1) = (0.7-rho) sin(theta)
```

`render.py --check` verifies the unit vector, exact decomposition,
orthogonality, complementary readout, residual orthogonality for the Rayleigh
choice, the Sylvester identity, and the scalar gap estimate. It also parses
the SVG and verifies the ambient geometry group exists.

The numerical model is finite-dimensional and ordered. The actual theorem
also covers infinite-dimensional spaces and unbounded operators with the
manuscript's accompanying domain and separation hypotheses.

## Semantic colors and typography

The palette matches the mathematical-symbol registry in
`papers/dk_formalization_journal/math_symbol_colors.tex`:

| Role | Paper color |
| --- | --- |
| Exact wanted | Blue `#1F6FD1` |
| Exact complement | Cyan `#007C91` |
| Trial | Amber `#A66705` |
| Angle | Magenta `#D12A7B` |
| Residual | Green `#087D43` |
| Spectral gap | Violet `#6E4BD8` |

The SVG requests **TeX Gyre Pagella** for prose and **STIX** for mathematics,
with serif fallbacks. Fonts are referenced by name, never redistributed.
Every visual object is generated from editable SVG elements with named groups.
