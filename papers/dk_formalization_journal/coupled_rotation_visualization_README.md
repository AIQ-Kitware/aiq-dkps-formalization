# Direct versus coupled rotation: interactive geometric viewer

This is a companion visualization for the Davis--Kahan formalization manuscript.
It compares two ambient orthogonal maps that carry the same real two-dimensional
source subspace onto the same target subspace, yet have different full
nuclear-norm displacement. The browser application is responsive and has no
external libraries or network requirements. The Python launcher can also
export compact vector figures suitable for inclusion in a LaTeX paper.

## Run

From this directory:

```bash
python3 coupled_rotation_viewer.py
```

The script opens `coupled_rotation_explorer.html` in the default browser. The
HTML file can also be opened directly. Rotate the principal-angle slider,
change the `t` slice, drag either 3D panel to orbit both views, and use the
check box to show the four-dimensional invariant-plane decompositions.
For the x-t, y-t, and z-t projections, choose **Direct R** or **Coupled W**
using the two-button selector above the plots (or press `R` or `W` on your
keyboard). Each time-projection plot shows only the selected transporter's
material-coordinate grid and tracked source-vector arrows. The 3D comparison
remains side by side. The target subspace and actual time slice are unchanged
when you switch modes; only the pointwise map changes. The selected mode is
also respected by the Save PNG dashboard export. For a reproducible browser
view, append `?projection=direct` or `?projection=coupled` to the HTML URL. The
Play button smoothly varies the angle. Save PNG captures a coordinated
high-resolution dashboard. Python's standard library is sufficient for this
interactive mode.

For an SVG or PDF figure (requires NumPy and Matplotlib):

```bash
python3 -m pip install numpy matplotlib
python3 coupled_rotation_viewer.py --export-figure direct_vs_coupled.svg --theta 45
python3 coupled_rotation_viewer.py --export-figure direct_vs_coupled.pdf --theta 45
python3 coupled_rotation_viewer.py --self-test
```

Both PDF and SVG exports are vector figures; a PNG export is also available.
The publication figure deliberately shows the same *target disk* in both
panels, with different grids and orange/purple arrows tracking the original
source basis vectors. The third panel compares displacement singular values.
The figure can be included with `\includegraphics` (for the PDF); its caption
should state that the rendered 3D discs are projections from four dimensions,
not fixed-time slices.

## Exact mathematical setup

Work in Euclidean `R^4` with coordinates `(x,y,z,t)`; the fourth coordinate is
named `t` for visualization but is **not** a relativistic time coordinate.
Set `K = span(e_x,e_y)` and, for a principal angle `theta`:

- `y_1 = cos(theta)e_x + sin(theta)e_t`;
- `y_2 = cos(theta)e_y - sin(theta)e_z`;
- `L(theta) = span(y_1,y_2)`.

The canonical **direct rotation** `R(theta)` independently rotates the
`(e_x,e_t)` plane and `(e_y,e_z)` plane by the two principal angles.

For the **coupled rotation** `W(theta)`, first set

- `u=(e_x+e_z)/sqrt(2)`, `v=(e_y+e_t)/sqrt(2)`;
- `a=(e_x-e_z)/sqrt(2)`, `b=(e_y-e_t)/sqrt(2)`.

`W(theta)` rotates the two-plane `span(u,v)` through `2 theta` and fixes
`span(a,b)` pointwise. The two maps differ on individual vectors, but

```text
R(theta) K = W(theta) K = L(theta).
```

More specifically, `R(theta)e_x = y_1`, `R(theta)e_y = y_2`, whereas

```text
W(theta)e_x =  cos(theta)y_1 + sin(theta)y_2,
W(theta)e_y = -sin(theta)y_1 + cos(theta)y_2.
```

Hence the coupled transformation merely changes the orthonormal *basis* of
the same target two-plane. For `0 < theta <= 90` degrees, the singular values
of the full displacement are

```text
I - R(theta): [2 sin(theta/2), 2 sin(theta/2),
               2 sin(theta/2), 2 sin(theta/2)],
I - W(theta): [2 sin(theta), 2 sin(theta), 0, 0].
```

Thus the nuclear costs are `8 sin(theta/2)` and `4 sin(theta)` respectively.
At `theta=45` degrees these are approximately `3.061` and `2.828`. The
*operator* norm instead prefers the direct rotation: its largest displacement
singular value is smaller. This illustrates the central norm distinction in
the Proposition 4.4 counterexample.

The displayed patch is the unit disk in the source plane. Since both maps are
orthogonal and have the same target subspace, its transformed **set** is
identical under both maps. The attached material grids and arrows distinguish
how the two maps move *points*. The gold geometry is the true intersection
with a fixed `t` hyperplane; it can be a disk, chord, point, or empty. By
contrast, the large 3D views project the entire disk across all times into
ordinary spatial coordinates. The `x-t`, `y-t`, and `z-t` views show the
coordinate-time projections of all events.

## Maintenance

- `coupled_rotation_viewer.py`: canonical NumPy model, geometry self-tests,
  vector PDF/SVG figure generation, and browser launcher.
- `coupled_rotation_explorer.html`: local, dependency-free Canvas interface;
  the same transformation formulas are implemented in JavaScript for
  interactive frame rates. When changing the geometry, update **both**
  implementations and their checks (`--self-test` and `verifyModel()`).
- Figures are derived artifacts: regenerate them from the script rather than
  hand-editing them or checking screenshots in as sources.

This demonstration is the equal-angle four-dimensional pairing example,
**not** a visualization of all unequal-angle matching blocks or an implementation
of the global matching algorithm.
