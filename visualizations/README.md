# Davis--Kahan visualizations

Executable geometric visualizations for the formalized Davis--Kahan results.
The current package contains two source-grounded case studies: the Section 2
**sine-theta theorem** and the explicit **Proposition 4.4 counterexample**.  Each
case study shares one checked numerical model between VTK and Manim renderers.

This directory is not part of the Lean build.  It is a companion for developing
intuition, figures, talks, and manuscript animations.  Numerical assertions here
do not replace the Lean proofs.

## What the first scene visualizes

The public Lean theorem is
`TauCeti.DavisKahan1970.SectionTwo.sinTheta`, whose conclusion is stated on the
literal positive trial-coordinate `sin Theta_0`.  Its proof-facing rectangular
representative is

```text
S = (I - F0 F0*) E0.
```

The visualization chooses the smallest real finite-dimensional specialization
where both objects and the residual can be drawn directly:

```text
ambient space E = R^2
exact desired subspace U = span(e1)
exact complementary subspace U_perp = span(e2)
trial subspace V = span(v_theta)
v_theta = (cos(theta), sin(theta))
A = diag(lambda_desired, rho + delta)
A0 = [rho]
```

The exact coordinate map `F0` sends `1` to `e1`; the trial coordinate map `E0`
sends `1` to `v_theta`.  Therefore

```text
S(1) = (I - P_U) v_theta = (0, sin(theta)).
```

Since the trial coordinate is one-dimensional, the positive modulus of `S` --
and hence the literal positive `sin Theta_0` -- is simply the scalar
`sin(theta)` for `theta` in `[0, pi/2]`.

The residual on the unit trial coordinate is

```text
R(1) = A v_theta - rho v_theta
     = ((lambda_desired - rho) cos(theta), delta sin(theta)).
```

Thus the Euclidean/operator-norm specialization of the theorem is visible as

```text
delta sin(theta) <= ||R(1)||_2.
```

The default scene sets `lambda_desired = rho = 0`, so

```text
R(1) = (0, delta sin(theta))
```

and the theorem is sharp for every displayed angle:

```text
delta sin(theta) = ||R(1)||_2.
```

This is a specialization for intuition, not the full theorem: the Lean result
handles real or complex Hilbert spaces, possibly unbounded self-adjoint
operators, full form-gap hypotheses, and where-defined unitarily invariant
norms.

## Setup

The visualization project is intentionally standalone from the Lean environment.
With `uv` installed:

```bash
cd visualizations
uv sync --extra vtk --extra test
```

For Manim as well:

```bash
uv sync --extra vtk --extra manim --extra test
```

The visualization project currently targets Python 3.11--3.13.  In particular,
Python 3.13 avoids warnings from Manim's current transitive `pydub` dependency
under Python 3.14.  If an older `.venv` was created with Python 3.14, recreate it:

```bash
rm -rf .venv
uv venv --python 3.13
uv sync --extra vtk --extra manim --extra test
```

If another uv-managed environment is already active, uv may print a
`VIRTUAL_ENV ... does not match ... .venv` warning.  That is expected: these
commands deliberately use the local `visualizations/.venv`.

Manim may require the usual system packages for Cairo, Pango, FFmpeg, and LaTeX
on the host distribution.

## Numerical model

Print the quantities in the default sharp model:

```bash
cd visualizations
uv run python -m dkvis.sine_theta --theta 35 --delta 1.5
```

Show a non-sharp model by moving the desired eigenvalue away from the trial
scalar:

```bash
uv run python -m dkvis.sine_theta \
    --theta 35 \
    --delta 1.5 \
    --rho 0.0 \
    --lambda-desired -0.6
```

## Interactive VTK explorer

```bash
cd visualizations
uv run --extra vtk python -m dkvis.vtk_sine_theta
```

The angle slider rotates the trial subspace.  The scene simultaneously shows:

- the exact desired subspace `U`;
- the trial subspace `V` and unit vector `v_theta`;
- `P_U v_theta`;
- `(I - P_U) v_theta`, the rectangular sine block used by the Lean proof;
- the residual `R(1)`;
- `sin(theta)`, `delta sin(theta)`, and `||R(1)||_2` numerically.

Generate a deterministic PNG without opening an interactive window:

```bash
mkdir -p renders
uv run --extra vtk python -m dkvis.vtk_sine_theta \
    --theta 40 \
    --delta 1.25 \
    --no-interact \
    --screenshot renders/sine-theta.png
```

## Manim animation

```bash
cd visualizations
uv run --extra manim python -m manim -pql dkvis/manim_sine_theta.py SineThetaScene
```

Invoke Manim through `python -m manim`, not the `.venv/bin/manim` console
script.  Manim loads scene files by path, and the module invocation keeps the
`visualizations/` project root on `sys.path`, so `from dkvis...` imports resolve.

The Manim scene uses the same `SineThetaModel`.  It animates the trial line while
keeping the exact subspace fixed, then displays the two identities that explain
the theorem geometrically:

```text
(I - P_U) v_theta = (0, sin(theta))
R(1) = (0, delta sin(theta))              [sharp default model]
```


## Proposition 4.4 counterexample

`dkvis.prop44.Prop44Model` encodes the exact `R^4` witness used by the Lean
refutation.  With `U = span(e0,e1)`, the admissible competitor is

```text
W = 1/2 * [[ 1, -1, -1, -1],
           [ 1,  1,  1, -1],
           [-1, -1,  1, -1],
           [ 1, -1,  1,  1]]
V = W(U).
```

Both principal angles between `U` and `V` are `pi/4`, strictly below the
printed `pi/3` threshold.  The Davis--Kahan direct rotation is

```text
R = 1/sqrt(2) * [[ 1,  0,  0, -1],
                 [ 0,  1,  1,  0],
                 [ 0, -1,  1,  0],
                 [ 1,  0,  0,  1]].
```

The displacement singular values are

```text
sigma(I - R) = (sqrt(2 - sqrt(2)),) * 4
sigma(I - W) = (sqrt(2), sqrt(2), 0, 0),
```

so the trace norm gives the strict contradiction

```text
||I - W||_* = 2 sqrt(2) ~= 2.828427
            < 4 sqrt(2 - sqrt(2)) ~= 3.061467
            = ||I - R||_*.
```

Print and verify those invariants directly:

```bash
cd visualizations
uv run python -m dkvis.prop44 --verify
```

### Interactive four-plane VTK explorer

```bash
uv run --extra vtk python -m dkvis.vtk_prop44
```

The VTK scene intentionally uses **no 4D-to-3D projection**.  Instead it shows
four exact two-dimensional invariant-plane restrictions of the actual `R^4`
operators:

```text
left column -- direct rotation R
  span(e0,e3): +45 deg
  span(e1,e2): -45 deg

right column -- competitor W
  span(m0,m1): +90 deg
  span(m2,m3):   0 deg (fixed)
```

These are different decompositions of `R^4`.  The direct-rotation planes are
principal/invariant planes for `R`; the `m` planes are the moving and fixed
invariant planes for `W`.  The display does not identify them with one another.

A single `MOTION t` slider animates all four local rotations from the identity
to the endpoint.  Only `t=1` is the Proposition 4.4 comparison.  Each panel
reports:

- its exact local rotation angle;
- the two singular values of `I-T` on that 2-plane;
- that plane's contribution to the trace norm.

For a real 2D rotation through angle `alpha`, both singular values of
`I-Rot(alpha)` equal

```text
2 |sin(alpha / 2)|,
```

so one plane contributes

```text
4 |sin(alpha / 2)|
```

to the full trace norm.  At the endpoint this makes the counterexample visible
without any projection artifact:

```text
R:  45 deg + 45 deg
    1.530734 + 1.530734 = 3.061467

W:  90 deg + 0 deg
    2.828427 + 0        = 2.828427
```

The competitor panels also state how the original source basis splits across
its two invariant planes:

```text
P_M e0       = m0 / sqrt(2)
P_M e1       = m1 / sqrt(2)
P_Mperp e0   = m2 / sqrt(2)
P_Mperp e1   = m3 / sqrt(2).
```

Thus the quarter-turn-plus-identity picture is not claiming that `U` itself is
one line in each `W` plane; it shows the exact invariant decomposition through
which `W` redistributes the ambient motion.

Generate a deterministic endpoint PNG:

```bash
mkdir -p renders
uv run --extra vtk python -m dkvis.vtk_prop44 \
    --t 1 \
    --no-interact \
    --screenshot renders/prop44.png
```

### Manim invariant-plane explanation

```bash
uv run --extra manim python -m manim -pql dkvis/manim_prop44.py Prop44Scene
```

This scene uses exact endpoint invariant decompositions instead of a 3D
projection.  They are deliberately labeled as *different* decompositions:

```text
R:  span(e0,e3) rotates +45 deg
    span(e1,e2) rotates -45 deg

W:  span(m0,m1) rotates +90 deg
    span(m2,m3) is fixed
```

It then compares the four singular values of the full displacement.  This is
the key trace-norm mechanism: the direct rotation has four equal nonzero chord
lengths, while the competitor has two larger chord lengths and two zeros; the
sum is nevertheless smaller for the competitor.

## Validation

The unit tests check the geometric decomposition, the residual formula, sharp
cases, and several non-sharp cases:

```bash
cd visualizations
uv run --extra test pytest -q
```

A useful smoke test for the VTK renderer is:

```bash
uv run --extra vtk python -m dkvis.vtk_sine_theta \
    --theta 40 --no-interact --screenshot renders/smoke.png
```

## Planned extensions

Keep the shared numerical model / multiple-renderer split.  The next natural
scenes are:

1. `tan Theta`: show the trial subspace as a graph over the exact subspace and
   visualize tangent as slope.
2. `sin 2Theta`: show the doubled-angle geometry, including the reflection
   interpretation.
3. `tan 2Theta`: animate the sharp 2x2 model and the approach to the `pi/4`
   barrier.
4. Proposition 4.4 equation (4.3): add a separate scene explaining why the
   printed principal-plane lower-bound step fails on the same witness.
