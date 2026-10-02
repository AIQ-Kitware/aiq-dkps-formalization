# Davis--Kahan visualizations

Executable geometric visualizations for the formalized Davis--Kahan results.
The current package contains two source-grounded case studies: the Section 2
**sine-theta theorem** and the explicit **Proposition 4.4 counterexample**. Each
case study shares one checked numerical model between VTK and Manim renderers.

This directory is not part of the Lean build. It is a companion for developing
intuition, figures, talks, and manuscript animations. Numerical assertions here
do not replace the Lean proofs.

## What the first sine-theta scenes visualize

The public Lean theorem is
`TauCeti.DavisKahan1970.SectionTwo.sinTheta`, whose conclusion is stated on the
literal positive trial-coordinate `sin Theta_0`. Its proof-facing rectangular
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
sends `1` to `v_theta`. Therefore

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

The visualization project currently targets Python 3.11--3.13. In particular,
Python 3.13 avoids warnings from Manim's current transitive `pydub` dependency
under Python 3.14. If an older `.venv` was created with Python 3.14, recreate it:

```bash
rm -rf .venv
uv venv --python 3.13
uv sync --extra vtk --extra manim --extra test
```

If another uv-managed environment is already active, uv may print a
`VIRTUAL_ENV ... does not match ... .venv` warning. That is expected: these
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

## Slide decks: the sine-theta theorem, in pictures

The decks are [manim-slides](https://manim-slides.eertmans.be) scenes with
presenter notes on every build. There are two presentation paths:

- **`sine-theta-short`: the 15-minute core talk.** It is for a technical but
  non-mathematical audience: the intuition, the theorem, what was formalized, and
  the Proposition 4.4 counterexample.
- **`sine-theta-full`: everything**, in six parts that are rendered separately
  and each get their own HTML, PDF and handout (`renders/part<k>-*.html`):

  | part | deck | content |
  | --- | --- | --- |
  | 1 | `part1-sine-theta` | the `sin Theta` theorem: setting, intuition, theorem, proof idea, Lean |
  | 2 | `part2-3d` | `sin Theta` in three dimensions (VTK) |
  | 3 | `part3-family` | the `tan Theta`, `sin 2Theta` and `tan 2Theta` theorems |
  | 4 | `part4-prop44` | Proposition 4.4: refutation and repair |
  | 5 | `part5-process` | how the formalization was built |
  | 6 | `part6-summary` | what to take away |

  Slides are numbered within their part ("3 / 7") and the footer names the part.
  The full deck is assembled from the parts' renders, so it renders nothing
  itself and re-rendering one part leaves the others alone. Slides beyond the
  core talk carry a badge in the top-right corner: `*` = optional technical
  depth, `**` = backup. Unmarked slides are the core talk. The title slide states
  this convention.

| slide | short | full | idea |
| --- | :-: | :-: | --- |
| `S00Title` | yes | yes | how far can an eigenvector turn? |
| `S00bSetting` | yes | yes | the setting: self-adjoint operators, from real symmetric matrices to unbounded operators |
| `S01Ellipse` | yes | yes | a positive-definite example maps the circle to an ellipse; axes are eigenvectors |
| `S02Perturb` | yes | yes | `A -> A+H`: eigenvalues barely move (Weyl), axes turn |
| `S03NoGap` | yes | yes | "How far can an eigenvector turn? It depends on whether there is a gap": A's eigenvectors (drawn as lines) in the ellipse and its eigenvalues on a number line; for a fixed small `H`, as the gap closes the eigenvector of `A+H` turns toward 45 degrees while the eigenvalues move at most `‖H‖` |
| `S03cUnstable` | yes | yes | "Without a gap, an eigenvector can point anywhere": `H` of fixed size turned once round; the traced eigenvector directions form a thin wedge (at most 7 degrees) with a gap and fill every direction without one; `A ± εσ_x` example; why Davis--Kahan works with subspaces |
| `S03bWanted` | yes | yes | which eigenvectors are "wanted": a chosen part of the spectrum (PCA, ground states, clustering); they span `U`, the rest `U^perp`, and the gap separates them |
| `S04Angle` | yes | yes | with a "Recall" panel for `U`, `V`, `theta`, `E0`, `F0`, `F1`: `sin theta = dist(v, U)`; `sin Theta0` is the operator whose eigenvalues are the sines |
| `S04bSinThetaOperator` | | `*` | `sin Theta0` exactly: definition, `|S| = sin Theta0`, and the Lean bridge |
| `S05Residual` | yes | yes | "The residual": a "Recall" panel for `A`, `U`, `v`; why `r = Av - rho v` is computable from `A` and `v` while the angle needs `U`; every build adds, so the last build is the complete slide |
| `S06Gap` | yes | yes | the separating window; why an interval |
| `S07Theorem` | yes | yes | `delta ||sin Theta0|| <= ||R||`: error <= residual / gap |
| `S08Why` | yes | yes | why it is true, with one wanted direction `u` and one unwanted `w`: the wrong part of `v` (length `sin theta`) is scaled by at least `delta` in the residual |
| `S08Components` | | `*` | the same mechanism across the whole spectrum (bar chart, with the equations) |
| `S09Sylvester` | | `*` | the block proof: a Sylvester equation |
| `S11Payoff` | yes | yes | `||sin Theta0|| <= ||H|| / delta` against the true rotation |
| `S10Sharp` | | `*` | the constant 1 is sharp |
| `D01Planes` | yes | yes | the 3D picture (VTK), ending on an orbit video |
| `D02Tilt` ... `D05TryIt` | | `*` | the 3D sweeps and the live demo |
| `S12Lean` | yes | yes | the complete Lean statement, with an orienting caption and a "reading it" build |
| `F01Setup` | | `*` | the shared setup of the four Section 2 theorems: old `A`, new `A+H`, their blocks, and which spectra each theorem separates |
| `F01bAngles` | | `*` | directed `Theta0` vs ambient `Theta` (each angle twice, `||sin Theta|| = ||P - Q||`), `R` vs `H`, and why `sin Theta` has no one-gap ambient form (Proposition 6.1) |
| `F01cTwoByTwo` | | `*` | one 2x2 rotation: `tan 2theta`, `sin 2theta`, `tan theta` are `b` over the old gap, the new gap and the mixed gap; `sin theta` is smaller |
| `F02TanTheta` | | `*` | the `tan Theta` theorem: Rayleigh--Ritz values and a one-sided gap; exact in two dimensions; fails with a two-sided gap (`diag(-1, 0, 1)`) |
| `F03SinTwoTheta` | | `*` | the `sin 2Theta` theorem: a gap inside `A+H` alone; equality on the 2x2 example; `theta` vs `90 - theta` and Theorem 8.2 |
| `F04TanTwoTheta` | | `*` | the `tan 2Theta` theorem: a gap in `A` alone and off-diagonal `H`; the gap example is an equality at every gap; Theorem 8.1's 45-degree ceiling |
| `S13Family` | | `*` | summary table of the four theorems, with their Lean names |
| `P01Claim` | yes | yes | Proposition 4.4: what it claims and why it is plausible |
| `P02Counterexample` | yes | yes | the `R^4` counterexample: chords, trace norm, the norms table, the Lean repair |
| `P03Why` | | `*` | concavity of chord length explains the failure and the `Q`-norm repair |
| `P04Details` | | `**` | the explicit matrices and Lean declarations |
| `W01Workflow` | | `*` | how the formalization was built: the workflow from the workshop paper, with who did what |
| `W02TwoChecks` | | `*` | Lean checks the proof; source comparison checks the statement; three kinds of drift seen in practice |
| `W03ThreeStatements` | | `*` | three checked sine-theta statements with the same conclusion and different scope |
| `W04Reversals` | | `*` | timeline of accepted source comparisons that were withdrawn (14 in 10 results, to 4 Sep 2026) |
| `W05Scale` | | `*` | foundations built, YWS, retained telemetry, and the starting point |
| `W06Claims` | | `*` | what the evidence supports and what it does not |
| `S14Summary` | yes | yes | three takeaways |

The modules are `dkvis/slides_sine_theta.py` (2D), `dkvis/slides_sine_theta_3d.py`
(3D, see below), `dkvis/slides_family.py` (the other three Section 2 theorems),
`dkvis/slides_prop44.py` (Proposition 4.4) and `dkvis/slides_process.py` (how the
formalization was built, from the workshop and journal papers in `papers/`; its
dated numbers are pinned to those papers' evidence snapshots). Deck order lives in
`dkvis/build_slides.py` (`PARTS` and `DECK_SCENES`).

The Lean facts quoted on the slides were checked against a fresh build with
`#check` and `#print axioms`:

- `TauCeti.DavisKahan1970.SectionTwo.sinTheta`
- `SectionTwo.tanTheta_directed`, `tanTheta_ambient`, `sinTwoTheta`,
  `tanTwoTheta_directed` and `tanTwoTheta_ambient` (all scalar-generic)
- `proposition4_4_refuted` and `proposition4_4_refutingPair`
- `directRotation_fullDisplacement_qnorm` and `kyFan_not_isQNorm`
- `sourceDirectedSinThetaOperator_eq_modulus`

All use only `propext`, `Classical.choice` and `Quot.sound`. `S12Lean` prints
`LEAN_SIGNATURE` verbatim, apart from dropped instance-binder names and re-broken
lines. Re-check it whenever the `sinTheta` alias moves.

Every number on a slide comes from `dkvis/sine_theta_story.py` (or the existing
`dkvis/sine_theta.py`), whose models are checked by `tests/`. Colors carry
meaning on every slide: blue = exact eigenspace, amber = trial, pink = angle,
green = residual, violet = gap.

Build and present from `visualizations/`. The `Makefile` wraps the common
cases (`make` lists the targets):

```bash
make setup                         # uv sync with the vtk, slides and test extras
make all                           # short deck, every part, and the full deck: 1080p60 HTML + PDF + handout in renders/
make part3 QUALITY=l               # one part of the full talk at 480p, with its own HTML (part1 ... part6)
make handout                       # renders/<deck>.handout.pdf: one page per slide, from the existing renders
make standalone                    # renders/<deck>.standalone.html: one file, videos embedded, easy to share
make rebuild                       # clean re-render of both decks from scratch
make short QUALITY=l PDF=0         # quick 480p draft of the short deck
make full SCENES="S05Residual"     # re-render only some scenes, then reconvert every part and the full deck
make clean-part3 && make part3     # clean re-render of one part
make present-short                 # present live with manim-slides
```

The underlying commands:

```bash
uv sync --extra vtk --extra slides --extra test   # needs LaTeX, and Pango/Cairo headers to build manimpango
RUN="uv run --extra vtk --extra slides --extra test"   # always pass the extras: a bare `uv run` re-syncs them away
$RUN python -m dkvis.build_slides sine-theta-short -q l          # quick draft (480p)
$RUN python -m dkvis.build_slides part3-family --pdf --handout   # one part, 1080p60
$RUN python -m dkvis.build_slides sine-theta-full                # every part, then the assembled full deck
$RUN manim-slides present --folder slides-sine-theta-short $($RUN python -m dkvis.build_slides sine-theta-short --list)
```

- Every slide shows its number bottom-right: its position in the short deck, or
  in its part ("7 / 16"). The number is the same on all of a slide's builds, so
  in the PDF a repeated number means "same slide, next animation step". Because
  the same scene sits at different positions in the short deck and in its part,
  each renders into its own `slides-<deck>/` folder; the full deck reuses the
  parts' folders. The full-frame VTK video builds carry no number.
- `renders/<deck>.html` is a reveal.js deck: arrow keys advance builds, and `S`
  opens the speaker view with the notes. Keep `renders/<deck>_assets/` next to
  it, or pass `--one-file` to embed the videos.
- `manim-slides present` is the most robust option for a live talk. Looping
  builds (angle sweep, sharpness sweep) repeat until you advance.
- `--pdf` writes the last frame of every build, for pasting into other slide
  software; `--pptx` writes PowerPoint.
- `--handout` writes `renders/<deck>.handout.pdf`, one page per slide: the
  final frame of its last build (skipping a trailing VTK video, which is a live
  demo rather than a page). **Design rule:** a slide's last build must stand
  alone as a static page. Builds may animate and remove things along the way,
  but whatever the slide argues has to be on screen at the end; when the
  argument is a motion (a sweep, a turn), the end state shows it statically,
  e.g. as traces, a plot, or before/after panels.
- `--scenes S08Components` re-renders one scene; conversion always uses the
  whole deck.
- `DKVIS_THEME=light` renders a light-background deck for bright rooms.

## Interactive 3D demo (VTK) and its slides

`dkvis/vtk_sine_theta_3d.py` is a live demo of the theorem in `R^3`, where the
exact invariant subspace is a plane: `U = span(f1, f2)` is the plane of the two
wanted axes of the ellipsoid of `A`, and `f3` spans the unwanted direction.

```bash
uv run --extra vtk python -m dkvis.vtk_sine_theta_3d                 # trial mode
uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --mode perturb  # A -> A + eps H
```

- **Trial mode:** the trial plane `V` is `U` tilted by `theta` about a hinge
  line at azimuth `phi`, with the Rayleigh--Ritz `A0 = E0^T A E0`. Two planes in
  `R^3` share a line, so the principal angles are `(theta, 0)`; the pink drop is
  the one nonzero sine, and the green residuals leave `V` at right angles.
- **Perturb mode:** the trial is the old eigenspace and the operator is
  `A + eps H` (fixed `H` with `||H||_2 = 1`); the ellipsoid and the exact plane move,
  and `R = eps H E0`.
- **Readouts:** the spectrum strip shows the wanted eigenvalues, `lambda3`,
  `spec(A0)`, and the gap `delta = min |mu_i - lambda3|`. With a single unwanted
  eigenvalue this is exactly the exchanged form of the paper's hypothesis. The
  right panel compares `delta ||sin Theta0||` against `||R||_2` live.
- **Controls:** sliders for `theta`, `phi`, `eps`, `lambda3`; drag to rotate, scroll
  to zoom; keys `m` mode, `space` play, `e` ellipsoid, `x` residuals, `r` reset
  view, `s` screenshot, `h` help, `q` quit.

Every configuration drawn is computed by `dkvis/sine_theta_3d.py`, and each
update re-checks the theorem (`tests/test_sine_theta_3d.py`). The same program
renders headlessly, so it also produces the slide assets:

```bash
uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --screenshot out.png
uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --movie sweep-theta --out out.mp4
uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --slide-assets media/vtk3d
```

`dkvis/slides_sine_theta_3d.py` is a five-scene deck built on it:

1. the planes in 3D, with VTK stills beside the text, then a looping orbit video;
2. the tilt sweep with a numbers table;
3. moving `lambda3`;
4. the perturbation;
5. "try it live".

`dkvis.build_slides` renders the VTK assets on first use (about 3 minutes;
`--refresh-assets` redoes them):

```bash
uv run --extra vtk --extra slides python -m dkvis.build_slides part2-3d         # the 3D part alone
uv run --extra vtk --extra slides python -m dkvis.build_slides sine-theta-full  # every part, 3D as part 2
```

In a talk, the video slides loop until you advance. To go live instead, switch
to the running `vtk_sine_theta_3d` window at the "try it live" slide.

## Sine-theta slide-building sequence (VTK)

The sine-theta material now has **three VTK scenes** intended to build slides in
order:

1. **setup** -- `dkvis.vtk_sine_theta_intro`
2. **motivation** -- `dkvis.vtk_sine_theta_motivation`
3. **theorem / illustration** -- `dkvis.vtk_sine_theta`

That sequence is meant to answer, in order:

1. What are the exact and trial objects?
2. Why does a sine appear at all?
3. How does the residual bound the subspace error?

### 1. Introductory setup scene

```bash
cd visualizations
uv run --extra vtk python -m dkvis.vtk_sine_theta_intro
```

This slide-oriented scene introduces the geometric objects **before** any proof
mechanics are used:

- ambient space `E = R^2`;
- exact subspace `U = span(e1)`;
- complementary line `U_perp = span(e2)`;
- trial subspace `V = span(v_theta)`;
- unit trial vector `v_theta`;
- coordinate maps `F0(1)=e1` and `E0(1)=v_theta`.

Generate a deterministic PNG:

```bash
mkdir -p renders
uv run --extra vtk python -m dkvis.vtk_sine_theta_intro \
    --theta 35 \
    --no-interact \
    --screenshot renders/sine-theta-intro.png
```

### 2. Motivation scene: why `sin(theta)`?

```bash
uv run --extra vtk python -m dkvis.vtk_sine_theta_motivation
```

This second slide keeps the exact and trial geometry visible while explaining the
proof-facing rectangular block:

```text
S = (I - P_U) E0.
```

On the unit trial coordinate,

```text
v_theta = P_U v_theta + (I - P_U) v_theta,
P_U v_theta       = (cos(theta), 0),
(I - P_U) v_theta = (0, sin(theta)).
```

So the length of the vertical leg is exactly `sin(theta)`, which is the visible
specialization of `||sin Theta_0||`.

Generate a deterministic PNG:

```bash
mkdir -p renders
uv run --extra vtk python -m dkvis.vtk_sine_theta_motivation \
    --theta 35 \
    --no-interact \
    --screenshot renders/sine-theta-motivation.png
```

### 3. Main interactive sine-theta explorer

```bash
uv run --extra vtk python -m dkvis.vtk_sine_theta
```

This main scene has been made more **slide-friendly**. At every slider position
it keeps the exact subspace, the trial subspace, the trial vector, its exact
projection, the complementary sine block, the residual, and the theorem panel
visible. The goal is that a screenshot at an arbitrary angle should still be
self-explanatory.

The scene simultaneously shows:

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
    --screenshot renders/sine-theta-main.png
```

## Manim animation

```bash
cd visualizations
uv run --extra manim python -m manim -pql dkvis/manim_sine_theta.py SineThetaScene
```

Invoke Manim through `python -m manim`, not the `.venv/bin/manim` console
script. Manim loads scene files by path, and the module invocation keeps the
`visualizations/` project root on `sys.path`, so `from dkvis...` imports resolve.

The Manim scene uses the same `SineThetaModel`. It animates the trial line while
keeping the exact subspace fixed, then displays the two identities that explain
the theorem geometrically:

```text
(I - P_U) v_theta = (0, sin(theta))
R(1) = (0, delta sin(theta))              [sharp default model]
```

## Proposition 4.4 counterexample

`dkvis.prop44.Prop44Model` encodes the exact `R^4` witness used by the Lean
refutation. With `U = span(e0,e1)`, the admissible competitor is

```text
W = 1/2 * [[ 1, -1, -1, -1],
           [ 1,  1,  1, -1],
           [-1, -1,  1, -1],
           [ 1, -1,  1,  1]]
V = W(U).
```

Both principal angles between `U` and `V` are `pi/4`, strictly below the
printed `pi/3` threshold. The Davis--Kahan direct rotation is

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

### Explanatory introduction VTK scene

```bash
uv run --extra vtk python -m dkvis.vtk_prop44_intro
```

This static slide-oriented scene introduces the actual geometric objects before
animation:

- ambient space `R^4`;
- source plane `U = span(e0,e1)`;
- destination plane `V = R(U) = W(U)`;
- the two exact invariant-plane decompositions used for the direct rotation and
  the competitor.

It keeps the source pieces and endpoint image pieces visible in all four exact
2D restriction panels, so screenshots can be dropped directly into slides.

Generate a deterministic PNG:

```bash
mkdir -p renders
uv run --extra vtk python -m dkvis.vtk_prop44_intro \
    --no-interact \
    --screenshot renders/prop44-intro.png
```

### Interactive four-plane VTK explorer

```bash
uv run --extra vtk python -m dkvis.vtk_prop44
```

The main VTK scene intentionally uses **no 4D-to-3D projection**. Instead it
shows four exact two-dimensional invariant-plane restrictions of the actual
`R^4` operators:

```text
left column -- direct rotation R
  span(e0,e3): +45 deg
  span(e1,e2): -45 deg

right column -- competitor W
  span(m0,m1): +90 deg
  span(m2,m3):   0 deg (fixed)
```

Unlike the first revision, the source and destination remain visible at every
slider position. Orange/cyan arrows show the source directions (or their
projected pieces), green/red arrows show the endpoint image, and white arrows
show the current interpolation state. That makes arbitrary screenshots much
more self-explanatory for talks.

Generate a deterministic PNG of the improved main scene:

```bash
mkdir -p renders
uv run --extra vtk python -m dkvis.vtk_prop44 \
    --t 0.70 \
    --no-interact \
    --screenshot renders/prop44-four-plane.png
```

These are different decompositions of `R^4`. The direct-rotation planes are
principal/invariant planes for `R`; the `m` planes are the moving and fixed
invariant planes for `W`. The display does not identify them with one another.

A single `MOTION t` slider animates all four local rotations from the identity
to the endpoint. Only `t=1` is the Proposition 4.4 comparison. Each panel
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

to the full trace norm. At the endpoint this makes the counterexample visible
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
projection. They are deliberately labeled as *different* decompositions:

```text
R:  span(e0,e3) rotates +45 deg
    span(e1,e2) rotates -45 deg

W:  span(m0,m1) rotates +90 deg
    span(m2,m3) is fixed
```

It then compares the four singular values of the full displacement. This is the
key trace-norm mechanism: the direct rotation has four equal nonzero chord
lengths, while the competitor has two larger chord lengths and two zeros; the
sum is nevertheless smaller for the competitor.

## Validation

The unit tests check the geometric decomposition, the residual formula, sharp
cases, and several non-sharp cases:

```bash
cd visualizations
uv run --extra test pytest -q
```

Useful smoke tests for the VTK renderer are:

```bash
uv run --extra vtk python -m dkvis.vtk_sine_theta_intro \
    --theta 35 --no-interact --screenshot renders/sine-intro-smoke.png

uv run --extra vtk python -m dkvis.vtk_sine_theta_motivation \
    --theta 35 --no-interact --screenshot renders/sine-motivation-smoke.png

uv run --extra vtk python -m dkvis.vtk_sine_theta \
    --theta 40 --no-interact --screenshot renders/sine-main-smoke.png
```

## Planned extensions

Keep the shared numerical model / multiple-renderer split. The next natural
scenes are:

1. `tan Theta`: show the trial subspace as a graph over the exact subspace and
   visualize tangent as slope.
2. `sin 2Theta`: show the doubled-angle geometry, including the reflection
   interpretation.
3. `tan 2Theta`: animate the sharp 2x2 model and the approach to the `pi/4`
   barrier.
4. Proposition 4.4 equation (4.3): add a separate scene explaining why the
   printed principal-plane lower-bound step fails on the same witness.
