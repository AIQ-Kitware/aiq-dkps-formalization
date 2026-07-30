# Roadmap: a finite-mass Fourier kernel for the reciprocal on `1 ≤ |x|`

**Topic T12 of the candidate design.** Eight modules, no prerequisites: this is
one of four topics that `scripts/check_tauceti_roadmap_topics.py --needs`
reports as independent, so it can be submitted without waiting on any other.

## The theorem this topic exists for

There is an explicit, integrable `k : ℝ → ℂ` whose Fourier integral reproduces
the reciprocal function on the whole exterior region:

```lean
theorem reciprocalKernel_fourier (x : ℝ) (hx : 1 ≤ |x|) :
    (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) = 1 / (x : ℂ)
```

and whose total mass is *exactly* the smallest constant this representation can
have:

```lean
theorem integral_norm_reciprocalKernel :
    (∫ t : ℝ, ‖reciprocalKernel t‖) = Real.pi / 2
```

Both halves matter, and the second is the reason the topic is worth a roadmap
rather than a lemma. Any `k` with the first property gives, by substituting a
pair of separated self-adjoint operators for `x`, a bound on the solution of a
Sylvester equation with constant `‖k‖₁`; the sharp constant `π / 2` in that
estimate *is* this kernel's `L¹` norm. A kernel with the right transform and a
worse mass proves a weaker theorem.

The mathematics is due to Haagerup and Zsidó. It is specified here
intrinsically — as a statement about one scalar kernel on the line — and
nothing downstream is assumed.

## Statement of the objects

```lean
def weight (y : ℝ) : ℝ := Real.tanh (Real.pi * y / 2)

def weightLaplaceTransform (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y)

def realKernel (t : ℝ) : ℝ := (Real.sin t / 2) * weightLaplaceTransform t

def reciprocalKernel (t : ℝ) : ℂ := -Complex.I * (realKernel t : ℂ)
```

Four definitions in one chain: a hyperbolic weight, its Laplace transform, the
sine multiple of that transform, and a rotation by `-i` that makes the Fourier
identity come out as `1 / x` rather than `i / x`. The kernel is odd, so the
transform is odd, and the two-sided statement follows from the `1 ≤ x` case by
reflection — which is exactly how `reciprocalKernel_fourier` is proved.

## Why the constant is `π / 2` and not something else

The mass computation is not an estimate. `‖reciprocalKernel t‖ = |realKernel t|`
pointwise, `|realKernel t| = ½ |sin t| · weightLaplaceTransform t`, and
Tonelli on the product `Ioi 0 × ℝ` turns the total mass into

```
½ ∫_{y>0} weight y · (∫_ℝ |sin t| e^{-y|t|} dt) dy
```

whose inner integral is closed-form,

```lean
theorem integral_abs_sin_mul_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|)) =
      2 * ((1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2)))
```

and whose product with `tanh (π y / 2)` collapses — the hyperbolic weight is
precisely the reciprocal of the periodic factor — leaving `∫_{y>0} (1+y²)⁻¹ dy
= π / 2`. **The weight is chosen to make that cancellation exact.** That is the
one sentence a reader should take away about why `tanh (π y / 2)` appears at
all, and it is the sentence the module docstrings should not make them
reconstruct.

The exchange of integrals is licensed by a single product-integrability
certificate, `integrable_kernel_prod`, which is also what the later Fourier
exchange uses.

## Existing foundations

Mathlib supplies the Fourier transform `𝓕` with its inversion theorem,
`MeasureTheory.Integrable` and the Bochner integral over `ℝ`, `ExpDecay`,
`Real.tanh` and the exponential/trigonometric API, Poisson summation, and
`Analysis.PSeries` for the lattice sums.

A sorry-free staged implementation exists under `ForTauCeti/`, in eight modules
(`scripts/check_tauceti_roadmap_topics.py --topic T12`):

| Module | Carries |
|---|---|
| `Analysis/Fourier/ExponentialAbs.lean` | the two-sided exponential: its oscillatory Laplace transform, its Fourier transform in Mathlib's normalization, decay `=o[cocompact ℝ]` of every real power, and the integrability certificates |
| `Analysis/Fourier/Poisson/CauchyLattice.lean` | the geometric lattice sum, Poisson summation against the Cauchy kernel, and the odd-pole expansion `weight y / y = (4/π) ∑' n, (y² + (2n+1)²)⁻¹` |
| `Analysis/SpecialFunctions/Integral/RationalQuadratic.lean` | the elementary Cauchy-type integrals over `Ioi 0`, the reciprocal step-difference telescoping series, and `integral_weight_mul_reciprocal_difference` |
| `Analysis/SpecialFunctions/Integral/SineLaplace.lean` | the Laplace transform of `|sin|` by periodic decomposition, with the generic `Real.abs_sin_add_nat_mul_pi` and `Real.abs_sin_abs` |
| `Analysis/Fourier/HaagerupZsido/Defs.lean` | the four definitions above and their positivity, parity, continuity and measurability API |
| `Analysis/Fourier/HaagerupZsido/Integrability.lean` | `integrable_kernel_prod`, integrability of the kernel, and the exact mass `π / 2` |
| `Analysis/Fourier/HaagerupZsido/Fourier.lean` | the oscillatory sine transform and the exterior identity `reciprocalKernel_fourier` |
| `Analysis/Fourier/HaagerupZsido/Kernel.lean` | a re-export aggregate, so one import still gives the whole `TauCeti.HaagerupZsido` API |

These results still require Tau Ceti review and migration.

## Pinned conventions

### The kernel is complex-valued and the real one is kept

`realKernel : ℝ → ℝ` and `reciprocalKernel : ℝ → ℂ` both exist, related by
`reciprocalKernel = -i · realKernel`. **Both stay.** The real kernel is what the
mass computation and every positivity argument work with; the complex one is
what states the Fourier identity without an `i` on the right-hand side. Folding
them into one definition would put a `Complex.ofReal` in the middle of every
real inequality, which is worse than a two-line bridge.

### `Ioi 0`, not `Ici 0`, in the Laplace transform

The weight vanishes at `0`, so the two agree; `Ioi` is chosen because every
lemma about the transform is stated for `0 < y`, and `Mathlib`'s
`integrableOn_Ici_iff_integrableOn_Ioi` is a one-step bridge when a consumer
wants the closed ray.

### Mathlib's Fourier normalization

`fourier_cexp_neg_two_pi_mul_abs` is stated for `𝓕` with Mathlib's `2π`
convention, while `reciprocalKernel_fourier` is stated as a bare integral
against `exp (i t x)`. This is deliberate: the first is a fact about Mathlib's
transform and belongs in its normalization; the second is the statement a
spectral-theory consumer substitutes an operator into, where the `2π` would have
to be undone immediately. The bridge is explicit rather than implied by a
scaling convention.

### Namespace

Everything except the four generic lemmas lives in `TauCeti.HaagerupZsido`. The
generic ones are placed where they belong and named for what they say:
`Real.abs_sin_add_nat_mul_pi`, `Real.abs_sin_abs`, and
`MeasureTheory.integrable_iff_integrableOn_Ioi_of_even`. A reviewer should be
able to take those three without taking the topic.

## What remains to land

The staged results above must be reviewed and migrated. The genuinely missing
mathematics is narrow, and it is at the two ends:

- **A minimality statement.** The roadmap claims `π / 2` is the sharp constant;
  the library proves the kernel *attains* it. That no admissible kernel does
  better is currently an external citation, not a Lean theorem. Either prove it
  or say plainly in the module docstring that `π / 2` is an upper bound with a
  matching known lower bound from the literature. **Recommend the latter for the
  first submission** — the sharpness proof is a separate topic, and overclaiming
  it in a docstring is worse than a one-line honest note.
- **Theorem-level acceptance examples**, in the shape Tau Ceti asks for: the
  identity applied to one concrete `x`, and the mass identity used to bound one
  concrete convolution.

Both are additions; neither changes a statement below.

## Ordering and PR slices

The import graph inside the topic is a chain, and it slices along it:

1. `ExponentialAbs` + `SineLaplace` — scalar transforms, no kernel in sight.
   Independently useful and independently reviewable.
2. `CauchyLattice` + `RationalQuadratic` — Poisson summation and the odd-pole
   expansion, i.e. everything about the *weight*.
3. `HaagerupZsido/{Defs, Integrability, Fourier}` — the kernel, its mass, and
   the exterior identity.

Slice 1 is the cheapest possible first contact with Tau Ceti review: two
modules, no new definitions that survive into the API, and every statement a
classical closed-form integral.

## References

* U. Haagerup and L. Zsidó, on the Fourier representation of the reciprocal on
  the exterior region and the resulting `π / 2` constant for separated Sylvester
  equations. The reconstruction this library follows is
  `prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`,
  which traces the `π / 2` provenance chain in the form used here.

## Mathlib References

* `Mathlib.Analysis.Fourier.Inversion` — `𝓕` and inversion.
* `Mathlib.MeasureTheory.Integral.ExpDecay` — integrability of exponentially
  decaying integrands.
* `Mathlib.Analysis.PSeries` — summability of the lattice sums.
* `Mathlib.Analysis.SpecialFunctions.Trigonometric.*` — `Real.tanh`, `Real.sin`.

## Provenance and coordination

The eight modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.) and carry `Spectra influence: none`. The topic's
only downstream consumer here is T16 (Sylvester equations and the Rosenblum
theorem), which uses `reciprocalKernel_fourier` and the `π / 2` mass through
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Internal/ReciprocalMultiplier/`
— that dependency is what makes T12 worth submitting first, and it is
one-directional.

Written 2026-07-29 by `jon (yardrat)` under lane ROADMAP-WRITE, which asks for
one topic per claim; the other fifteen topics are unwritten and free. Module
paths here are the post-`PLACE-SYLV` ones: that lane moved
`Analysis/Fourier/HaagerupZsidoKernel.lean` into
`Analysis/Fourier/HaagerupZsido/Kernel.lean`, beside the three modules it
aggregates.
