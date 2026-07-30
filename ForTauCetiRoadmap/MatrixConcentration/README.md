# Roadmap: sample moments and matrix concentration

**Topic T20 of the candidate design.** Five modules. Depends on T19. Consumed by
nothing — a leaf, and the applied end of the development. Part of the statistical
track; see the T18 roadmap for how the three compose.

## The theorem this topic exists for

For a random real-symmetric `n × n` matrix `Ŝ(ω)` entrywise close in mean square
to a fixed symmetric `A` — `∫ (Ŝ_{kl} − A_{kl})² ≤ v` for every entry — Chebyshev
and a union bound over the `n²` entries give an entrywise deviation bound with
high probability, and T19's `‖toEuclideanLin A‖ ≤ n · ‖A‖_∞` converts that into
an **operator-norm** bound.

That operator-norm bound is exactly the hypothesis T18 wants. The three topics
meet here: T20 produces `‖Ŝ − A‖ ≤ ε` with probability `1 − δ`, T19 makes the
spectral quantities measurable, and T18 turns the norm bound into a subspace
rotation bound under a population gap.

## The route is deliberately elementary

**Chebyshev plus a union bound, not a matrix Bernstein or Tropp-style
inequality.** That is a real choice and a reviewer should see it as one.

The elementary route costs a factor of `n` (from the entrywise-to-operator-norm
comparison) and a union bound over `n²` entries. A matrix concentration
inequality would give a dimension-dependence of `log n` instead. What it would
also require is the matrix Laplace transform machinery, which is not in Mathlib.

So the trade is: a weaker constant, obtained from ingredients that exist, versus
a sharper constant requiring a substantial new development. For a first
submission the elementary route is the right one — but the roadmap should say
that the bound is **not sharp in the dimension**, so that nobody reads the
`n`-dependence as intrinsic.

## The modules

| Module | Role |
|---|---|
| `SampleMean` | For square-integrable random vectors with common mean `μ`, the mean-squared error of `r⁻¹ ∑ₖ Xₖ` about `μ` is `r⁻²` times the sum of the individual errors. |
| `Variance` | The scalar moment facts the above rests on. |
| `SampleCovariance` | The sample covariance operator. |
| `CenteredScatter` | The centered scatter `∑ᵢ (zᵢ − mean z) ⊗ (zᵢ − mean z)`, with an **exact add-one update** as its primary theorem. |
| `MatrixConcentration` | Chebyshev + union bound ⇒ the entrywise, hence operator-norm, deviation bound. |

`CenteredScatter`'s add-one update is worth noting: it is an *exact* identity for
how the scatter changes when one sample is appended, not an estimate. That makes
the sample covariance computable incrementally and is the kind of statement that
is easy to get wrong by one term — the centering means the new point shifts the
mean as well as adding a summand.

## What a reviewer should check

1. **That the `n`-dependence is honest and stated** — see above. The bound is
   elementary and dimension-suboptimal by design.
2. **That `CenteredScatter`'s add-one update is exact**, not an inequality, and
   accounts for the mean shift.
3. **That `SampleMean`'s `r⁻²` scaling is for the *sum* of individual errors**,
   which is the independence-free form; assuming independence would give `r⁻¹`
   times an average and a stronger theorem than is proved.

## Prerequisites

T19. Nothing depends on this topic.
