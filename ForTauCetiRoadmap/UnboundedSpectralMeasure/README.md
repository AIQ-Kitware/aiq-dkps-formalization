# Roadmap: the spectral measure of an unbounded self-adjoint operator, and Stone

**Topic T15c of the candidate design.** Twelve modules; needs T13 (one-parameter
unitary groups), T14 (Borel calculus and PVMs) and T15b (resolvents). The deepest
topic in the unbounded stack, and the one the Davis–Kahan sin-Θ theory consumes.

## The two theorems

**The spectral measure.** A self-adjoint `A : H →ₗ.[ℂ] H` carries a
projection-valued measure on the Borel sets of `ℝ`, obtained by relabelling the
Borel calculus of its Cayley transform:

```lean
noncomputable def spectralPVM (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
```

with the resolvent formula identifying `R(z)` as the calculus of
`x ↦ (x - z)⁻¹`, the spectral projections `specProjection hA B hB` of a Borel set,
and the reduction `specRestrict hA B hB` of `A` to a spectral subspace — itself
self-adjoint.

**Stone, uniqueness half.** The unitary group of `A` determines `A`:

```lean
-- generator (genToGroup hA) = A
```

## Why the Cayley transform, and where the junk goes

`U = (A - i)(A + i)⁻¹` is a *bounded unitary*, so it carries T14's Borel calculus
directly; relabelling `spectrum ℂ U` by the inverse Cayley map `w ↦ i(1+w)/(1-w)`
turns that calculus into a measure on `ℝ`. This is the route the library chose
over Herglotz/Poisson, and `dev/tauceti/spectra-removal-plan.md` records the
comparison.

**The relabelling blows up at `w = 1`, which can lie in the spectrum**, so the
construction is only faithful because the diagonal measures give `{1}` no mass.
That is `diagMeasure_cayley_preimage_one`, and its proof is short and worth
knowing: `(1 - U)` annihilates the spectral projection of `{1}` because the symbol
`(1 - w)·1_{{1}}(w)` is identically zero, while `1 - U` is `2i` times the resolvent
`(A + i)⁻¹` and hence injective. **A roadmap that omitted this would be hiding the
one place the construction could have failed.**

## Pinned conventions

### Yosida before Stone, and the approximants are named

The unitary group is built from bounded approximants —
`yosidaApprox A n = n² R(in) - in` and its symmetrised form — rather than by
exponentiating `A` directly. They are public and named because the convergence
statements are about them, not about a limit that appears from nowhere.

### Maximality is proved once and used to identify operators

`SelfAdjointMaximal.lean` proves that `A ≤ B` with both self-adjoint forces
`A = B`. **This is why one never proves both inclusions** when identifying two
self-adjoint operators — most immediately when identifying the generator of the
unitary group of `A` with `A` itself, which is Stone's uniqueness half. One
69-line module removes a symmetric argument from every such proof.

### Grid, cut operator, block lower bound: the three shapes a block argument needs

The sin-Θ theory does not consume the spectral measure abstractly; it cuts the
line into cells and works cell by cell. Three modules exist for exactly that, and
each records what makes the naive version insufficient:

* `SpectralGrid.lean` — `gridCell ε k = [kε, (k+1)ε)` with measurability, pairwise
  disjointness and covering, plus which cells carry spectrum;
* `SpectralCutOperator.lean` — `SpectralMeasure.lean` proves `‖A y - c y‖ ≤ r ‖y‖`
  on a spectral range **pointwise**, and a Hilbert–Schmidt block argument needs it
  as an *operator* bound, because the ideal properties of the energy are stated
  for operators;
* `BlockLowerBound.lean` — the reassembly step: a family that splits vector norms
  turns a per-block lower bound into a global one, stated with **nothing about
  where the blocks come from** — no projections, no spectral theory, no
  countability, no convergence of `∑ blocks i` in any operator topology.

`SpectralProjectionGroup.lean` is the compatibility the cutting needs: `E_A(B)`
commutes with `exp(itA)`, or the blocks are not preserved by the flow.

### Support, stated as a null statement

`SpectralSupport.lean` gives the measure no mass on any Borel set of resolvent
points (`specProjection_eq_zero_of_subset_resolventSet`) rather than defining a
`support` and proving an inclusion. It is the last property the Davis–Kahan
development consumes that does not follow from the resolvent formula by algebra.

## Existing foundations

Mathlib supplies `LinearPMap` with `IsSelfAdjoint`, the continuous functional
calculus, `Measure` on `ℝ` with its Borel structure, and unitary groups.
T14 supplies the Borel calculus and `ProjValMeasure`; T15b supplies the resolvent
set, the named resolvent and openness; T13 supplies one-parameter unitary groups
and their generators.

A sorry-free staged implementation exists under `ForTauCeti/` (twelve modules;
`scripts/check_tauceti_roadmap_topics.py --topic T15c`). It still requires Tau
Ceti review and migration.

## What remains to land

- **The spectral theorem as one statement.** Every piece is here —
  `spectralPVM`, the resolvent formula, the support statement, the reduction — and
  no single declaration says *`A` is the integral of the identity against its
  spectral measure*. It is what a reader opens the topic looking for.
- **Stone's existence half as a named theorem.** `genToGroup` builds the group and
  `StoneUniqueness` identifies its generator; the packaged bijection between
  self-adjoint operators and strongly continuous one-parameter unitary groups is
  not stated.
- **Uniqueness of the spectral measure.** That a PVM with the resolvent formula is
  *the* spectral measure is the characterisation a reviewer will ask for, and it is
  not proved.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

## Ordering and PR slices

1. `LinearPMap/{YosidaApproximation, SelfAdjointMaximal}` — the bounded
   approximants and maximality. 821 + 69 lines, no spectral measure yet.
2. `LinearPMap/SpectralMeasure/Construction.lean` and `SpectralMeasure.lean` —
   the Cayley construction, the resolvent formula, spectral projections, and the
   reduction; then the bounded-set truncation and the resolvent gap.
3. `LinearPMap/{SpectralSupport, SpectralGapInverse, SpectralFormBounds,
   StoneUniqueness, SpectralProjectionGroup}` — the properties.
4. `LinearPMap/{SpectralGrid, SpectralCutOperator}` and `BlockLowerBound` — the
   three block-argument shapes. These are the most obviously reusable of the
   twelve and the least tied to this construction.

Slice 2 is the topic. Slice 4 could be submitted first if a reviewer prefers to
start with something small, since it depends on the construction only through the
cut operator.

## Provenance and coordination

The twelve modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.). The construction replaced a dependency on the
Spectra library: the target it displaced is
`Spectra.QuantumMechanics.SpectralTheory.spectralPVM`, the route comparison is in
`dev/tauceti/spectra-removal-plan.md`, and
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` carries
the provenance of the route itself.

T15c is rung **N** of `dev/tauceti/submission-ladder.md`. It is consumed by T16
(Sylvester and Rosenblum) and hence by T17.

**This topic was T15's last third until 2026-07-30.** Lane T15-SPLIT divided a
25-module, 6,700-line T15 into T15a/T15b/T15c;
[`../UnboundedOperators/README.md`](../UnboundedOperators/README.md) is the
pre-split roadmap covering all three.

Written 2026-07-30 by `jon (yardrat)` under lane ROADMAP-WRITE, claimed together
with T15a.
