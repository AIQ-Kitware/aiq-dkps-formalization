# Roadmap: the bounded Borel functional calculus and projection-valued measures

**Topic T14 of the candidate design.** Ten modules, no prerequisites — one of the
independent topics `scripts/check_tauceti_roadmap_topics.py --needs` reports, and
the one the whole unbounded stack (T15) rests on.

## What is missing from Mathlib, exactly

Mathlib has the **continuous** functional calculus of a normal element and no
Borel one; it has `Measure`, `StieltjesFunction` and Riesz–Markov–Kakutani, and
no spectral measures. This topic supplies the step between: for a normal
`a : H →L[ℂ] H` on a complex Hilbert space, a bounded Borel symbol `f` on
`spectrum ℂ a` acts as a bounded operator, the assignment is a `*`-homomorphism,
and applying it to indicator functions yields a projection-valued measure.

Everything downstream in the library that says *spectral projection* — the
spectral subspaces of an unbounded self-adjoint operator, the Cayley-transform
spectral measure, the block decomposition behind the Sylvester spectral gap —
comes from here. It is a prerequisite, not a convenience.

## The construction, and why it is built this way

The route is **diagonal measures → polarisation → operator → PVM**, and each
arrow is one module.

1. **`BorelCalculus/DiagonalMeasure.lean`.** For a vector `ξ`, the functional
   `f ↦ ⟪ξ, cfcHom f ξ⟫` on `C(spectrum ℂ a, ℂ)` is positive, so
   Riesz–Markov–Kakutani gives a finite regular Borel measure `diagMeasure ha ξ`
   with `∫ f ∂(diagMeasure ha ξ) = ⟪ξ, cfcHom ha f ξ⟫`.

2. **`BorelCalculus/Polarization.lean`.** Polarise:
   `pair f ψ ξ = ¼ Σ_{k<4} iᵏ ∫ f ∂(diagMeasure (ξ + iᵏ • ψ))`. For continuous
   `f` this *is* `⟪ψ, cfcHom f ξ⟫`; for bounded Borel `f` it is the definition of
   what the matrix element ought to be.

3. **`BorelCalculus/Operator.lean`.** `pair ha f` is sesquilinear and bounded,
   hence the matrix-element form of a unique `borelCalculus ha hf : H →L[ℂ] H`.

4. **`BorelCalculus/Multiplicative.lean`.** The calculus extends the continuous
   one, its diagonal matrix elements are the diagonal integrals, and it is
   multiplicative.

5. **`BorelCalculus/PVM.lean`** and **`ProjValMeasure/{Basic,Additivity}.lean`.**
   Indicators give projections; the projections assemble into a
   `TauCeti.ProjValMeasure` on the Borel sets of `ℝ`.

**The transport principle is the whole proof, and it is isolated on purpose.**
Every identity is checked for a *continuous* symbol — where it is a fact about
`cfcHom`, hence free — and then moved to the Borel symbol by `ε` in the `L¹` of
the *finite* sum of diagonal measures occurring in the statement
(`exists_continuous_pair_close`, `norm_pair_sub_pair_le`). An identity mentioning
finitely many vectors mentions finitely many diagonal measures, so one finite
measure controls it. A reviewer who reads only `Polarization.lean` has read the
method.

One consequence is worth stating because it looks like an oversight and is not:
**multiplicativity is the only step that needs the transport twice, in a fixed
order.** The continuous approximant `p` of `f` is chosen first, and the tolerance
for the approximant `q` of `g` is then `ε / (1 + ‖p‖)`. There is no uniform bound
over approximants, so the second tolerance genuinely depends on the first.

## Pinned conventions

### The PVM carries its diagonal measures as data

`ProjValMeasure` bundles the projection field *and* the scalar measures
`diag ξ`, welded together by `inner_proj`. **Countable additivity is therefore
never stated**: it already lives inside `Measure ℝ`. Idempotence,
self-adjointness, positivity and finite additivity are theorems, not fields.
An alternative design — projections as the only data, additivity as an axiom —
was not taken, because it would put a summability side-condition on every
consumer.

### PVMs live on `ℝ`, and the relabelling is explicit

`TauCeti.ProjValMeasure` is a measure on the Borel sets of `ℝ`, while the
spectrum of a normal operator lives in `ℂ`. `BorelCalculus/PVM.lean` therefore
takes an arbitrary measurable **relabelling** `κ : spectrum ℂ a → ℝ` rather than
assuming self-adjointness. For a self-adjoint operator `κ` is the real part; for
the Cayley transform of an *unbounded* self-adjoint operator it is the inverse
Cayley map, which is exactly what T15 needs and exactly why `κ` is a parameter
and not a special case.

### Three measure-theoretic modules are generic and stay generic

`MeasureTheory/CfcMeasurable.lean` (for fixed continuous `f`, `ω ↦ cfc f (a ω)`
is measurable — with no measurable selection of an eigenbasis),
`MeasureTheory/CompactExists.lean` (`{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable for
a Carathéodory `F` on a compact `S`, again with no selection theorem), and
`MeasureTheory/HellySelection.lean` (Helly selection and the Stieltjes measure of
a monotone limit) are stated for their own hypotheses in `MeasureTheory`, not for
this topic's operators. A reviewer can take any of the three without taking the
calculus.

## Existing foundations

Mathlib supplies `cfcHom` and the continuous functional calculus of a normal
element, `IsStarNormal`, Riesz–Markov–Kakutani, `Measure`, `StieltjesFunction`,
`Lp` spaces, and dominated convergence.

A sorry-free staged implementation exists under `ForTauCeti/`, in ten modules
(`scripts/check_tauceti_roadmap_topics.py --topic T14`): the five
`Analysis.InnerProductSpace.BorelCalculus.*`, the two
`Analysis.InnerProductSpace.ProjValMeasure.*`, and the three
`MeasureTheory.*` above. These results still require Tau Ceti review and
migration.

## What remains to land

- **A statement of uniqueness.** The calculus is constructed and shown
  multiplicative; that it is the *unique* bounded extension of `cfcHom` agreeing
  on continuous symbols is the natural characterisation a reviewer will ask for,
  and it is not currently a theorem.
- **The spectral theorem as a headline.** The pieces are here; no single
  statement says *a self-adjoint bounded operator is the integral of the
  identity against its PVM*. Worth stating for its own sake, since it is what a
  reader looks for when they open the topic.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

None of these changes a statement already staged.

## Ordering and PR slices

1. `MeasureTheory/{CfcMeasurable, CompactExists, HellySelection}` — three
   independent measure-theoretic additions, reviewable with no operator theory
   in sight.
2. `BorelCalculus/{DiagonalMeasure, Polarization, Operator, Multiplicative}` —
   the calculus, ending at the homomorphism property.
3. `ProjValMeasure/{Basic, Additivity}` and `BorelCalculus/PVM` — the structure
   and the measure it produces.

Slice 2 is the one that carries the argument; slices 1 and 3 are short.

## Mathlib References

* `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.*` — `cfcHom`.
* `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.*`.
* `Mathlib.MeasureTheory.Measure.Stieltjes` — `StieltjesFunction`.
* `Mathlib.MeasureTheory.Integral.DominatedConvergence`.

## Provenance and coordination

The ten modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.). The route was chosen against Spectra's
Herglotz/Poisson construction; the comparison is recorded in
`dev/tauceti/spectra-removal-plan.md`, and
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` carries
the provenance of the route itself.

T14 is rung **K** of `dev/tauceti/submission-ladder.md`. Its only downstream
consumer here is T15 (unbounded self-adjoint operators on `LinearPMap`), which
takes the PVM through the Cayley transform — see
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean`.

Written 2026-07-29 by `jon (yardrat)` under lane ROADMAP-WRITE, one topic per
claim. T01, T21 and T22 remain independent and unwritten.
