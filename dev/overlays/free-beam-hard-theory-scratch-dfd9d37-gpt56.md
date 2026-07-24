# Hard free-beam scratch campaign

Base commit: `dfd9d37ebc86`

This package is an additive mathematics draft for the unclaimed Section 9
free-beam lane. It does not modify the active nonacute polar/Section 3 files
reserved for Opus.

## Scope

The overlay adds 17 Lean modules containing roughly 2,800 lines of proof
drafts. The campaign is divided into three layers.

### Abstract operator layer

`Abstract/PositiveSurjectiveCriterion.lean`

* Generalizes the positive von Neumann criterion used in Spectra.
* Proves density from positivity and surjectivity of `1 + A`.
* Proves that a symmetric nonnegative partial operator with surjective `1 + A`
  is self-adjoint.
* Packages the result for `DavisKahanExt.ClosedOperator`.

`Abstract/BoundedInverseRealization.lean`

* Proves dense range of a bounded self-adjoint injective operator.
* Constructs its inverse on its range as a closed densely defined operator.
* Proves symmetry, positivity, surjectivity of `1 + R⁻¹`, and self-adjointness.

`Abstract/CoerciveFormResolvent.lean`

* Represents a coercive form by a bounded positive self-adjoint operator on a
  form Hilbert space.
* Constructs `R = j A⁻¹ j*`.
* Proves the variational identity, injectivity, symmetry, positivity, and
  self-adjointness of `R`.
* Constructs the associated positive self-adjoint unbounded operator `R⁻¹`.

`Abstract/CompactGraphEmbedding.lean`

* Defines sequential compactness predicates matching the existing Section 9
  interface.
* Proves equivalence between compactness of a bounded resolvent and compactness
  of the graph-domain embedding of its inverse.

`Abstract/FormCompactness.lean`

* Proves that compactness of the form embedding implies compactness of the
  form resolvent and the associated operator graph.

`Abstract/BoundedGraphCompactness.lean`

* Proves that sequential graph compactness is invariant under adding a bounded
  perturbation.

`Abstract/TraceKernelModel.lean`

* Packages a maximal fourth-order graph Hilbert space, continuous ambient
  embedding, fourth derivative, and four endpoint traces.
* Constructs the free trace kernel, its ambient domain, transported fourth
  derivative, and a closed-operator wrapper.

`Abstract/GraphClosedness.lean`

* Constructs the graph embedding `u -> (u,D4u)`.
* Identifies its range with the ambient partial-operator graph.
* Converts a graph-norm lower bound into graph closedness through the
  anti-Lipschitz closed-range theorem.

`Abstract/MaximalDomainTransport.lean`

* Transports the maximal graph space, derivative, and endpoint traces into
  ambient submodules.
* Proves the free ambient domain is exactly the joint trace kernel.
* Proves the free derivative agrees with the maximal derivative.

### Classical ODE layer

`Classical/CharacteristicConverse.lean`

* Supplies a nonzero kernel vector for the singular two-by-two boundary matrix.
* Proves the right-boundary converse.
* Proves that every nonzero characteristic root produces a nontrivial free
  classical mode.
* Proves the root/free-mode equivalence at nonzero frequency.

`Classical/ModeData.lean`

* Bundles the closed-form trigonometric-hyperbolic mode as `FourthOrderData`.
* Connects the characteristic converse to the smooth Green infrastructure.
* Proves nontriviality through the initial value/velocity jet.
* Produces smooth free eigenmode data for each nonzero characteristic root.

`Classical/AffineModes.lean`

* Constructs real and complex affine zero modes explicitly.
* Proves free boundary conditions, zero fourth derivative, and injectivity of
  the two-parameter representation.

`Classical/RootLocalizationReduction.lean`

* Proves continuity and basic sign exclusions for the characteristic function.
* Defines a finite scalar certificate for the first positive root.
* Proves that split root-exclusion data supplies the existing
  `PositiveRootLocalization` interface and the `> 500` consequence.

### Analytic assembly layer

`Analytic/ShiftedBeamRealization.lean`

* Models the coercive shifted bending form.
* Constructs the shifted operator and subtracts the bounded identity.
* Proves the unshifted quadratic form equals the bending energy.
* Proves nonnegativity, self-adjointness, and graph compactness of the beam
  operator from the abstract form inputs.

`Analytic/EigenmodeReduction.lean`

* Separates compact-resolvent discreteness from one-dimensional ODE regularity.
* Proves that a classified positive eigenpair yields a characteristic root.
* Derives the positive-spectrum characterization and the `> 500` bound from
  point-spectrum and regularity inputs.

`Analytic/FoundationAssembler.lean`

* Builds the existing paper-facing `SobolevTraceFoundation` from a graph-space
  trace model and the remaining high-level analytic facts.
* Automatically discharges ambient maximal/free domain transport, trace-kernel
  identification, density, graph closedness, and derivative agreement.

`HardTheoryAll.lean` imports the complete new campaign but is deliberately not
added to the already compiled `Scratch.FreeBeam.All` aggregate until repair.

## Mathematical status

These are full proof drafts, not theorem stubs. There are no proof-escape
constructs in the new Lean files. The environment used to produce this overlay
does not contain Lean, so none of the files has been elaborated here.

The strongest mathematical progress is independent of exact Sobolev APIs:

1. a complete bounded-resolvent-to-unbounded-self-adjoint construction;
2. a form-resolvent construction and compactness bridge;
3. graph-Hilbert transport of free endpoint traces;
4. the missing converse to the classical characteristic equation;
5. exact shifted-to-unshifted beam assembly;
6. a clean reduction of positive spectral classification to point-spectrum
   discreteness plus ODE regularity.

The genuinely unresolved concrete analysis is now concentrated in:

* constructing a concrete interval `H2` form Hilbert space and `H4` graph
  Hilbert space;
* proving continuous endpoint traces;
* proving density of a smooth free core;
* proving compactness of the `H2 -> L2` embedding;
* identifying the operator associated to the shifted form with `D4 + I` and
  the natural free boundary conditions;
* proving regularity/classification of domain eigenvectors;
* completing rigorous scalar first-root exclusion below the first positive
  root;
* constructing the isometric affine-kernel equivalence.

## Expected compiler repairs

The drafts were written against APIs visible in the base source but without an
elaborator. Repair should preserve statements and proof architecture.

Likely mechanical issues include:

* exact `LinearEquiv.ofInjective` argument inference;
* coercions between range submodules and ambient spaces;
* `ContinuousLinearMap.prod`, multiplication, and inverse simplification;
* orientation of `ContinuousLinearMap.adjoint_inner_left`;
* exact spelling of `Real.le_sqrt_of_sq_le` side conditions;
* rewriting `ClosedOperator.addBounded_apply` through definitionally equal
  domain subtypes;
* continuity spelling for complex affine functions;
* simplification of the identified mode at `0`;
* nested intersections in the closed trace-kernel proof;
* `simpa` boundaries when identifying the assembled closed operator with the
  structure expected by `SobolevTraceFoundation`.

If a theorem turns out to need an additional hypothesis, do not insert one
silently. Report the exact mathematical gap and adjust the corresponding
scratch abstraction explicitly.

## Spectra provenance

Two generic arguments are adapted from the vendored Spectra snapshot at commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`, authored by Adam Bornemann and
released under Apache-2.0:

* `Spectra/Modular/TomitaTakesaki/VonNeumannTstarT.lean`, declaration
  `Spectra.TomitaTakesaki.modularOp_isSelfAdjoint` supplies the proof route for
  the positive-surjective self-adjointness criterion.
* `Spectra/Modular/Tomita/BoundedPicture.lean`, private declaration
  `denseRange_of_selfAdjoint_injective` supplies the dense-range argument.

The adapted declarations have explicit source headers. The machine-readable
ledger in `dev/upstream-extraction/free-beam-hard-theory-provenance-dfd9d37.json`
records the mapping. These arguments should eventually move to a generic
library with the attribution preserved.

## Suggested repair order

1. `Abstract/PositiveSurjectiveCriterion.lean`
2. `Abstract/BoundedInverseRealization.lean`
3. `Abstract/CompactGraphEmbedding.lean`
4. `Abstract/TraceKernelModel.lean`
5. `Abstract/GraphClosedness.lean`
6. `Abstract/MaximalDomainTransport.lean`
7. `Abstract/CoerciveFormResolvent.lean`
8. `Abstract/FormCompactness.lean`
9. `Abstract/BoundedGraphCompactness.lean`
10. `Classical/CharacteristicConverse.lean`
11. `Classical/ModeData.lean`
12. `Classical/AffineModes.lean`
13. `Classical/RootLocalizationReduction.lean`
14. `Analytic/ShiftedBeamRealization.lean`
15. `Analytic/EigenmodeReduction.lean`
16. `Analytic/FoundationAssembler.lean`
17. `HardTheoryAll.lean`

Compile each file independently before using the aggregate import. Promote
small generic results only after their local APIs have stabilized.

## Promotion status (2026-07-24, jon window A)

**PROMOTED out of Scratch into the maintained MathAhead tree.** The whole
campaign compiles and moved from `DavisKahan/Experimental/Scratch/FreeBeam/**`
to `DavisKahan/Experimental/MathAhead/HiddenFoundations/FreeBeam/**` (namespace
`…Experimental.Scratch.FreeBeam` → `…Experimental.MathAhead.HiddenFoundations.FreeBeam`).
All 16 hard-theory modules plus the 3 smooth-core files and both aggregates now
build; the aggregate is `FreeBeam.All` (smooth core + `HardTheoryAll`), wired
through `MathAhead.Section9All` into `MathAhead.All` / `HiddenFoundations.All`.
`Scratch/All.lean` no longer imports FreeBeam. `MathAhead.Section9All` builds
green (8799 jobs); `Scratch.All` builds green (9003 jobs); zero proof-escape
terms in the promoted tree.

The three genuinely unresolved concrete inputs listed above (interval `H2`/`H4`
space, continuous traces + Rellich compactness, and the first-root localization
`4.73 < firstPositiveRoot`) remain packaged as `structure` fields — the campaign
is reduction machinery, so this promotion does **not** discharge the
`Frontier/Section9Analytic.lean` obligations; grounding those needs the concrete
inputs constructed.
