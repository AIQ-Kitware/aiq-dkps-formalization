# Rebase note for the mathematics agent, 2026-07-20

Base your next drop on `a33cf4d` or later. This round was compiler repair only:
no theorem statement was weakened, no declaration was removed, and nothing was
left incomplete except where explicitly recorded below.

## What changed under you

### One of your two open obligations is closed

**Arbitrary-spectrum homogeneous uniqueness is proved and free of admissions.**

```
Spectra.QuantumMechanics.SpectralTheory.generatorIntertwiner_eq_zero_of_disjoint_spectrum
Spectra.QuantumMechanics.SpectralTheory.spectralProjection_spectrum_eq_id
Spectra.YosidaHille.GeneratorIntertwines.group
ForMathlib...ExactSinTheta.closedSylvester_homogeneous_eq_zero_complex
ForMathlib...ExactSinTheta.closedSylvester_homogeneous_eq_zero_real
```

all print exactly `[propext, Classical.choice, Quot.sound]`.

Your proof candidate was mathematically correct throughout. It failed only
because `GeneratorIntertwines.group` cited the density of the generator domain
without importing the module that proves it, so the theorem the whole
rectangular chain rests on did not exist. Do not redesign this argument.

### Both of your open obligations are now closed

The second one, **pairwise tensor spectral support**, is proved and free of
admissions. `Spectra.Spaces.Tensor.HilbertSchmidtSpectralGap` builds, and
`borelMeasure_sylvesterGroup_tmul`, `hasVectorSpectralGap_tmul`,
`spectralProjection_gap_eq_zero` and `hasVectorSpectralGap` all print exactly
`[propext, Classical.choice, Quot.sound]`.

As with the first obligation, the mathematics of your candidate was sound. It
failed on namespace and notation scoping, a dense induction applied rather than
eliminated, an integrand written in the source variable rather than the mapped
one, and a higher-order product factorisation that needed its factors named.
Nothing about the argument was redesigned.

### The tensor/operator dictionary and the flow layer above it

`Spectra.Spaces.Tensor.HilbertSchmidt` builds, and all ten endpoints are
admission-free, including `hasSum_columnTensor`, `norm_sq_eq_tsum_column_norm_sq`,
`existsUnique_tensor_iff_summable_columns` and the `ofOperator` inverse.

The whole subtree now builds. Measured serially on a quiet tree, every one of
`HilbertSchmidt`, `HilbertSchmidtFlow`, `HilbertSchmidtGeneratorBridge` and
`HilbertSchmidtSpectralGap` is at zero errors.

An earlier version of this note reported the dictionary alone as "the package",
which overstated it: at that point the flow layer still had thirteen errors and
the three modules above it were showing that one module's failures propagating.

The column expansion had to be rebuilt: it rested on five lemmas that do not
exist in Mathlib under any name. It now goes through `OrthogonalFamily`, with a
Bessel estimate proved from the Pythagoras identity and Cauchy--Schwarz. New
public lemmas you may cite: `norm_sum_columnTensor_sq`, `sum_column_norm_sq_le`,
`summable_column_norm_sq`, plus `toOperator_tmul'` (pure tensor with the second
factor left in the conjugate space) and `Conj.ofConj_adjoint_map`.

`ofOperator_toOperator`'s summability argument now reads
`summable_column_norm_sq b z`. `ofOperator` discards that argument
definitionally, so the theorem asserts exactly what it did before.

### Modules that went from red to green

| Module | Was | Now |
| --- | --- | --- |
| `Spectra.Spaces.Tensor.Hilbert` | latent notation bug | fixed |
| `Spectra.Spaces.Tensor.HilbertSchmidt` | 39 | 0 |
| `Spectra.YosidaHille.RectangularIntertwining` | 5 | 0 |
| `Spectra.SpectralTheory.SeparatedIntertwiner` | 5 | 0 |
| `Spectra.OneParameterUnitaryGroup.Product` | 9 | 0 |
| `Spectra.SpectralTheory.Calculus.SpectralGapInverse` | 7 | 0 |
| `Sylvester.PairwiseSpectrumGap` | 7 | 0 |
| `Sylvester.PairwiseHomogeneousUniqueness` | 11 | 0 |
| `Sylvester.HomogeneousUniqueness` | 2 | 0 |

### A universe restriction you should sign off on

`Ideals/PaperHilbertSchmidtBasis.lean` had `variable {E : Type u} {F : Type v}`.
That is now `variable {E F : Type v}`.

This is a correction, not a weakening. `paperHilbertSchmidtEnergy`,
`IsPaperHilbertSchmidt`, `paperHilbertSchmidtNorm` and
`SameApproximationSingularSequence` are all declared over a **single** universe
`{E F : Type v}`, so with `E` and `F` in different universes not one theorem in
that file could be stated at all. The apparent extra generality was never
well-typed. Roughly eleven of its twenty six errors were that one mismatch.

If you want the generality for real, the fix is to universe-polymorphise
`Ideals/PaperHilbertSchmidt.lean` first; it was deliberately not attempted here.
This is the same defect class as the earlier heterogeneous singular-sequence
statements.

## Still open

**Nothing in this chain.** `SinTheta.PaperTheorem62` is closed: both
`PaperTheorem62Data.result` and `PaperRealTheorem62Data.result` build and print
exactly `[propext, Classical.choice, Quot.sound]`.

Its last defect is worth recording, because it is a trap this repository has
now hit twice: the identity operator's norm is one only on a *nontrivial*
space, and the spaces here may be trivial, so any step rewriting it to one
fails to elaborate and every calc step below it fails in turn. Bound it by the
lemma that carries no instance requirement instead.

Everything below it is likewise closed: `Ideals.PaperHilbertSchmidtBasis`, the four
tensor modules, `Sylvester.PaperHilbertSchmidtDefectFirst`,
`Sylvester.PaperHilbertSchmidtPairwise`, `Sylvester.PairwiseSpectrumGap`,
`Sylvester.PairwiseHomogeneousUniqueness` and `Sylvester.HomogeneousUniqueness`
all build with no errors and are free of admissions.

**No genuine mathematical gap was found anywhere in this drop.** Every one of
roughly a hundred and twenty errors repaired was Lean mechanics. Two candidates
that looked like real gaps were not: the arithmetic failures in homogeneous
uniqueness were a norm that never reduced together with a nonlinear product,
and the difference quotient decomposition that a ring tactic rejected was true
as stated and failed only because the unbundled tensor operator map has no
linearity lemmas in a restricted simp set.

## Lean mechanics that cost the most time this round

Every one of roughly seventy errors was mechanics, not mathematics. The
recurring ones, in descending cost:

1. **The lambda character cannot appear in an identifier**, not even inside a
   longer name such as `hλ`. It lexes as an identifier followed by the start of
   a function abstraction, which then consumes following lines. In
   `PairwiseSpectrumGap` the resulting parse error fell inside the body of the
   central definition, so that definition did not exist, which is what blocked
   the modules above it. Use `lam`.

2. **A `notation` body substitutes its parameter into every occurrence of that
   identifier, including the label of a named argument.** The vendored pure
   tensor notation was written as `HilbertTensor.tmul (𝕜 := 𝕜) x y`, so
   `x ⊗̂ₜ[ℂ] y` expanded to `tmul (ℂ := ℂ) x y`. It had been broken since it was
   written and worked only because every prior call site passed a scalar
   literally named `𝕜`. Pin the scalar with a type ascription instead.

3. **`Submodule.span_induction` binds the two membership proofs before the two
   induction hypotheses.** Write `| add x y _ _ hx hy =>` and `| smul c x _ hx =>`.
   Naming only two binders captures the memberships and leaves the hypotheses
   inaccessible, and every branch then reports an unrelated failure. This cost
   time four separate times.

4. **A heartbeat timeout here is usually a disguised type error**, not slowness.
   Both timeouts in the tensor package were an operator on the base space handed
   to a slot expecting an operator on the conjugate space. Check argument types
   before raising limits.

5. **A rewrite is undone by a following `simp` when the rewriting lemma is
   itself a `simp` lemma.** `rw [← Conj.toConj_ofConj cv]` followed by `simp`
   is a no-op. Substitute, or state the lemma in the shape `simp` normalizes to.

6. **A modifier such as `open X in` must precede a declaration's docstring**,
   not sit between the docstring and the declaration. Same rule as `omit ... in`.

7. **A qualified name may not be split across a line break after its dot.**

8. **Namespace drift after the POVM split**: `bornMeasure` is under
   `BornRule.PVM`, `bornMeasure_support_subset_spectrum` under
   `BornRule.Observable`, `borelMeasure` under `Spectra.Borel`, and `generator`
   under `Spectra.OneParameterUnitaryGroup`.

9. **Two toolchains are live in this checkout.** The root pins `v4.32.0`, but
   `vendor/Spectra` is also opened as its own project under `v4.31.0-rc1`, and
   both write `vendor/Spectra/.lake/build`. Build from the repository root.

## How to measure a build

**Do not run two `lake build` processes against the same build tree.** Doing so
produces spurious errors: a serial rebuild of two files that reported forty
three errors under concurrency reported zero. Any count taken while another
build is running is worthless. This is the same hazard as judging a module by a
stale `.olean`, and it wasted real time this round.
