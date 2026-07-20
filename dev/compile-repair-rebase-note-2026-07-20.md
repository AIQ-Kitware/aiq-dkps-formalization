# Rebase note for the mathematics agent, 2026-07-20

Base your next drop on `88e32a8` or later.

This round was compiler repair only. **No theorem statement was weakened, no
hypothesis was added, no declaration was removed, and nothing was left
incomplete.** The two exceptions to "nothing changed but proofs" are recorded
explicitly below, under *Universe restriction* and *One signature argument*.

---

## 1. Both of your open obligations are closed

### Arbitrary-spectrum homogeneous uniqueness

```
Spectra.QuantumMechanics.SpectralTheory.generatorIntertwiner_eq_zero_of_disjoint_spectrum
Spectra.QuantumMechanics.SpectralTheory.spectralProjection_spectrum_eq_id
Spectra.YosidaHille.GeneratorIntertwines.group
ForMathlib…ExactSinTheta.closedSylvester_homogeneous_eq_zero_complex
ForMathlib…ExactSinTheta.closedSylvester_homogeneous_eq_zero_real
```

All print exactly `[propext, Classical.choice, Quot.sound]`.

Your argument was mathematically correct throughout. It failed because
`GeneratorIntertwines.group` cited the density of the generator domain without
importing the module that proves it — so the theorem the entire rectangular
chain rests on **did not exist**. Three one-line fixes. Do not redesign it.

### Pairwise tensor spectral support

```
Spectra.HilbertSchmidtTensor.borelMeasure_sylvesterGroup_tmul
Spectra.HilbertSchmidtTensor.hasVectorSpectralGap_tmul
Spectra.HilbertSchmidtTensor.spectralProjection_gap_eq_zero
Spectra.HilbertSchmidtTensor.hasVectorSpectralGap
```

All axiom-clean. Again the mathematics was sound; the failures were namespace
and notation scoping, a dense induction applied rather than eliminated, an
integrand written in the source variable instead of the mapped one, and a
higher-order product factorisation needing its factors named. Nothing about the
argument was redesigned.

---

## 2. Theorem 6.2 is closed

```
ForMathlib…ExactSinTheta.PaperTheorem62Data.result      → [propext, Classical.choice, Quot.sound]
ForMathlib…ExactSinTheta.PaperRealTheorem62Data.result  → [propext, Classical.choice, Quot.sound]
```

Both the complex and the real endpoint.

---

## 3. Modules that went from red to green

| Module | Was | Now |
| --- | --- | --- |
| `Spectra.Spaces.Tensor.Hilbert` | latent notation bug | fixed |
| `Spectra.Spaces.Tensor.HilbertSchmidt` | 39 | 0 |
| `Spectra.Spaces.Tensor.HilbertSchmidtFlow` | 13 | 0 |
| `Spectra.Spaces.Tensor.HilbertSchmidtGeneratorBridge` | 13 | 0 |
| `Spectra.Spaces.Tensor.HilbertSchmidtSpectralGap` | 13 | 0 |
| `Spectra.YosidaHille.RectangularIntertwining` | 5 | 0 |
| `Spectra.SpectralTheory.SeparatedIntertwiner` | 5 | 0 |
| `Spectra.OneParameterUnitaryGroup.Product` | 9 | 0 |
| `Spectra.SpectralTheory.Calculus.SpectralGapInverse` | 7 | 0 |
| `Ideals.PaperHilbertSchmidtBasis` | 26 | 0 |
| `Sylvester.PairwiseSpectrumGap` | 7 | 0 |
| `Sylvester.PairwiseHomogeneousUniqueness` | 11 | 0 |
| `Sylvester.HomogeneousUniqueness` | 2 | 0 |
| `Sylvester.PaperHilbertSchmidtDefectFirst` | 6 | 0 |
| `Sylvester.PaperHilbertSchmidtPairwise` | 8 | 0 |
| `SinTheta.PaperTheorem62` | 17 | 0 |

`scripts/check_repaired_modules.sh` now covers 37 modules and passes serially.
The source-facing gate `scripts/check_full_unbounded_sin_theta.py` re-runs
CLEAN with zero `sorryAx`.

**Nothing in this chain is open.**

---

## 4. No genuine mathematical gap was found

Roughly a hundred and twenty errors were repaired. **Every one was Lean
mechanics.** Three separate things looked like real mathematical gaps and were
not — worth stating because each cost time to disprove:

- The arithmetic failures in homogeneous uniqueness: a norm that never reduced,
  together with a product that is not linear.
- A difference-quotient decomposition that a ring tactic rejected with the false
  residual `-(I⁻¹·t⁻¹) = 0`. **The identity is true as stated.** It failed
  because the unbundled tensor operator map has no linearity lemmas in a
  restricted `simp only` set, so the quotient never split.
- The Theorem 6.2 cascade, which traced to `‖id‖ = 1` requiring a *nontrivial*
  space.

---

## 5. Two changes that are not merely proofs

### Universe restriction — please sign off

`Ideals/PaperHilbertSchmidtBasis.lean` had `variable {E : Type u} {F : Type v}`;
it is now `variable {E F : Type v}`.

This is a **correction, not a weakening**. `paperHilbertSchmidtEnergy`,
`IsPaperHilbertSchmidt`, `paperHilbertSchmidtNorm` and
`SameApproximationSingularSequence` are all declared over a single universe, so
with `E` and `F` in different universes not one theorem in that file could be
*stated*. The apparent generality was never well-typed; eleven of its twenty-six
errors were that one mismatch.

To have the generality for real, universe-polymorphise
`Ideals/PaperHilbertSchmidt.lean` first. Deliberately not attempted here. Same
defect class as the earlier heterogeneous singular-sequence statements.

### One signature argument

`ofOperator_toOperator`'s summability argument now reads
`summable_column_norm_sq b z`. `ofOperator` discards that argument
definitionally, so the theorem asserts exactly what it did before.

---

## 6. New API you may cite

The column expansion rested on five lemmas that **do not exist in Mathlib under
any name**. It was rebuilt on `OrthogonalFamily`, with a Bessel estimate proved
from the Pythagoras identity and Cauchy–Schwarz. Now available:

- `norm_sum_columnTensor_sq`, `sum_column_norm_sq_le`, `summable_column_norm_sq`
- `toOperator_tmul'` — pure tensor with the second factor left in `Conj F`
- `Conj.ofConj_adjoint_map`
- `toOperator_add`, `toOperator_sub`, `toOperator_smul`, `toOperator_zero`,
  `toOperator_sum` — **`toOperator` is unbundled**, so `map_add` and friends do
  not reach it

---

## 7. Lean mechanics that cost the most time

In descending cost:

1. **The lambda character cannot appear in an identifier**, not even inside a
   longer name such as `hλ`. It lexes as an identifier followed by the start of
   a function abstraction, which then consumes the following lines. Twice the
   resulting parse error fell *inside a definition body*, so that definition did
   not exist and every module above it was blocked. Use `lam`.

2. **A qualified name may not be split across a line break after its dot.**
   Eighteen occurrences across four files.

3. **`Submodule.span_induction` binds the two membership proofs before the two
   induction hypotheses.** Write `| add x y _ _ hx hy =>` and
   `| smul c x _ hx =>`. Naming only two binders captures the memberships and
   leaves the hypotheses inaccessible; every branch then reports an unrelated
   failure. Cost time six separate times.

4. **`Dense.induction` is `elab_as_elim`.** Supply the motive `(P := …)` and use
   `refine … ?_ ?_ point`, never `apply`. The point goes in the *last* slot.
   There is no `Dense.induction_on`.

5. **A heartbeat timeout here is usually a disguised type error**, not slowness.
   Confirmed six times. Check argument types before raising limits.

6. **`‖id‖ = 1` requires a nontrivial space.** `ContinuousLinearMap.norm_id`
   carries an instance requirement that does not hold when the space may be
   trivial. Use `ContinuousLinearMap.norm_id_le`, which carries none.

7. **A `notation` body substitutes its parameter into every occurrence of that
   identifier, including the label of a named argument.** The vendored pure
   tensor notation read `HilbertTensor.tmul (𝕜 := 𝕜) x y`, so `x ⊗̂ₜ[ℂ] y`
   expanded to `tmul (ℂ := ℂ) x y`. Broken since written; it worked only because
   every prior call site passed a scalar literally named `𝕜`.

8. **A rewrite is undone by a following `simp`** when the rewriting lemma is
   itself a `simp` lemma. `rw [← Conj.toConj_ofConj cv]` then `simp` is a no-op.

9. **A restricted `simp only` cannot see `@[simp]` lemmas** you are relying on —
   list them explicitly.

10. **A modifier such as `open X in` must precede a declaration's docstring**,
    not sit between the docstring and the declaration. Same rule as `omit … in`.

11. **Namespace drift after the POVM split**: `bornMeasure` under
    `BornRule.PVM`; `bornMeasure_support_subset_spectrum` under
    `BornRule.Observable`; `borelMeasure` under `Spectra.Borel`;
    `borelMeasure_fourier` under `Spectra.Borel.SpectralMeasure`; `generator`
    under `Spectra.OneParameterUnitaryGroup`; `RealComplexification.complexify`
    under `Foundation`.

12. **`gcongr` goal count and ordering are not what you expect.** Prefer the
    explicit monotonicity lemmas, which are order-deterministic.

---

## 8. How to measure a build — read this before reporting any count

**Never run two `lake build` processes against the same build tree.** Doing so
produces entirely spurious errors. This round, two files that reported forty
three errors under concurrency reported **zero** when rebuilt serially, and one
run reported sixteen thousand bogus Mathlib errors from file-descriptor
exhaustion. A count taken while another build is running is worthless.

Two toolchains are live in this checkout: the root pins `v4.32.0`, but
`vendor/Spectra` is also opened as its own project under `v4.31.0-rc1`, and both
write `vendor/Spectra/.lake/build`. **Build from the repository root.**

This is the same class of hazard as judging a module by a stale `.olean`, and it
cost real time twice.
