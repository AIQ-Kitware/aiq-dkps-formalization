# Uniqueness of the multiplicity decomposition: the attack plan

Written 2026-08-06, immediately after Theorem 3.1 landed.  **Read this before starting; it
records what is reachable, what is not, and one prerequisite defect that was fixed first.**

## Status, 2026-08-06 (later the same day)

**Both halves are done.  Uniqueness is closed.**
`TauCeti.BorelCalculus.operatorUnitaryEquiv_iff_measureEquiv_and_level`
(`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityLevelUniqueness.lean`):
two data present unitarily equivalent operators **iff** their bases are in the same measure
class and every level set agrees up to a null set.  Axiom-clean, default build.  Read the
Half 1 and Half 2 sections for the module lists and for the estimates in this document that
turned out to be wrong -- Half 2's central prediction among them.

## What is open, precisely

`SameSpectralMultiplicity` is an **existential over presentations**.  Both directions of
`sameSpectralMultiplicity_iff_unitarilyEquivalent` are proved, so it is a complete invariant in
the sense of the biconditional -- which is what the paper's sentence asserts.  What is missing is
that the datum of an operator is *unique*, i.e. the converse of
`operatorUnitaryEquiv_of_measureEquiv`:

```text
OperatorUnitaryEquiv D.operator E.operator
  →  MeasureEquiv D.base E.base  ∧  ∀ k, D.base (D.level k ∆ E.level k) = 0.
```

The measure half of that implication is now proved (`measureEquiv_base_of_operatorUnitaryEquiv`); the level-set half is not.  Until it lands, `SpectralMultiplicityFoundation` stays uninhabited: its `multiplicity` field is
a *function*, which needs uniqueness as well as existence, plus a canonical `Datum`, which is
`Cardinal → Quotient measureClassSetoid`.  `measureClassSetoid` already exists, so that half is a
strict extension rather than a rewrite.

## Prerequisite, already fixed: the datum was degenerate

Uniqueness was not merely unproved; **as stated it would have been false**.  Nothing forced
`base` to vanish off `level 0`, and mass out there contributes to no summand of
`MultiplicityDatum.measure`, so two data differing only outside `level 0` present the *same*
operator with different measure classes.  The field `base_supported_level_zero` closes that, and
`exists_hasMultiplicityModel` supplies it (`subset_levelSet_zero`).  Do not remove it.

## The two halves, and their difficulty

### Half 1: the measure class is determined.  **DONE, 2026-08-06.**

`TauCeti.BorelCalculus.measureEquiv_base_of_operatorUnitaryEquiv` in
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityUniqueness.lean`:

```text
OperatorUnitaryEquiv D.operator E.operator  →  MeasureEquiv D.base E.base
```

axiom-clean, in the default build.  The modules that carry it, in dependency order:

1. `ForTauCeti/MeasureTheory/MulLpAlgebra.lean` -- `mulLp` is a `⋆`-algebra map in its symbol,
   and every multiplication operator is normal.
2. `ForTauCeti/MeasureTheory/MulLpSpectrum.lean` -- the essential range of the symbol lies in the
   spectrum.  **This was the load-bearing step and the plan did not anticipate it**: without it
   `f ∘ g` cannot be written down at all for `f : C(spectrum ℂ (mulLp ρ g), ℂ)`, since `f` is
   defined on the spectrum and `g` takes values in `ℂ`.  σ-finiteness is used here, to find a set
   of positive *finite* measure carrying the indicator that contradicts the lower bound off the
   spectrum.
3. `ForTauCeti/MeasureTheory/MulLpCfc.lean` -- step 2(A), `cfc f (mulLp ρ g) = mulLp ρ (f ∘ g)`,
   by uniqueness of the continuous functional calculus.  The empty-spectrum case is split off
   rather than excluded: a complex Banach algebra with an empty-spectrum element is a
   subsingleton.
4. `ForTauCeti/MeasureTheory/LpNonvanishing.lean` -- step 2(B), a nowhere-vanishing `L²` function
   on a σ-finite space.
5. `.../BorelCalculus/DiagMeasureMulLp.lean` -- step 2(C), `map val (diagMeasure F) = g_* (|F|²·ρ)`
   and the two absolute-continuity halves that follow from it, hence a maximal vector.
6. `.../BorelCalculus/MultiplicityUniqueness.lean` -- step 3.

**Estimates that were wrong, recorded so they are not re-walked.**

* Step 1 predicted a Stone--Weierstrass argument.  It was not needed:
  `LinearIsometryEquiv.conjStarAlgEquiv` and `StarAlgHomClass.map_cfc` supply the whole
  transport, and the only real side condition is continuity of the conjugation.
* Step 2(A) was estimated at 200--400 lines "where the remaining work of Half 1 sits".  The cfc
  uniqueness argument itself was routine; the unanticipated corestriction of the symbol to the
  spectrum (item 2 above) was the real cost.
* Step 3 needed no positivity on the far side, as the plan already noted, and that is what makes
  it short: each direction uses a maximal vector on its own side and the cheap domination on the
  other.  `absolutelyContinuous_base_of_intertwines` is stated once and run twice.

The one step that is **not** formal is the passage from `Prod.fst _* D.measure` to `D.base`:
that is `measureEquiv_map_fst_measure`, and it holds only because of the datum field
`base_supported_level_zero`.  Without it the theorem is false.  Do not remove that field.

### Half 2: the level sets are determined.  **DONE, 2026-08-06.**

The invariant that landed is `SpectralGeneratedLE ha hS m` -- the range of the spectral
projection of a Borel `S ⊆ ℂ` lies in the closed Borel-calculus span of `m` vectors -- a
Boolean-at-each-`m` version of the "minimal number of generators" this plan proposed.  If
`base (level k \ level' k) > 0`, taking `S` to be that set gives `¬ GeneratedLE k` on the `D`
model and `GeneratedLE k` on the `E` model, and transport along the unitary is the
contradiction.  The modules, in dependency order:

1. `ForTauCeti/MeasureTheory/MatrixKernelSelection.lean` -- measurable selection of a unit
   kernel vector for a measurable family of `m × n` matrices, `m < n`, via the resolvent limit
   `t (B + t)⁻¹ → proj ker B` with `B = AᴴA`: each approximant is a det--adjugate rational
   function of the entries, and the eigendecomposition is used only pointwise.
2. `ForTauCeti/MeasureTheory/LpSliceSum.lean` (additions) -- `lintegral`/Bochner/a.e.
   decompositions over `sliceSum`, both directions.
3. `.../BorelCalculus/BorelNatural.lean` -- Borel-calculus naturality, `specProjC`, cyclic
   transport, `SpectralGeneratedLE` and its unitary invariance.
4. `.../BorelCalculus/MulLpBorel.lean` -- `h(mulLp g) = mulLp (h ∘ g)` for bounded Borel `h`;
   spectral projections of the model are indicator multiplications.
5. `.../BorelCalculus/MultiplicityLevelUniqueness.lean` -- the two bounds, the level-set
   theorem, and the combined biconditional.

**Estimates that were wrong, recorded so they are not re-walked.**

* "The Borel case needs a monotone-class argument on top of it."  It does not.  The Borel
  calculus is *defined* by the polarised diagonal integrals, and Half 1's
  `map_val_diagMeasure_eq_of_intertwines` transports those directly; naturality is four
  integral rewrites.  The only genuine care is types: symbols on the two spectra are pulled
  back from `ℂ`, and extension-by-zero (`exists_comp_val_eq`) shows that loses nothing.
* "This is a dimension count over the measure algebra and is where the real work is."  Half
  right.  The real work was doing the count **measurably**: given `k` claimed generators, the
  defect direction in `ℂ^{k+1}` must be chosen measurably in the spectral parameter with the
  rank of the section matrix jumping arbitrarily, and no formula built from a fixed set of
  minors survives that.  The resolvent-limit selection is where the effort went; the count
  itself (`k < k + 1`) is then pointwise linear algebra.
* The upper bound was expected to need a density argument ("closure of `{h·1_A}` is
  `L²(A)`").  It needs only duality: a vector orthogonal to the slice-indicator orbits has
  slice sections annihilated by every bounded test function, hence vanishing a.e. -- the test
  functions are truncations of the section itself.

## What may now be claimed

The census may record: a complete invariant **canonically** -- measure class and level sets
are both determined by the operator (`operatorUnitaryEquiv_iff_measureEquiv_and_level`).
`SpectralMultiplicityFoundation` is still uninhabited, but the obstruction is gone; what
remains for it is bookkeeping (a canonical `Datum` as a quotient by `measureClassSetoid` and a
function-valued multiplicity field), not mathematics, and it is beyond the paper's sentence.
