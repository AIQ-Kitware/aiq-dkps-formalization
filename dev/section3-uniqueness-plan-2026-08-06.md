# Uniqueness of the multiplicity decomposition: the attack plan

Written 2026-08-06, immediately after Theorem 3.1 landed.  **Read this before starting; it
records what is reachable, what is not, and one prerequisite defect that was fixed first.**

## Status, 2026-08-06 (end of day)

**Half 1 is done.**  The measure class of a multiplicity datum is a unitary invariant.  Half 2 --
the level sets -- is untouched and is the real Hahn--Hellinger.  Read the Half 1 section for the
module list and for three estimates in this document that turned out to be wrong.

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

### Half 2: the level sets are determined.  **Hard, and it is the real Hahn--Hellinger.**

The invariant to use is the **minimal number of generators**: for a Borel `S`, let `mult_D S` be
the least cardinal `κ` such that the calculus-invariant subspace `E_D(S) H` is generated by `κ`
vectors.  A unitary intertwiner preserves it, and on the model it computes to the essential
supremum of the multiplicity function over `S`.  Then if
`base (level k \ level' k) > 0`, taking `S` to be that set gives `mult_D S ≥ k + 1` and
`mult_E S ≤ k`.

Two genuinely new pieces are needed, and neither is small:

* **The unitary intertwines the spectral projections**, i.e. naturality of the *Borel* calculus,
  not just the continuous one.  Half 1 step 1 gives the continuous case; the Borel case needs a
  monotone-class argument on top of it.
* **Computing `mult_D S` on the model**: that `⊕_{j<k+1} L²(μ)` needs exactly `k + 1`
  generators.  This is a dimension count over the measure algebra and is where the real work is.

## What must not be claimed meanwhile

The census records the honest position and must keep doing so: a complete invariant in the sense
of the biconditional, **not** a canonical one; `SpectralMultiplicityFoundation` uninhabited;
uniqueness an explicitly recorded open obligation.
