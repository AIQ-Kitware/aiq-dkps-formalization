# Section 3 elementary bridge and Lemma 6.3 mathematics-ahead pass

Prepared against repository archive `9e2557409aa7`, after applying the
Sylvester semigroup mathematics overlay.

This overlay does not touch the Sylvester, ideal-family, graph-subspace, or
continuation files from the preceding overlay.  It advances two independent
fronts that were still missing.

## Main semantic correction

The frontier version of Lemma 6.3 used

```text
K * P = Q * K
```

which immediately implies the off block `Q*K*(1-P)` is zero.  That is not the
Davis--Kahan hypothesis.  The corrected source condition is

```text
K * P = Q * K * P.
```

The completed theorem in this overlay uses the corrected condition.

## Added files

- `DavisKahan/Experimental/MathAhead/Section3Elementary.lean`
  - concrete generic Halmos cosine and sine restrictions;
  - generic Pythagorean identity;
  - identification of the crossed intersections;
  - positivity of both diagonal compressions of the acute direct rotation;
  - skew-adjointness of the crossed blocks;
  - packaging of the canonical acute rotation as a paper direct rotation;
  - Corollary 3.2 reversal.

- `DavisKahan/Experimental/MathAhead/Lemma63.lean`
  - corrected source statement;
  - approximation-square-energy monotonicity under left compression;
  - finite-rank conversion to paper Hilbert--Schmidt energy;
  - orthogonal-domain energy splitting;
  - complete scalar conclusion.

- `DavisKahan/Experimental/MathAhead/All.lean`
- `dev/davis-kahan-mathahead-candidates.json`: frontier-node redirect map.

## Compile order

```bash
lake env lean DavisKahan/Experimental/MathAhead/Section3Elementary.lean
lake env lean DavisKahan/Experimental/MathAhead/Lemma63.lean
lake env lean DavisKahan/Experimental/MathAhead/All.lean
```

After they compile, redirect these frontier nodes:

```text
s3-generic-cosine-restriction
s3-generic-sine-restriction
s3-generic-pythagoras
s3-crossed-identification
s3-cor3-2
s6-approximation-energy
s6-lemma6-3-approx
```

The canonical direct-rotation packaging is additional infrastructure for
Proposition 3.1.

## Lemma ledger: high confidence

- `halmosCosineSq`, `halmosSineSq`
- `halmosCosineSq_add_sineSq`
- `projection_mem_halmosGenericPart_left`
- `projection_mem_halmosGenericPart_right`
- `spectraDirectRotation`
- `spectraDirectRotation_mem_unitary`
- `spectraDirectRotation_intertwines`
- `spectraDirectRotation_reversal`
- `spectraDirectRotation_add_star_eq_two_smul_absoluteValue`
- `projection_mul_spectraDirectRotation_mul_projection`
- `complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection`
- `spectraCanonicalAbsoluteValue_commute_projection`
- `spectraOperatorAbsoluteValue_nonneg`
- `ContinuousLinearMap.nonneg_iff_isPositive`
- `ContinuousLinearMap.approximationNumber_comp_left_le`
- `ContinuousLinearMap.approximationNumber_zero`
- `paperHilbertSchmidtEnergy_eq_sum_range_of_rank_le`
- `paperHilbertSchmidtEnergy_eq_basisEnergy`
- `isPaperHilbertSchmidt_of_rank_le`
- `approximationSingularValue_nonneg`
- `approximationSingularValue_le_opNorm`

## Lemma ledger: likely spelling or API repair

- `ContinuousLinearMap.codRestrict` on a composed map into a submodule
- `star_projection`
- `star_complementaryProjection`
- `Commute.sub_left`
- `LinearMap.rank_comp_le_left`
- `LinearMap.rank_comp_le_right`
- `HilbertBasis.orthogonalSumSubmodule`
- `HilbertBasis.orthogonalSumSubmodule_inl_mem`
- `HilbertBasis.orthogonalSumSubmodule_inr_mem`
- `Equiv.tsum_sum`
- rank bookkeeping for `A = K*P`; the displayed proof is mathematically
  unnecessary because `rank(A) <= rank(P)`, but the exact cardinal lemma name
  needs repair.

## Confidence

- generic Halmos restrictions: complete mathematics, local API repair likely.
- generic Pythagoras: complete.
- crossed-intersection identification: complete.
- acute direct-rotation paper blocks: complete mathematics, star/rewrite names
  likely need repair.
- Corollary 3.2: complete wrapper around an existing theorem.
- Lemma 6.3: complete mathematical proof.
- Lemma 6.3 finite-rank bookkeeping: likely compiler repair around rank and the
  orthogonal-sum Hilbert basis constructor.

## Remaining Section 3 front

This overlay does not claim the following are finished:

- nonacute direct-rotation construction and parameterization;
- operator-level classification of two projection pairs;
- spectral-multiplicity classification;
- compact angle-list classification;
- maximal fixed-angle reducing subspaces;
- principal-square-root converse.

Those remain the next independent mathematics batch.
