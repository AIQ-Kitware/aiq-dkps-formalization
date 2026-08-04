# Proof obligations

## Numbered paper results

All numbered mathematical statements now have a theorem surface:

* Theorem 1;
* Theorem 2;
* Corollary 3;
* Theorem 4, right and left;
* Lemma 5.

## Additional completed source material

* corrected equation (4), with the source typo documented;
* direct right and left rank-one singular-vector corollaries;
* exact operator/Frobenius minimum and aligned-frame constants.

## Elegance audit status

The in-place audit consolidated the Frobenius ideal foundation, added bundled
orthonormal-column/row Lemma 5 wrappers, removed manual dimension witnesses
from the literal `sigma_1` API, and added a machine-checked counterexample to
the printed equation (4).

## Remaining non-numbered source-fidelity work

* package the smaller residual numerator mentioned after Theorem 2;
* add optional wrappers whose hypotheses are literal contiguous matrix indices
  `r..s` rather than intrinsic corresponding-block predicates;
* migrate reusable results from this completion lane into canonical modules.

These are no longer blockers for coverage of the paper's numbered theorems.

## Build guard

`FinishYuWangSamworth` **is** a default build target: it joined `defaultTargets`
on 2026-08-02, so `lake build` compiles everything here and a regression cannot
land unnoticed.  The library also carries `warningAsError` under the Mathlib
standard linter set, matching the option set Tau Ceti's own `lean_lib` applies.

The earlier text in this slot said the opposite — that nothing here was
compiled by `lake build` and that the census quantified what that cost.  That
was true when written and is not now.  The nine rows it described as
`proved_outside_build` are all `proved_in_build`, and the census's
`unguarded-completion-lane` gap has been removed along with its nine
references.

## Census state (2026-08-04)

`dev/yu-wang-samworth-2015-full-source-census.json`: **21 of 22 rows proved in
the default build; the 22nd is an exposition row that is not proof debt.  There
is no unformalized proof debt left for this paper.**

Both Section 2 sharpness examples landed 2026-08-04
(`Symmetric/OrthogonalSharpness.lean`, `Symmetric/PlanarSharpness.lean`), so the
census now certifies not only that the paper's bounds hold but that its
constants and dimension dependence are unimprovable — which is half of what
makes the paper useful and was previously unrepresented.

Two rows named declarations that do not exist: an unrecorded
`PopulationGap` → `InternalGap` rename left `TauCeti.PopulationGap`,
`...RightSingularPopulationGap` and `...LeftSingularPopulationGap` in the
census.  The renderer's resolution check had been failing on the first of
these, which is why the rendered `.md` was stale.  All three are corrected.
