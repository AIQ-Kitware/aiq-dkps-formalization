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
* formalize the two sharpness examples;
* add optional wrappers whose hypotheses are literal contiguous matrix indices
  `r..s` rather than intrinsic corresponding-block predicates;
* migrate reusable results from this completion lane into canonical modules.

These are no longer blockers for coverage of the paper's numbered theorems.

## This library is not a default build target

`lakefile.toml` does not list `FinishYuWangSamworth` in `defaultTargets`, so a
green `lake build` does **not** compile anything here. The generated census
(`dev/yu-wang-samworth-2015-full-source-census.json`) quantifies what that
costs. **Re-measured 2026-07-30 (lane CLAIM-DOC): the census now carries 22
items, of which 12 resolve to declarations in `defaultTargets` libraries, 7
resolve only into `Finish*`, and 3 could not be located by name at all.** The
earlier figure in this document, 19 items with 10 guarded, is superseded.

The three unlocatable items are worth a look on their own: a census entry whose
declarations cannot be found by name is either renamed or gone, and neither is
visible to any gate.

Coverage and protection against regression are different properties. This
document asserts the first; the second is not yet true. Build explicitly with
`lake build FinishYuWangSamworth`.
