# Grounding ledger

**Audit status, 2026-07-30 (lane CLAIM-DOC):**
`python3 FinishYuWangSamworth/scripts/verify_grounding.py` → `FinishYuWangSamworth
grounding audit: OK`, exit 0, run against the current tree. The script is now in
`dev/README.md`'s gate list; until this lane, nothing ran it, so the ledger below
was a claim with no live evidence. Its sibling in `FinishTanTwoTheta` was failing
on four stale references at the same moment — the two libraries were not in the
same state, which is why the row asked for both to be run rather than assumed.


The completion lane builds only on repository-local, machine-checked results.

## Symmetric results

* `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics`
  * `yuWangSamworth_sinTheta_le`
  * `yuWangSamworth_alignedBasis_le`
  * `yuWangSamworth_eigenvector_le`
* `ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`
  * `sinTheta_perturbation_le`
  * `opNorm_sinThetaMap_le_of_intervalGap`

## Rectangular results

* `FinishYuWangSamworth.Rectangular.FrobeniusGram`
* `FinishYuWangSamworth.Rectangular.Theorem4`
* `ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.SingularSubspace`

## Appendix compression

* `DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidt`
  * `paperHilbertSchmidtNorm_comp_le`
* `DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFrobenius`
  * finite-dimensional Frobenius realization

No theorem in this lane uses `sorry`, `axiom`, or an ungrounded external result.

## Source audit: equation (4)

The printed equation (4) in arXiv:1405.0680 omits a square on the factor
`2 - ‖v̂ - v‖²`.  Direct substitution of
`‖v̂ - v‖² = 2 - 2⟪v̂,v⟫` shows that the correct identity contains
`(2 - ‖v̂ - v‖²)²`.  The formal theorem records this corrected identity, and
`yuWangSamworth_equation4_printed_counterexample` machine-checks a concrete
failure of the printed polynomial formula.
