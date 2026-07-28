# Grounding ledger

The completion lane builds only on repository-local, machine-checked results.

## Symmetric results

* `DavisKahan.Specialized.Statistics`
  * `yuWangSamworth_sinTheta_le`
  * `yuWangSamworth_alignedBasis_le`
  * `yuWangSamworth_eigenvector_le`
* `DavisKahan.FiniteDimensional.SinTheta.Perturbation`
  * `sinTheta_perturbation_le`
  * `opNorm_sinThetaMap_le_of_intervalGap`

## Rectangular results

* `FinishYuWangSamworth.Rectangular.FrobeniusGram`
* `FinishYuWangSamworth.Rectangular.Theorem4`
* `DavisKahan.Specialized.SingularSubspace`

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
