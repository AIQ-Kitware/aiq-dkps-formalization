# Grounding ledger

This package is checked by
`dev/policy/yu-wang-samworth-grounding.yaml` and is part of the default
build.  The source census is the current paper-coverage authority:
`dev/yu-wang-samworth-2015-full-source-census.json`.

The package builds only on repository-local, machine-checked results.

The lists below name the paper-facing results.  The YAML policy is the
authority; when the two disagree, the YAML is right.

## Symmetric results

* `YuWangSamworth2015.Symmetric.Theorem1`
  * `yuWangSamworth_theorem1_uiNorm_le`, `..._frobenius_le`, `..._opNorm_le`
* `YuWangSamworth2015.Symmetric.Theorem2`
  * `theorem2_sinTheta`, `theorem2_alignedFrame`
  * `yuWangSamworth_sinTheta_block_le`, `yuWangSamworth_alignedFrame_block_le`,
    `yuWangSamworth_alignedFrame_block_real_le`
* `YuWangSamworth2015.Symmetric.Corollary1`
  * `corollary1_sinTheta`, `corollary1_alignedVector`
  * `corollary1_printed_unnormalized_counterexample`
* `YuWangSamworth2015.Symmetric.AngleIdentity`
  * `yuWangSamworth_equation4`, `yuWangSamworth_equation4_printed_counterexample`
* `ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`
  * `sinTheta_perturbation_le`
  * `opNorm_sinThetaMap_le_of_intervalGap`

The `Core.Statistics` forms `yuWangSamworth_sinTheta_le`,
`yuWangSamworth_alignedBasis_le` and `yuWangSamworth_eigenvector_le` are
superseded.  They carry `CorrespondingEigenblock`, which pins both blocks to
Mathlib's chosen eigenbases and is narrower than the printed hypothesis.  They
remain in the policy as supporting declarations, not as the paper-facing surface.

## Rectangular results

* `YuWangSamworth2015.Rectangular.SourceTheorem3`
  * `theorem3_rightSinTheta`, `theorem3_leftSinTheta`
  * `theorem3_rightAlignedFrame`, `theorem3_leftAlignedFrame`
  * `IsRightSingularBlock`, `IsLeftSingularBlock`, `SourceSingularGap`
* `YuWangSamworth2015.Rectangular.RankBoundary`
  * `yuWangSamworth_theorem3_printed_rankBoundary_refutation`
* `YuWangSamworth2015.Rectangular.SingularBlock`
* `YuWangSamworth2015.Rectangular.FrobeniusGram`
* `YuWangSamworth2015.Rectangular.Theorem4`
* `YuWangSamworth2015.Core.SingularSubspace`

## Appendix compression

* `DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidt`
  * `paperHilbertSchmidtNorm_comp_le`
* `DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFrobenius`
  * finite-dimensional Frobenius realization

The grounding audit rejects proof placeholders or ungrounded external results in
the package closure.  Run it rather than relying on a dated audit statement:

```bash
aiq-lean source grounding dev/policy/yu-wang-samworth-grounding.yaml
```

## Source audit: equation (4)

The printed equation (4) in arXiv:1405.0680 omits a square on the factor
`2 - ‖v̂ - v‖²`.  Direct substitution of
`‖v̂ - v‖² = 2 - 2⟪v̂,v⟫` shows that the correct identity contains
`(2 - ‖v̂ - v‖²)²`.  The formal theorem records this corrected identity, and
`yuWangSamworth_equation4_printed_counterexample` machine-checks a concrete
failure of the printed polynomial formula.
