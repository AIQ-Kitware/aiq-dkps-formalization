# Grounding ledger

## Paper theorem -> existing Lean foundation

| Paper surface | Existing declaration or module | Status entering lane |
|---|---|---|
| Theorem 2, Frobenius sine bound with population-only gap and `min` numerator | `TauCeti.DavisKahanTheory.yuWangSamworth_sinTheta_le` | proved |
| Theorem 2, interval-block wrapper | `TauCeti.DavisKahanTheory.yuWangSamworth_intervalBlock_le` | proved |
| Theorem 2, aligned-basis conclusion | `TauCeti.DavisKahanTheory.yuWangSamworth_alignedBasis_le` | proved |
| Corollary 3, rank-one eigenvector conclusion | `TauCeti.DavisKahanTheory.yuWangSamworth_eigenvector_le` | proved |
| Appendix residual sandwich | `DavisKahan/Sources/YuWangSamworth2015.lean` | proved |
| Gram perturbation identities and operator-norm bounds | `DavisKahan/Specialized/SingularSubspace.lean` | proved |
| Right/left Frobenius Gram perturbation and paper-coefficient bounds | `FinishYuWangSamworth.Rectangular.FrobeniusGram` | proved in lane; awaiting compiler verification |
| Right/left singular-subspace operator-norm endpoints | `rightSingularSubspace_sinTheta_le`, `leftSingularSubspace_sinTheta_le` | proved, not exact Theorem 4 |
| Squared operator-branch singular-vector overlap bound | `sq_gap_mul_sum_cross_singularVectors_le` | proved, partial Theorem 4 |
| Exact right Theorem 4 with source `min` numerator | `FinishYuWangSamworth.Rectangular` | open |
| Exact left Theorem 4 | `FinishYuWangSamworth.Rectangular` | open |
| Right/left aligned singular-frame conclusions | `FinishYuWangSamworth.Rectangular` | open |
| Rank-one right/left singular-vector corollaries | `FinishYuWangSamworth.Rectangular` | open |
