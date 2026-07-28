# Grounding ledger

## Paper theorem -> Lean foundation

| Paper surface | Declaration or module | Status |
|---|---|---|
| Theorem 2, Frobenius sine bound with population-only gap and `min` numerator | `TauCeti.DavisKahanTheory.yuWangSamworth_sinTheta_le` | proved |
| Theorem 2, interval-block wrapper | `TauCeti.DavisKahanTheory.yuWangSamworth_intervalBlock_le` | proved |
| Theorem 2, aligned-basis conclusion | `TauCeti.DavisKahanTheory.yuWangSamworth_alignedBasis_le` | proved |
| Corollary 3, rank-one eigenvector conclusion | `TauCeti.DavisKahanTheory.yuWangSamworth_eigenvector_le` | proved |
| Appendix residual sandwich | `DavisKahan/Sources/YuWangSamworth2015.lean` | proved |
| Gram perturbation identities and base operator-norm bounds | `DavisKahan/Specialized/SingularSubspace.lean` | proved |
| Right/left Frobenius and paper-coefficient Gram bounds | `FinishYuWangSamworth.Rectangular.FrobeniusGram` | proved |
| Exact right Theorem 4 sine bound | `yuWangSamworth_rightSingularSubspace_le` | proved in lane; awaiting compiler verification |
| Exact left Theorem 4 sine bound | `yuWangSamworth_leftSingularSubspace_le` | proved in lane; awaiting compiler verification |
| Right aligned-frame conclusion | `yuWangSamworth_rightSingularAlignedBasis_le` | proved in lane; awaiting compiler verification |
| Left aligned-frame conclusion | `yuWangSamworth_leftSingularAlignedBasis_le` | proved in lane; awaiting compiler verification |
| Rank-one right/left singular-vector corollaries | future `Rectangular.RankOne` module | open |
