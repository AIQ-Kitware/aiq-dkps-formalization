# Proof obligations

## Completed citation-facing theorem

### Exact Theorem 4

`FinishYuWangSamworth.Rectangular.Theorem4` now packages:

* the exact right-singular sine bound;
* the identical left-singular sine bound;
* right and left aligned-frame conclusions with the paper's `2^(3/2)` factor;
* both intrinsic operator-norm and literal top-singular-value (`sigma_1`) forms.

The implementation is factored through one generic Gram-transport theorem, so
right and left versions share the same proof and constant bookkeeping.

## P0: remaining citation-facing completion

### Rank-one singular-vector corollaries

Expose direct right and left unit-vector statements with phase/sign alignment.
These should be derived from the exact aligned-frame theorem at `d = 1`, not
reproved through a separate perturbation argument.

### Source-index wrappers

Add optional wrappers taking an explicit contiguous index block `r..s` and
constructing the corresponding Gram eigenblocks and squared-singular-value gap.
The current exact theorem uses the more intrinsic and safer
`CorrespondingRightSingularBlock` / `CorrespondingLeftSingularBlock` predicates.

## P1: source fidelity and reusable infrastructure

* Package Appendix Lemma 5 in a recognizable compression API if the current
  intrinsic Frobenius lemmas are not directly discoverable.
* Record the sharper residual numerator stated after Theorem 2.
* Formalize equation (4) if useful to the independent `FinishTanTwoTheta` lane.

## P2: non-citation-critical completeness

* Formalize the two sharpness examples.
* Audit the Section 3 application claims as prose or executable examples.
