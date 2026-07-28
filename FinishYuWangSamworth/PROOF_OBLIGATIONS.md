# Proof obligations

## P0: citation-facing completion

### 1. Exact right-singular Theorem 4

Construct a source-shaped corresponding-block predicate for ordered right
singular subspaces, viewed as spectral blocks of `A.adjoint ∘ A`. Apply the
already proved population-gap theorem to the two right Gram operators.

The missing quantitative bridge must provide both branches:

* operator branch from `opNorm_rightGram_sub_le` followed by
  `||Ahat|| <= ||A|| + ||Ahat - A||`;
* Frobenius branch
  `||Ahat^* Ahat - A^* A||_F <=
    (||Ahat||_op + ||A||_op) ||Ahat - A||_F`.

Then simplify to the paper's directly usable coefficient
`2 * sigma_1(A) + ||Ahat - A||_op`.

### 2. Exact left-singular Theorem 4

Repeat the construction for `A ∘ A.adjoint`. Prefer an adjoint transfer theorem
when it genuinely shortens the proof and preserves the source constant.

### 3. Aligned singular frames

Use the existing aligned-basis/Procrustes theorem to derive the paper's
`2^(3/2)` right and left frame bounds from the completed sine bounds.

### 4. Rank-one singular-vector corollaries

Expose direct right and left unit-vector statements, with phase/sign alignment,
so forward citations do not need to reconstruct the `d = 1` specialization.

## P1: source fidelity and reusable infrastructure

* Package Appendix Lemma 5 in a recognizable compression API if the current
  intrinsic Frobenius lemmas are not directly discoverable.
* Record the sharper residual numerator stated after Theorem 2.
* Formalize equation (4) if useful to the independent `FinishTanTwoTheta` lane.

## P2: non-citation-critical completeness

* Formalize the two sharpness examples.
* Audit the Section 3 application claims as prose or executable examples.
