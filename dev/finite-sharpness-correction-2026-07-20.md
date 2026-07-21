# Finite sharpness correction: singular-value multiplicity

The historical planar `sin 2Θ` equality compared two operators with different
singular-value multiplicities:

- `sinTwoAngleOperator U V = 2 P_{Uᗮ} P_V P_U` is one-sided and has one nonzero
  singular value on each nontrivial principal plane;
- the symmetric off-diagonal perturbation has two equal nonzero singular values
  on each such plane.

Consequently their operator norms match after the sharp factor-two scaling, but
an arbitrary unitarily invariant norm need not match. The Frobenius and nuclear
norms already distinguish the two sequences. The corrected endpoint is
`sinTwoTheta_model_operatorNorm_equality` on `0 ≤ θ ≤ π/4`.

The former `directSum_models_simultaneous_equality` declaration was removed
rather than weakened into a theorem that no longer expressed simultaneous
symmetric-gauge sharpness. A future all-UI direct-sum theorem must use a
rank-matched one-sided residual model.

This batch also supplies reusable planar singular-value lemmas, including the
square-is-scalar argument for symmetric `2 × 2` blocks and the one-sided
rank-one block calculation.
