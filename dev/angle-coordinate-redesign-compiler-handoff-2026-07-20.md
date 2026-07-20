# Compiler handoff: source-coordinate angle embedding redesign

Date: 2026-07-20 America/New_York

## Exact base

This batch is rebased on the compiler agent archive at Git HEAD:

`90ef32fcc534de8204d7e71d793810f4142561c4`

The base working tree was clean. The rectangular Schatten, finite lp gauge,
weak-majorization, and compatibility modules from commits `a8d4ea3` and
`90ef32f` were already present. None of those compiler-clean files were
reapplied or edited in this batch.

## Mathematical defect repaired

For an isometric trial map `X : F -> E`, set

* `C = P_U X : F -> E`,
* `S = P_{U-perp} X : F -> E`.

The previous provisional formulas used ambient rectangular pseudoinverses and
postcomposition by `X`. Types did not reject them, but the angle semantics were
wrong:

* `C^+ X` introduces an additional projection/readback factor;
* `2 S C^* X = 2 S C^* C` has singular values
  `2 sin(theta) cos(theta)^2`, not `sin(2 theta)`;
* the double-angle cosine belongs first on the source coordinates as
  `C^* C - S^* S`.

The canonical replacement uses the positive source cosine

`Q = |C| = (C^* C)^(1/2) : F -> F`.

The corrected coordinate maps are:

* tangent: `S Q^+`;
* double-angle sine: `2 S Q`;
* source double-angle cosine: `C^* C - S^* S`;
* rectangular double-angle cosine: `X (C^* C - S^* S)`;
* double-angle tangent: `(2 S Q) (C^* C - S^* S)^+`.

On a simultaneous principal-angle basis these act by `tan(theta)`,
`sin(2 theta)`, `cos(2 theta)`, and `tan(2 theta)`, respectively.

## Files changed

### DavisKahan/FiniteDimensional/Residual/AngleEmbedding.lean

Added canonical source-coordinate infrastructure:

* `cosThetaGram`;
* `sinThetaGram`;
* `cosThetaMagnitude`;
* `cosThetaGram_add_sinThetaGram_eq_id`;
* `cosThetaMagnitude_sq`;
* `ker_cosThetaMagnitude`;
* `cosThetaMagnitude_injective`;
* `singularValues_cosThetaMagnitude_eq_embedding`;
* `cosTwoThetaSourceOperator`;
* `cosTwoThetaSourceOperator_isSymmetric`;
* `cosTwoThetaSourceOperator_eq_two_smul_sub_id`;
* corrected `cosTwoThetaEmbedding`;
* kernel, singular-value, and injectivity bridges for the corrected rectangular
  double-angle cosine;
* `singularValues_cosThetaEmbedding`;
* `singularValues_cosThetaMagnitude`.

The corrected `cosTwoThetaEmbedding` preserves its historical rectangular
signature `F -> E`; it now embeds the correct source operator on the left by
`X`, rather than constructing an ambient block and composing on the right.

### DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean

Replaced all three provisional bodies:

* `tanThetaEmbedding = S Q^+`;
* `sinTwoThetaEmbedding = 2 S Q`;
* `tanTwoThetaEmbedding = sinTwoThetaEmbedding (cosTwoThetaSourceOperator)^+`.

Added:

* `tanThetaEmbedding_eq_inverseOnRange`;
* `tanThetaEmbedding_eq_inverseOnRange_of_isTransverse`;
* `tanTwoThetaEmbedding_eq_inverseOnRange`.

These use the compiler-accepted bridges
`FiniteDimensional.moorePenroseInverse_eq_inverseOnRange` and
`FiniteDimensional.inverseOnRange`.

### DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean

Repointed the historical candidate proof from the nonexistent namespace name
`FiniteDimensional.cosTwoThetaEmbedding` to the source denominator
`cosTwoThetaSourceOperator`. Replaced the fictional
`moorePenroseInverse_eq_inverse_of_injective` rewrite with the new canonical
`tanTwoThetaEmbedding_eq_inverseOnRange` theorem.

This file still contains other historical candidate dependencies that may be
unimplemented. Do not infer that the whole module is repaired merely from this
local correction.

## Suggested sequential compiler pass

Run these first, sequentially:

```text
lake env lean DavisKahan/FiniteDimensional/Residual/AngleEmbedding.lean
lake env lean DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean
lake env lean DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean
```

Likely elaboration seams:

1. The proof of `cosThetaGram_add_sinThetaGram_eq_id` may need minor rewriting
   around `inner_starProjection_left_eq_right` or `X.inner_map_map`.
2. `singularValues_cosThetaMagnitude_eq_embedding` may need explicit unfolding
   of `cosThetaMagnitude` and `trialGramSqrt` when constructing the positivity
   witness.
3. The two inverse-on-range compatibility proofs may need `simpa` rather than
   `rw` because proof arguments occur in dependent definitions; proof
   irrelevance should close the discrepancy.
4. `cosTwoThetaEmbedding_injective_iff` may need a direct constructor if the
   two `ker_eq_bot` rewrites choose an inconvenient direction.
5. The third module is expected to expose unrelated fictional historical APIs.
   Repair only genuine local consequences of the source-coordinate redesign;
   do not weaken its theorem statement and do not invent replacement APIs.

After local repair, run the standard checks sequentially:

```text
python3 scripts/check_full_part_iii_math_ahead.py --static-only
python3 scripts/check_full_part_iii_math_ahead.py
python3 scripts/generate_all_aggregates.py --check
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/inventory_davis_kahan_debt.py --json
python3 scripts/check_library_structure.py
```

The structural checker had 116 pre-existing check-3 violations at the base
commit. This batch does not relocate modules and should not change that count.

## Deliberately not claimed

This batch does not claim the singular-value identifications

* `singularValues(tanThetaEmbedding) = tan(principalAngles)`;
* `singularValues(sinTwoThetaEmbedding) = |sin(2 principalAngles)|`;
* `singularValues(tanTwoThetaEmbedding) = |tan(2 principalAngles)|`.

Those require a simultaneous CS decomposition or an equivalent spectral
calculus proving that the sine block, cosine Gram square root, and source
cosine share the required principal directions. The definitions are now
mathematically correct inputs to that theorem, but the theorem itself should
be proved separately.

No changes were made to
`DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean`.
