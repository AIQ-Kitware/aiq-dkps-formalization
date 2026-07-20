# Handoff: source norm witness and defect-first Theorem 6.2 infrastructure

Date: 2026-07-19
Base commit: `d307141e5233d06c8e4aad27b0689b95a9d83aff`

## Read this first

The compiler-repair agent should continue its existing queue.  This drop is a
separate mathematics-ahead layer for the two independent gaps it identified:

1. the paper-exact unitarily invariant norm class had no concrete inhabitant;
2. the rectangular Hilbert--Schmidt/tensor construction required by Theorem
   6.2 did not exist.

No Lean toolchain was available while preparing this drop.  None of the new
modules is claimed to compile until the compiler agent accepts it.

Do not replace the compiler-accepted direct-sum weak-majorization proof.  In
particular, do not symmetrize finite-rank approximants: the rank may double.
The lower approximation-number estimate needs the two independent witness
subspaces and the rank-safe direct-sum argument already accepted by Lean.

## Result 1: the paper norm class is now concretely inhabited

`Ideals/PaperUnitaryInvariantNormInstances.lean` constructs the normalized
finite `l1` symmetric gauge and transports it through the existing
paper-norm/symmetric-gauge correspondence.  The resulting
`paperNuclearNorm : PaperUnitaryInvariantNorm` has finite prefix gauge equal to
the Ky Fan prefix sum.

The key audit declaration is:

```lean
paperUnitaryInvariantNorm_nonempty : Nonempty PaperUnitaryInvariantNorm
```

This closes the non-vacuity objection.  It does not depend on the incomplete
old rectangular ideal instances.

Recommended first compile:

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormInstances
```

Likely repairs are finite-sum API and exact field names in
`PaperSymmetricNormingFunction`; the mathematics is elementary.

## Result 2: canonical rectangular Hilbert--Schmidt model

`Spectra/Spaces/Tensor/HilbertSchmidt.lean` uses

```text
HS(F,E) = E tensor Conj(F)
```

and defines the coordinate-free map

```text
J(z)(x) = (u |-> u tensor conjugate(x))* z.
```

For pure tensors it proves

```text
J(u tensor conjugate(v)) = rankOne u v.
```

The file also supplies injectivity, left/right composition laws, basis column
expansions, tensor reconstruction from square-summable columns, and exact
column-energy identities.

`Ideals/PaperHilbertSchmidtBasis.lean` then identifies this model with the
repository's existing square norm, which is defined through the complete
approximation-number sequence.  The intended endpoint is:

```lean
IsPaperHilbertSchmidt A ↔
  ∃! z : HilbertSchmidtTensor.Space E F,
    HilbertSchmidtTensor.toOperator z = A
```

with exact equality between the tensor norm and
`paperHilbertSchmidtNorm A`.

The proof is basis-independent and does not assume compactness.  Finite square
energy implies compactness only after the equality has been established.

Recommended compile order:

```bash
lake build Spectra.Spaces.Tensor.HilbertSchmidt
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtBasis
```

## Important correction: Theorem 6.2 must be defect-first

The older `Sylvester/PaperHilbertSchmidt.lean` selected a tensor representing
the supplied bounded solution `X` before proving that `X` was
Hilbert--Schmidt.  That construction assumes the desired conclusion and is
not usable.

The corrected route begins with the known Hilbert--Schmidt defect `C`:

1. tensorize `C` to `c`;
2. apply the reciprocal spectral multiplier to `c`;
3. obtain a tensor `z0` with generator value `c` and the sharp norm bound;
4. map `z0` back to a bounded Hilbert--Schmidt operator `X0`;
5. prove `X0` satisfies the original closed Sylvester equation;
6. identify the supplied bounded solution `X` with `X0` by bounded
   homogeneous uniqueness.

This reduction is implemented in
`Sylvester/PaperHilbertSchmidtDefectFirst.lean`.  Its public theorem takes the
two exact facts that remain to be derived from pairwise spectrum separation:

- a vector spectral gap for the defect tensor;
- bounded homogeneous uniqueness.

It does not replace either by a stronger gap assumption.

## Supporting infrastructure

### Lightweight joint spectral measure imports

The old joint-PVM import closure pulled in mixed-state/KMS files unrelated to
Theorem 6.2.  The following split isolates the basic POVM and projective
machinery:

- `BornRule/POVMCore.lean`;
- `BornRule/Joint/ProjectivePVM.lean`;
- `ProjValMeasure/GeneralMap.lean`.

`Joint/Defs.lean` now imports the core layer.  `POVM.lean` re-exports the core
and retains the higher mixed-state material.  `joint_product_form` is public
because the projective pushforward proof uses it.

### Tensor Sylvester flow

`Spaces/Tensor/HilbertSchmidtFlow.lean` defines

```text
W(t) = U_A(t) tensor conjugate(U_B(t))
```

and proves that `J(W(t)z) = U_A(t) J(z) U_B(-t)`.

### Generator graph direction

`Spaces/Tensor/HilbertSchmidtGeneratorBridge.lean` proves the direction needed
by the defect-first inverse:

```text
z in dom(generator W), generator W z = c
  -> J(z) maps dom B into dom A
  -> A J(z) - J(z) B = J(c).
```

The converse graph theorem remains useful but is not required for the
constructed inverse.

### Vector-local reciprocal calculus

`SpectralTheory/Calculus/SpectralGapInverse.lean` supplies the bounded cutoff
symbol

```text
g_delta(s) = if delta <= |s| then 1/s else 0
```

and proves directly that its calculus vector lies in the group-generator
domain, is sent back to the defect vector on gap-supported spectral measure,
and has norm at most `delta⁻¹` times the defect norm.

### Existing three-gap homogeneous uniqueness

`Sylvester/HomogeneousUniqueness.lean` derives bounded uniqueness from the
already accepted operator-norm theorem for the three supported source gap
configurations.  This is reusable but is deliberately not used as a fake
replacement for arbitrary pairwise separation.

## The exact remaining mathematics for Theorem 6.2

Two obligations remain.  They are independent of the compile-repair queue and
must not be hidden behind stronger assumptions.

### A. Spectral support of the defect tensor

From

```text
delta <= |lambda - alpha|
for lambda in spectrum A and alpha in spectrum B,
```

prove that the scalar spectral measure of `c` for the tensor flow `W` is
supported in `{s | delta <= |s|}`.

Recommended route:

1. split `W` into commuting left and conjugate-right tensor groups;
2. package their self-adjoint generators and joint PVM;
3. identify the PVM of `W` with pushforward by addition;
4. identify the right tensor spectral coordinate with `-alpha` for
   `alpha in spectrum B`;
5. use marginal support to obtain support on
   `{(lambda,-alpha)}`;
6. push forward to `lambda-alpha`.

The new `ProjectivePVM`, `GeneralMap`, and group-product modules are intended
for this proof.

### B. Bounded homogeneous uniqueness under arbitrary pairwise separation

For bounded `Y`, prove

```text
A Y - Y B = 0  ->  Y = 0
```

under disjoint self-adjoint spectra, without first assuming ideal membership.

Recommended route:

1. use the closed equation to prove generator intertwining;
2. differentiate `U_A(-t) Y U_B(t)x` on `dom B` and show it is constant;
3. extend by density to `U_A(t)Y = YU_B(t)`;
4. generalize the existing Fourier-determinacy argument to rectangular
   intertwiners and obtain
   `E_A(S)Y = YE_B(S)` for every measurable `S`;
5. take `S = spectrum A`; the `A` projection is identity and the `B`
   projection is zero because the spectra are disjoint;
6. conclude `Y = 0`.

This proof should become reusable Spectra infrastructure.  A whnf/heartbeat
timeout in the rectangular calculus step should first be treated as a possible
hidden type mismatch, not as a performance problem.

## Compiler lessons to preserve

- Lean stops elaborating a tactic block after the first failure.  A low error
  count does not imply the later proof exists.
- Verify every identifier before using it.  The previous Lemma 6.1 draft
  referenced several nonexistent declarations.
- A homogeneous helper cannot be applied to operators over different spaces;
  the resulting failure may surface as a heartbeat timeout.
- `congrArg (fun x => x)` proves nothing beyond its input equality and cannot
  convert pointwise singular-value equalities into finite-gauge equalities.
- Do not propagate a rewrite orientation mechanically.  Two projection
  decompositions needed the original orientation after an earlier correction
  had been over-applied.
- A theorem whose min--max bridge is complex-only must not claim a real scalar
  scope in its documentation.
- Local instances do not propagate to importers.
- Nested namespace shadows can make a real imported declaration appear
  missing.

## Verification sequence after repair

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormInstances
lake build Spectra.Spaces.Tensor.HilbertSchmidt
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtBasis
lake build Spectra.Spaces.Tensor.HilbertSchmidtFlow
lake build Spectra.Spaces.Tensor.HilbertSchmidtGeneratorBridge
lake build Spectra.SpectralTheory.Calculus.SpectralGapInverse
lake build DavisKahan.Experimental.InfiniteDimensional.Sylvester.HomogeneousUniqueness
lake build DavisKahan.Experimental.InfiniteDimensional.Sylvester.PaperHilbertSchmidtDefectFirst
lake env lean DavisKahan/Experimental/InfiniteDimensional/Sylvester/PaperHilbertSchmidtMathAheadAudit.lean
```

Only after the two pairwise obligations above are proved should
`PaperHilbertSchmidt.lean` be rewritten to use the defect-first theorem and the
source Theorem 6.2 audit be considered closed.
