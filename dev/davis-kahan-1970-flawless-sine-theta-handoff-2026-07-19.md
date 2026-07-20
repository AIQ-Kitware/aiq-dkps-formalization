# Handoff: literal completion of the Davis--Kahan 1970 sine-theta section

Date: 2026-07-19
Authoritative base: `d9eeaa37c205b37177c03f456f44b7355bf0925f`

## Goals

Immediate: finish today with no definitional, hypothesis, conclusion, norm,
angle, domain, sharpness, or source-surface difference from the sine-theta
material in Davis--Kahan 1970.

Ultimate: formalize the full paper.  New infrastructure should therefore be
reusable for tangent-theta, double-angle, direct rotation, and spectral
repulsion, but those topics must not distract from closing the sine-theta audit.

## Protected accepted base

The base repository's complex and real general sine-theta routes, natural
spectral-subspace forms, bounded specializations, source roots, and existing
audit were compiler-accepted before this overlay.  Do not rewrite them.  The
exact-paper layer is imported only by
`DavisKahan.Sources.DavisKahan1970.FullSineTheta`.

## What this overlay adds

1. A coherent source norm whose ideal membership is canonically determined by
   its finite symmetric gauges, not an arbitrary predicate.
2. A proposed equivalence with coherent symmetric norming functions.
3. Literal cosine-defined directed angles and functional-calculus sines.
4. Heterogeneous singular-sequence representatives, matching the paper's
   freedom to choose coordinate spaces.
5. Literal full angles and projector-difference singular-data bridges.
6. Lemmas 6.1 and 6.2 with their sharp block/reflection proofs.
7. Universal-norm original sine and Theorem 6.1 wrappers over the accepted
   finite-Ky-Fan theorem.
8. Exact common-domain appendix packaging.
9. Proposition 6.1.
10. Theorem 6.2's Hilbert--Schmidt route and finite-rank bound-norm fallback.
11. Planar equality, finite-multiplicity sharpness, and the printed
    one-direction counterexample.
12. A literal source facade and dedicated trusted-dependency audit.

## Mathematical corrections already made

- The source angle is `arccos` of the positive cosine block.  The ambient
  `arcsin` construction is only an equivalent representative.
- Symmetrizing a rank-`n` approximation with conjugation can double rank and
  cannot establish reverse approximation inequalities.  The rank-safe min--max
  route is retained.
- An arbitrary ideal-membership predicate plus unitary invariance does not
  model every source norm.  Membership is derived from the canonical prefix
  supremum.
- Lemma 6.1 is a direct-sum weak-majorization theorem, not a triangle estimate.
- Lemma 6.2 is a reflection-pinch contraction and loses no factor.
- Theorem 6.2's subscript-one fallback is the operator norm, not the trace norm.
- The paper's arbitrary `sin Theta_0` representative may act on different
  coordinate spaces.  The paper-facing theorem uses a heterogeneous complete
  singular-sequence relation.

## Compile order

Run each command to a zero-error result before proceeding.  The first six
leaves isolate the foundational API risks.

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperSingularValueTransport
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNorm
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormLaws
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormDefinite
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperNormCorrespondence
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHeterogeneousRepresentative
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.OperatorModulusApproximation
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationBlockSum
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCosineAngle
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCosineAngleReal
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperFullAngle
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperFullAngleReal
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperProjectionBlocks
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperLemma61
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperTheorem61Universal
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperSymmetric
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidt
lake build DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtFiniteRank
lake build DavisKahan.Experimental.InfiniteDimensional.Sylvester.PaperHilbertSchmidt
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperTheorem62
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCommonDomainTheorems
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperSharpness
lake build DavisKahan.Sources.DavisKahan1970.FullSineTheta
lake env lean DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullPaperSineThetaAudit.lean
```

## Highest-risk declarations

### 1. Hilbert--Schmidt tensor model

`exists_paperHilbertSchmidtSylvesterSpectralModel` currently names the exact
missing infrastructure under `Spectra.HilbertSchmidtTensor`.  Those declarations
are not in the current vendored API.  Implement them in a dedicated module
rather than weakening Theorem 6.2 or replacing its constant-one statement with
a contour bound.

Required mathematics:

- completion of finite-rank rectangular operators in the square norm;
- isometry with `E tensor conjugate(F)`;
- left/right closed self-adjoint multiplication operators;
- strong commutation;
- joint PVM and scalar measure;
- multiplier identity for the closed Sylvester equation;
- support on the product of the two spectra.

### 2. Source norm correspondence

`PaperSymmetricNormingFunction.paperNormEquiv` uses best-guess finite-dimensional
UIN APIs.  Do not solve errors by adding a majorization law as independent
mathematical data unless it is proved equivalent to the ordinary symmetric
norm axioms.  The goal is literal universality, not a conveniently smaller
class.

### 3. Literal angle functional calculus

Likely repairs concern exact `cfc_comp`, `cfc_mul`, positivity, and subtype
instances.  Preserve the source definition `Theta_0 = arccos |C_0|`.  Do not
revert to naming the cross block itself as the angle sine.

### 4. Heterogeneous representative transport

The pure relation belongs below the norm layer.  Norm and square-norm transport
live in higher modules to avoid an import cycle.  Keep this separation.

### 5. Full-angle coordinate equivalences

Expect coercion and orientation repairs involving orthogonal decomposition
isometries and double orthogonal complements.  The target theorem is exact
singular-sequence equality with `P-Q`.

### 6. Sharpness matrices

The matrix computations are intended as genuine theorem-use tests, not
ornamental examples.  Preserve conclusions that mention the residual and sine
operators explicitly.

## Acceptance protocol

1. Rebuild `DavisKahan.Sources.DavisKahan1970.FullSineTheta` successfully.
2. Compile `FullPaperSineThetaAudit.lean` directly.
3. Every printed dependency list must be exactly
   `[propext, Classical.choice, Quot.sound]`.
4. Re-verify the previously accepted `FullPartIII` and `FullUnboundedAudit`.
5. Search the entire new dependency cone for proof bypasses.
6. Confirm no source alias points to the older ideal-family-only or
   block-only compatibility theorem when a literal paper theorem exists.
7. Compare the public statement line by line with the correspondence matrix.

Do not claim the sine-theta section is source-faithful until all seven checks
pass.
