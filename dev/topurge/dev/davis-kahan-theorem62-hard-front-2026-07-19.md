# Davis--Kahan Theorem 6.2 hard-front rebase

Date: 2026-07-19
Base commit: `b56455cdef29f6b0ba55e44a6a235432e67e9999`

This note records the hard-front mathematics rebased onto the compiler-accepted
paper-norm witness and correspondence work.

## Verified work inherited from the base

The paper-literal norm layer is now demonstrably nonempty and machine-checked.
In particular:

- the normalized `ell1` symmetric gauge constructs the paper nuclear norm;
- definiteness is derived from normalization and zero-padding rather than
  postulated on the source seminorm structure;
- the singular values of a real diagonal operator are identified with the
  decreasing rearrangement of the absolute diagonal entries;
- both round trips in `PaperNormCorrespondence` are proved propositionally;
- the scoped repairs in `PaperRankOneNormalization.lean` and
  `PaperUnitaryInvariantNormDefinite.lean` are retained unchanged.

Do not replace those files with any earlier mathematics-ahead version.

## Immediate compiler blocker inherited from the base

`Spectra/Spaces/Tensor/HilbertSchmidt.lean` is the first unresolved module in
the square-norm route.  The Lean-enabled pass reported roughly nine errors,
including a nonexistent `norm_noninc`, an unelaborated `rightTensor_add`, and
stuck typeclass inference.

This rebase includes static repairs for the most direct defects:

- factor the easy inequality into `Conj.norm_map_le`, then apply it twice;
- make the hidden ambient type explicit in `rightTensor_add` and
  `rightTensor_smul`;
- replace the nonexistent continuous-linear-map congruence helper with
  evaluation by `congrArg`;
- prove the operator-norm contraction directly rather than by an invalid
  `simpa` from `le_opNorm`;
- remove two ill-typed uses of tensor/operator injectivity where the goal was
  already an operator equality;
- replace the nonexistent finite-rank sum lemma with an explicit range-in-span
  rank estimate.

These repairs have not been compiled in this environment.  The first task for
the Lean-enabled agent is still to compile this module and report the exact
remaining diagnostics before changing downstream mathematics.

## 1. Bounded homogeneous uniqueness at arbitrary disjoint spectra

Let `A` and `B` be self-adjoint operators on complex Hilbert spaces `E` and
`F`, and let `X : F -> E` be bounded. Assume

- `X(dom B) subset dom A`, and
- `A X x = X B x` for every `x in dom B`.

No interval ordering is assumed. Suppose only that `sigma(A)` and `sigma(B)`
are disjoint.

### Generator intertwining implies group intertwining

Write `U_A(t) = exp(i t A)` and `U_B(t) = exp(i t B)`. On `dom B`, fix `t`
and consider

`g(s) = U_A(t-s) X U_B(s) x`.

The domain invariance of `U_B`, the domain transport by `X`, and the generator
identity imply that both derivative terms exist and cancel. Hence `g'(s)=0`,
so `g(0)=g(t)` and

`U_A(t) X x = X U_B(t) x`.

The generator domain is dense and both sides are bounded in `x`, so this
identity holds on all of `F`.

### Group intertwining implies spectral-calculus intertwining

For `xi in E` and `eta in F`, group intertwining gives equality of the
polarized spectral forms at every character:

`<xi, U_A(t) X eta> = <X* xi, U_B(t) eta>`.

Four-vector polarization expresses each complex spectral form as a fixed
linear combination of finite positive scalar measures. Fourier uniqueness
therefore promotes character equality to equality for every bounded Borel
symbol `f`:

`f(A) X = X f(B)`.

In particular, for every Borel set `S`,

`E_A(S) X = X E_B(S)`.

### Project onto one spectrum

Take `S = sigma(A)`. The scalar spectral measures of `A` are supported inside
`sigma(A)`, hence `E_A(S)=I`. Since `S` is disjoint from `sigma(B)`, every
scalar spectral measure of `B` gives `S` zero mass, hence `E_B(S)=0`.
Therefore `X=0`.

This proves bounded homogeneous uniqueness under arbitrary disjoint spectra.
Positive pairwise separation then gives uniqueness of bounded solutions of the
same closed Sylvester equation.

### Lean leaves

- `Spectra.YosidaHille.RectangularIntertwining`
- `Spectra.SpectralTheory.SeparatedIntertwiner`
- `ExactSinTheta.PairwiseHomogeneousUniqueness`

## 2. Global tensor spectral gap from pairwise spectral separation

Let `U` and `V` be the Stone groups of `A` and `B`. On

`HS(F,E) = E tensor conjugate(F)`,

the Sylvester flow is

`W(t) = U(t) tensor conjugate(V(t))`.

For a pure tensor `z = u tensor conjugate(v)`, its characteristic function is

`<z,W(t)z> = <u,U(t)u> <v,V(-t)v>`.

If `mu_u` and `nu_v` are the scalar spectral measures of `U` and `V`, this is
the Fourier transform of the pushforward of `mu_u x nu_v` by

`(lambda,alpha) |-> lambda-alpha`.

Fourier uniqueness gives the exact measure identity. Pairwise separation of
the two scalar supports therefore places the pure-tensor measure outside the
gap. The gap spectral projection kills every pure tensor, hence vanishes on the
whole tensor completion by density and continuity.

This route avoids the broken mixed-state joint-Born import closure and proves a
global tensor spectral gap, stronger than the defect-local statement needed by
Theorem 6.2.

### Lean leaves

- `Spectra.HilbertSchmidtTensor.HilbertSchmidtSpectralGap`
- `ExactSinTheta.PaperHilbertSchmidtPairwise`

## 3. Defect-first conclusion

Let `C` be Hilbert--Schmidt and let `c` be its tensor. The global tensor gap
permits the bounded reciprocal spectral multiplier. Applying it to `c` gives
`z0` with

- `z0` in the tensor-generator domain;
- generator value `c`;
- `delta * ||z0|| <= ||c||`.

Mapping `z0` back to an operator gives a Hilbert--Schmidt solution `X0` of the
closed Sylvester equation. Arbitrary-spectrum homogeneous uniqueness identifies
the supplied bounded solution `X` with `X0`. This is the non-circular,
constant-one pairwise-gap estimate required by Davis--Kahan Theorem 6.2.

## 4. Compiler-review order

1. `Spectra.Spaces.Tensor.HilbertSchmidt`
2. `DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtBasis`
3. `Spectra.YosidaHille.RectangularIntertwining`
4. `Spectra.SpectralTheory.SeparatedIntertwiner`
5. `ExactSinTheta.PairwiseSpectrumGap`
6. `ExactSinTheta.PairwiseHomogeneousUniqueness`
7. `Spectra.HilbertSchmidtTensor.HilbertSchmidtSpectralGap`
8. `ExactSinTheta.PaperHilbertSchmidtPairwise`
9. `ExactSinTheta.PaperTheorem62`
10. `DavisKahan.Sources.DavisKahan1970.FullSineTheta`
11. both exact-paper audit modules

## 5. Standing repair cautions

- A failed first tactic prevents the rest of that declaration from being
  elaborated. Read every line after the first failure before describing a proof
  as mostly repaired.
- A reduction or heartbeat timeout can be an unsatisfiable type unification,
  especially when a theorem was stated homogeneously but used between different
  Hilbert spaces.
- `congrArg (fun x => x)` transports nothing and cannot turn pointwise singular
  value equality into equality of their sums.
- Do not infer real coverage from a complex-only min--max bridge.
- Do not recreate the paper norm witness or its correspondence. They are green
  on this base.
- If the tensor/operator map needs a mathematical change rather than an API
  repair, preserve the pure-tensor rank-one identity and the exact tensor norm
  equality; those are the load-bearing invariants.
