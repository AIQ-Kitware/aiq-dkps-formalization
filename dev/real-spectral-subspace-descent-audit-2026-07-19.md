# Real spectral-subspace descent: mathematical audit

Date: 2026-07-19

## Purpose

This note audits the real natural-input route independently of Lean elaboration.
The route starts with a densely defined real self-adjoint operator, passes to
its coordinatewise complexification, obtains the canonical complex spectral
measure, descends each conjugation-invariant spectral projection, and restricts
the original real operator to the descended range.

The conclusions below distinguish mathematically valid claims from proof routes
that look plausible but lose a rank bound or silently assume a domain identity.

## 1. Restriction to a reducing subspace

Let `A` be a densely defined self-adjoint operator on a real or complex Hilbert
space `H`. Let `U` be a closed subspace with orthogonal projection `P`, and put
`Q = I - P`. Assume:

1. `P (dom A) subset dom A` and `Q (dom A) subset dom A`;
2. `A(dom A intersect U) subset U`;
3. `A(dom A intersect U-perp) subset U-perp`.

Define `A_U` on `U` with domain `dom A intersect U` and action inherited from
`A`.

### Density

For `u in U`, choose `x_n in dom A` with `x_n -> u`. Then `P x_n` lies in
`dom A intersect U` and converges to `u`. Thus the restricted domain is dense
in `U`.

### Closedness

If `u_n -> u` in `U` and `A_U u_n -> v` in `U`, the same convergences hold in
`H`. Closedness of `A` gives `u in dom A` and `Au = v`. Hence `u` lies in the
restricted domain and the restricted graph is closed.

### Adjoint domain

Suppose `y in U` belongs to `dom(A_U*)`, represented by `z in U`:

`<A x, y> = <x, z>` for every `x in dom A intersect U`.

For arbitrary `x in dom A`, write `x = Px + Qx`. Both summands are in the
operator domain. Since `A(Qx) in U-perp` and `y,z in U`,

`<A(Qx), y> = 0 = <Qx, z>`.

The adjoint relation therefore extends from `Px` to every `x in dom A`:

`<Ax,y> = <x,z>`.

Self-adjointness of `A` gives `y in dom A` and `Ay=z`. Because `y in U`, this
is exactly `y in dom A_U` and `A_U y=z`. The reverse inclusion follows from
symmetry. Hence `A_U` is self-adjoint.

### Audit conclusion

The restriction theorem is valid with the stated reduction laws. No spectral
theorem, separability, or complex scalar assumption is needed. This is the
part of the development most naturally suited to a general-purpose library.

## 2. Conjugation invariance of the spectral measure

Let `H_C` be the complexification of a real Hilbert space, and let `J` be its
canonical conjugation. If `A_C` is the complexification of a real self-adjoint
operator, then:

- `J(dom A_C) = dom A_C`;
- `A_C Jx = J A_C x` on `dom A_C`.

For a Borel set `S subset R`, let `P(S)` be the spectral projection of `A_C`.
Define

`Q(S) = J P(S) J`.

Although `J` is conjugate-linear, `Q(S)` is complex-linear because it is the
composition of two conjugate-linear maps with a complex-linear map. The family
`Q` is a projection-valued measure. Countable additivity is preserved by the
isometric involution `T -> J T J`.

The spectral integral of the real coordinate function against `Q` equals
`J A_C J`. The coordinate function is real-valued, so conjugating scalar
coefficients introduces no change. Since `J A_C J = A_C`, uniqueness in the
spectral theorem gives `Q=P`. Therefore

`J P(S) = P(S) J`

for every Borel `S`.

### Important proof obligation

The Lean proof must use the uniqueness theorem for the exact PVM/integral API
being used. It is not enough to prove that each `J P(S) J` is an orthogonal
projection. The integral representation of `A_C`, including its domain, is the
uniqueness datum.

### Audit conclusion

The claim is valid. The vulnerable part is API orientation, not mathematics.

## 3. Descent of a conjugation-invariant projection

Let `P : H_C -> H_C` be a bounded complex-linear orthogonal projection that
commutes with `J`. For `x in H_R`, `ofReal x` is fixed by `J`, so `P(ofReal x)`
is also fixed by `J`. Fixed points of canonical conjugation are precisely the
real copy. Define

`p x = re(P(ofReal x))`.

Then:

1. `P(ofReal x) = ofReal(p x)`;
2. `p` is bounded and real-linear;
3. complex-linearity of `P` gives
   `P(ofReal x + i ofReal y) = ofReal(px) + i ofReal(py)`;
4. therefore the complexification of `p` is exactly `P`;
5. injectivity of complexification transfers `p^2=p` and `p*=p` from `P`.

Thus `p` is the unique real orthogonal projection whose complexification is
`P`.

### Audit conclusion

The descent is canonical and non-vacuous. The fixed-point lemma should be made
explicit rather than hidden in simplification.

## 4. Equality of descended and canonical spectral ranges

Let `U_R = range p` and `U_C = range P`. Since `complexify(p)=P`,

`complexifySubmodule(U_R) = U_C`.

There are two robust proofs:

- range proof: complexification preserves the range of a real bounded map;
- projection proof: both submodules have the same orthogonal projection, and a
  closed subspace is determined by its orthogonal projection.

The projection proof is usually shorter after the projection descent theorem.
It also rules out accidentally descending a different real form of an
isomorphic complex subspace.

### Audit conclusion

The claim is valid and should remain in the trusted audit. It is a key
consistency theorem, not optional documentation.

## 5. Approximation numbers under real complexification

For a bounded real Hilbert-space operator `T`, the equality

`a_n(T_C) = a_n(T)`

is mathematically correct, but one tempting proof is incorrect.

### Invalid shortcut

Given a complex rank-`n` approximant `R`, the symmetrization

`(R + J R J) / 2`

commutes with conjugation and does not increase the approximation error.
However, its rank can be as large as twice the rank of `R`. This argument does
not preserve the index `n` and cannot prove exact equality of approximation
numbers.

### Valid proof used by the repository

The upper inequality complexifies a real finite-rank approximant. Complexifying
preserves both rank and operator norm.

For the reverse inequality, use the Hilbert-space min-max characterization. A
strict lower threshold below `a_n(T)` produces an `(n+1)`-element real linearly
independent family whose real span has that lower modulus. The same family in
the real copy is complex linearly independent. For

`z = x + i y`

in its complex span, both `x` and `y` lie in the original real span, and

`||T_C z||^2 = ||Tx||^2 + ||Ty||^2`.

The same lower modulus therefore holds on the complex span. The complex
min-max characterization gives the reverse inequality.

### Audit conclusion

The exact approximation-number and finite Ky Fan equalities are valid provided
the real and complex min-max lemmas have the same indexing convention. The
compiler audit should check `n` versus `n+1` carefully.

## 6. Descent through arbitrary unitary-invariant ideal families

The real Sylvester proof does not need to manufacture a complex ideal family
from an arbitrary real one. Instead it proves, after complexification, the
finite Ky Fan inequalities

`delta * KF_k(X_C) <= KF_k(C_C)`

for every `k`, transports them back using exact Ky Fan preservation, and invokes
the real family's finite-Ky-Fan dominance field.

This is sound only because `UnitaryInvariantIdealFamily` in the current API is
an alias of the stronger `KyFanDominantIdealFamily`; ordinary ideal laws alone
do not imply Fan dominance. Documentation and public names must continue to
make that requirement visible.

### Audit conclusion

The route supports every family represented by the current source-facing
abstraction. It must not be generalized to a weaker rectangular ideal record
without adding a Fan-dominance hypothesis.

## 7. Natural-input theorem dependency chain

The intended real theorem has the following honest chain:

1. complexify the real self-adjoint ambient operator;
2. obtain its canonical complex spectral PVM;
3. prove conjugation invariance and descend the exact projection;
4. identify the complexification of the descended range with the canonical
   complex spectral range;
5. prove that the descended range reduces the real operator;
6. construct the self-adjoint real restriction to the complementary range;
7. construct the exact/complementary orthogonal decomposition and both
   inclusion intertwiners;
8. package `UnboundedSinThetaData` internally;
9. apply the real all-gap sine-theta theorem.

No finite-dimensionality, compactness, boundedness of the ambient operator,
or supplied restriction/projection is needed.

## 8. Compiler-accepted outcome and future regression conditions

The route is compiler-accepted at commit `19e6d2fa5e5b` and must not be retired.
The following would instead constitute a future mathematical regression requiring
repair before any affected endpoint is trusted:

- the complexified closed operator does not commute with canonical conjugation
  on its full domain;
- the Spectra uniqueness theorem requires data not proved for the conjugated
  PVM;
- the descended projection fails to complexify exactly to the original one;
- the real spectral range fails to reduce the original operator;
- the approximation-number min-max indices disagree by one;
- the public ideal family lacks the finite-Ky-Fan dominance property used in
  the descent.

The completed repair pass found two genuine direction errors hidden behind earlier
elaboration failures.  Consequently, no remaining failure should be described as
purely elaborational until the relevant file has compiled.
