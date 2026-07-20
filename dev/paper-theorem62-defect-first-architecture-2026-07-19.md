# Davis–Kahan Theorem 6.2: defect-first Hilbert–Schmidt architecture

Date: 2026-07-19

## Status

This note records the corrected mathematical construction for the square-norm
Sylvester estimate used by Davis–Kahan Theorem 6.2. It supersedes the earlier
model that attempted to tensorize the unknown bounded solution before proving
that it was Hilbert–Schmidt.

That earlier direction is circular. A general bounded operator does not define
a vector in the Hilbert–Schmidt completion. The defect is known to be
Hilbert–Schmidt; therefore the construction must start from the defect.

## Target

Let `A` and `B` be closed self-adjoint operators on complex Hilbert spaces `E`
and `F`. Let `X : F → E` be bounded and satisfy

`A X - X B = C`

on `dom B`, with `C` Hilbert–Schmidt. Assume

`δ ≤ |λ - α|`

for every `λ ∈ spectrum A` and `α ∈ spectrum B`, where `δ > 0`.

The desired conclusion is

`X` is Hilbert–Schmidt and `δ ‖X‖₂ ≤ ‖C‖₂`.

No compactness assumption on `A`, `B`, or `X` is permitted.

## 1. Canonical Hilbert space of rectangular Hilbert–Schmidt operators

Use

`HS(F,E) = E ⊗₂ conjugate(F)`.

For `z ∈ E ⊗₂ conjugate(F)`, define `J z : F → E` by

`J z x = R_x* z`,

where `R_x u = u ⊗ conjugate(x)`.

For pure tensors,

`J(u ⊗ conjugate(v)) x = ⟨v,x⟩ u`.

Thus `J` is the canonical rank-one dictionary. Parseval in any Hilbert basis
shows

`‖z‖² = Σ_i ‖J z e_i‖²`.

Combining this with the finite-cutoff Eckart–Young identity proves that `J`
is an isometric equivalence from the Hilbert tensor product onto the bounded
operators whose complete approximation-number square sum is finite. This is
exactly the repository's paper square norm; it is not a second notion of
Hilbert–Schmidt membership.

The implementation leaves are:

- `Spectra/Spaces/Tensor/HilbertSchmidt.lean`;
- `Ideals/PaperHilbertSchmidtBasis.lean`.

## 2. Left-minus-right unitary flow

Let

`U_A(t) = exp(i t A)` and `U_B(t) = exp(i t B)`.

On `HS(F,E)`, define

`W(t) = U_A(t) ⊗ conjugate(U_B(t))`.

Under `J`,

`J(W(t) z) = U_A(t) (J z) U_B(-t)`.

The sign is forced by the conjugate second factor and is the correct
left-minus-right orientation.

The bounded group construction and the operator intertwining identity live in
`Spectra/Spaces/Tensor/HilbertSchmidtFlow.lean`.

## 3. The generator is the closed Sylvester operator

Let `L` be the Stone generator of `W`. The required graph theorem is

`z ∈ dom L` and `L z = c`

if and only if `J z` maps `dom B` into `dom A` and

`A (J z) x - (J z) B x = J c x`

for every `x ∈ dom B`.

The direction from the tensor generator to the closed Sylvester equation can
be proved directly from difference quotients. For `x ∈ dom B`, write

```
U_A(t) Jz U_B(-t)x - Jz x
  = [U_A(t) Jz U_B(-t)x - Jz x]
```

and isolate the difference quotient of `U_A(t) Jz x` by adding and subtracting
`U_A(t) Jz x`. The first term converges to `Jc x`; the second uses the reversed
`B`-group quotient and converges to `-Jz(Bx)`. Hence

`genDiffQuot U_A (Jz x) → Jc x + Jz(Bx)`.

Stone uniqueness gives `Jz x ∈ dom A` and

`A(Jz x) = Jc x + Jz(Bx)`.

The converse is a Hilbert–Schmidt Duhamel argument. First prove it for finite
spectral cutoffs, where both generators are bounded and differentiation is
ordinary. Then pass to the tensor limit using the closedness of `L` and the
square-norm convergence of the cutoffs. This is the right location for domain
subtype bookkeeping; it must not be hidden in the public theorem.

## 4. Product spectral support

The scalar spectral measure of `W` is the pushforward by

`(λ, α) ↦ λ - α`

of the product/joint spectral measure obtained from the lifted left and right
PVMs on `E ⊗₂ conjugate(F)`.

There are two acceptable constructions.

### Route A: lifted PVMs

Lift the spectral projections by

- `P_A(S) ↦ P_A(S) ⊗ I`;
- `P_B(T) ↦ I ⊗ conjugate(P_B(T))`.

Their ranges commute. Package their joint PVM, then push it forward along the
difference map.

### Route B: group characterization

Construct the left and right tensor groups, use their Stone generators, prove
strong commutativity from pointwise group commutation, and use the existing
joint-PVM theorem. Identify the PVM of the product group with the pushed-forward
joint PVM by equality of characteristic functions and
`Measure.ext_of_charFun`.

Route B reuses more of Spectra, but it still needs the graph identification in
Section 3 and the support comparison with the original spectra.

The current structural leaves remove an unrelated KMS dependency from the
joint-PVM construction:

- `BornRule/POVMCore.lean`;
- `BornRule/Joint/ProjectivePVM.lean`;
- `ProjValMeasure/GeneralMap.lean`;
- `OneParameterUnitaryGroup/Product.lean`.

## 5. Defect-first inverse

Let `c ∈ HS(F,E)` be the tensor representing `C`. The pairwise spectral gap
implies that the scalar spectral measure of `c` for `W` is supported in

`{s | δ ≤ |s|}`.

Define the bounded Borel symbol

```
gδ(s) = if δ ≤ |s| then 1/s else 0.
```

Set

`z₀ = Φ_W(gδ) c`.

Then

`‖z₀‖ ≤ δ⁻¹ ‖c‖`.

The mixed bounded/unbounded product law gives

`(∫ s dP_W(s)) z₀ = c`,

because `s gδ(s) = 1` almost everywhere on the scalar spectral measure of
`c`. The vector-local inverse is implemented in
`SpectralTheory/Calculus/SpectralGapInverse.lean`.

By Section 3, `X₀ = J z₀` solves the closed Sylvester equation with defect
`C`. It is Hilbert–Schmidt and

`δ ‖X₀‖₂ ≤ ‖C‖₂`.

## 6. Identify the supplied bounded solution

The supplied `X` and constructed `X₀` are both bounded solutions. Their
difference solves the homogeneous equation.

Uniqueness under pairwise spectral separation must be proved at the bounded
operator level. It may be obtained from the same tensor spectral multiplier
once `X-X₀` is known Hilbert–Schmidt, but that would be circular. Use instead
the standard resolvent/Rosenblum uniqueness theorem for bounded intertwiners:
separated self-adjoint spectra imply the only bounded solution of

`A Y - Y B = 0`

is zero. This uniqueness statement is independent of any ideal membership and
should be exposed as its own reusable theorem.

Then `X = X₀`, yielding the desired membership and sharp estimate.

## 7. Why the earlier scalar-measure model was invalid

The old model selected a tensor vector representing `X` before proving that
`X` had finite square energy. That assumes the conclusion. Its scalar Born
measure and all subsequent integral identities were therefore unavailable.

The corrected construction tensors `C`, which is known to have finite square
energy, applies a bounded inverse multiplier, and only then obtains the
Hilbert–Schmidt solution.

## 8. Current implementation boundary

The current static implementation supplies the following reusable pieces:

1. the tensor/operator dictionary and its exact square-norm identification;
2. the tensor-flow construction;
3. the generator-to-closed-Sylvester graph direction needed by the inverse;
4. the vector-local reciprocal functional calculus and its sharp norm bound;
5. the defect-first reduction from those ingredients;
6. bounded homogeneous uniqueness for the three already-supported source gap
   configurations.

The exact pairwise-distance theorem still has two independent mathematical
obligations:

1. **Pairwise tensor spectral support.**  Pairwise separation of
   `spectrum A` and `spectrum B` must imply that the scalar spectral measure of
   the Hilbert--Schmidt defect tensor for the left-minus-right flow is supported
   in `{s | delta <= |s|}`.  This should be proved from the lifted left and right
   spectral measures, their joint PVM, and pushforward by `(lambda, alpha) |->
   lambda - alpha`.
2. **Bounded homogeneous uniqueness under arbitrary pairwise separation.**  If
   a bounded `Y` satisfies `A Y - Y B = 0`, then `Y = 0` whenever the spectra
   are disjoint.  This must be proved before knowing that `Y` is
   Hilbert--Schmidt.  The clean route is generator intertwining -> unitary-group
   intertwining -> spectral-projection intertwining -> disjoint-support
   annihilation.

The existing three-gap uniqueness theorem is useful elsewhere but is not a
replacement for item 2: arbitrary pairwise-separated closed subsets of the
real line need not satisfy an interval/exterior or ordered half-line
configuration.

Once these two obligations compile, Theorem 6.2 is a short defect-first
functional-calculus argument. Neither requires compactness or finite
dimension.
