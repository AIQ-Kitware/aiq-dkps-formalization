# Stage 1 finite-dimensional infrastructure math-ahead handoff

Base: `d3ae782b677406ed378815fa71b46ae99e95b37c`.

This batch replaces two fictional historical APIs with concrete reusable
constructions.

## Self-adjoint functional calculus

`ForMathlib/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean`
defines the finite-dimensional calculus by the ordered orthonormal eigenbasis
already supplied by pinned Mathlib.  Its initial API contains:

- diagonal action on eigenvectors;
- preservation of symmetry;
- recovery of the original operator from the identity function;
- congruence for functions agreeing on the finite spectrum;
- the multiplication/composition law.

The API deliberately requires an explicit symmetry witness.  The angle module
now supplies the positivity-derived symmetry witness for `sinAngleOperator`,
and recursively uses symmetry preservation for the tangent operators.  This is
preferable to a total definition that silently returns zero on nonsymmetric
input.

## Moore--Penrose inverse

`ForMathlib/Analysis/InnerProductSpace/MoorePenroseInverse.lean` defines the
rectangular pseudoinverse from the existing intrinsic singular system:

`A⁺ = Σᵢ σᵢ⁻¹ rankOne(vᵢ, uᵢ)`.

Zero singular values contribute zero through total field inversion.  The first
candidate lemmas establish action on nonzero singular vectors, the first
Penrose identity, and the left-inverse law under injectivity.

`inverseOnRange A hA` is a proof-carrying name for the same total map.  The
mathematically correct law is

`inverseOnRange A hA ∘ A = id`.

Do not restore historical uses of `A ∘ inverseOnRange A hA = id` for a merely
injective rectangular map.  That equation is false unless surjectivity is also
available.  Repair dependent graph proofs by using the left-inverse law, or by
identifying `A ∘ A⁺` with the orthogonal projection onto `range A`.

## Compiler order

Run sequentially:

```bash
lake env lean ForMathlib/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean
lake env lean ForMathlib/Analysis/InnerProductSpace/MoorePenroseInverse.lean
lake env lean DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean
lake env lean DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean
```

Repair these four modules before continuing to rectangular Schatten norms.
The latter has a separate missing majorization/Minkowski layer and is not
papered over in this batch.

## Required follow-up API

Once the defining modules compile, add the remaining generally useful Penrose
laws as separate compiler-verified steps:

- `A⁺ A A⁺ = A⁺`;
- `A A⁺` is the orthogonal projection onto `range A`;
- `A⁺ A` is the orthogonal projection onto `(ker A)ᗮ`;
- adjoint compatibility `(A⁺)† = (A†)⁺`;
- equality with the ordinary inverse for a bijective endomorphism.

Do not add those as uncompiled decorative declarations.  Establish each only
when its downstream use is ready to compile.

## Acceptance

Use exit status throughout.  Preserve all guarded declarations.  A successful
static contract is not proof acceptance.
