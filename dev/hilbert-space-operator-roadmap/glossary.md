# Glossary for the Hilbert-space operator theory family

This is a **learning companion**, not part of the roadmap specification. It explains the
mathematical vocabulary, Lean notation, and Mathlib structures used in the family. The
explanations favor intuition first and then state the more precise meaning needed to read
the proposed theorem signatures.

The glossary is not a replacement for the Mathlib documentation. In particular, a Lean
notation can be more general than the way it is used in these roadmaps. For example,
`E →ₗ[𝕜] F` means a linear map over a scalar semiring/ring accepted by the typeclass
assumptions; in this family, `𝕜` is usually constrained by `[RCLike 𝕜]`, so the intended
cases are real or complex scalars.

## A small signature, read from left to right

Consider a simplified theorem:

```lean
variable {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

example {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ LinearMap.operatorAbs A := by
  sorry
```

Read it as follows:

1. `𝕜` is a scalar type and `E` is a vector-space type.
2. `[RCLike 𝕜]` says `𝕜` behaves like `ℝ` or `ℂ`.
3. `[NormedAddCommGroup E]` gives vectors addition, subtraction, zero, and a norm.
4. `[InnerProductSpace 𝕜 E]` gives scalar multiplication and an inner product.
5. `[FiniteDimensional 𝕜 E]` says the vector space has finite dimension.
6. `{A : E →ₗ[𝕜] E}` is an implicit linear endomorphism of `E`.
7. `(hA : A.IsSymmetric)` is a proof that `A` is self-adjoint/symmetric.
8. `∃ U : E ≃ₗᵢ[𝕜] E` asks for a linear isometric equivalence from `E` to itself.
9. `(U : E →ₗ[𝕜] E)` coerces that equivalence to its underlying linear map.
10. `∘ₗ` is composition of linear maps.
11. `by sorry` is a placeholder proof in a suggested-signature file. The signature is
    being compile-checked; the theorem has not been proved in that file.

`LinearMap.operatorAbs` is intentionally a searchable placeholder name in the current
roadmap draft. The glossary does not settle its eventual public name.

---

# Part I — Lean notation and syntax

## Declarations

### `def`

Defines data or a function. Lean unfolds a definition when asked or when reduction makes
it useful.

```lean
 def f (x : ℝ) : ℝ := x + 1
```

### `noncomputable def`

Defines an object whose existence is mathematically valid but from which Lean cannot, or
is not being asked to, extract executable code. Spectral bases, choice-based inverses,
and many finite-dimensional constructions are naturally `noncomputable`.

### `theorem` and `lemma`

Both declare propositions together with proofs. The distinction is stylistic rather than
logical. A `theorem` is usually a more prominent result; a `lemma` is usually supporting
API.

### `structure`

Bundles fields into one type. Fields can include data and proofs.

```lean
structure Example where
  value : ℝ
  nonneg : 0 ≤ value
```

A structure is useful when several conditions should travel together and have named
projections. `IsMoorePenroseInverse` is proposed as a predicate/structure-like package so
the four Penrose conditions do not remain anonymous hypotheses.

### `class`

A structure intended for typeclass inference. If Lean sees `[CompleteSpace E]`, it searches
for an instance proving that `E` is complete.

### `namespace`

Groups declaration names. Inside `namespace LinearMap`, a declaration named `foo` becomes
`LinearMap.foo` and can often be used by dot notation as `A.foo`.

### `section` and `end`

Organize variables and assumptions without changing the eventual declaration names.

### `variable`

Introduces variables and typeclass assumptions reused by subsequent declarations.

### `example`

Checks a statement or proof without adding a permanent named declaration.

## Arguments and binders

### `(x : T)` — explicit argument

The caller normally supplies `x` explicitly.

### `{x : T}` — implicit argument

Lean normally infers `x` from other arguments or the expected type. It can still be given
explicitly with named-argument syntax such as `(x := value)`.

### `[C T]` — instance argument

Lean's typeclass system searches for an instance of `C T`. For example,
`[FiniteDimensional 𝕜 E]` supplies the theorem that `E` is finite-dimensional over `𝕜`.

### `⦃x : T⦄` — strict implicit argument

A stricter form of implicit argument. Lean attempts to infer it only after another explicit
argument has forced the relevant elaboration context.

### `∀ x, P x`

“For every `x`, proposition `P x` holds.”

### `∃ x, P x`

“There exists an `x` such that `P x` holds.”

### `fun x => ...`

An anonymous function, analogous to Python's `lambda x: ...`.

### `let x := value`

Introduces a local abbreviation inside an expression or proof.

## Types and propositions

### `Type`, `Type u`

The type of data types. Universe levels such as `u`, `v`, and `w` prevent paradoxes and
allow declarations to be universe-polymorphic.

### `Prop`

The type of propositions. A term of type `P : Prop` is a proof of `P`.

### `P → Q`

A function from proofs of `P` to proofs of `Q`; logically, implication.

### `P ↔ Q`

Logical equivalence: both `P → Q` and `Q → P`.

### `P ∧ Q`, `P ∨ Q`, `¬ P`

Conjunction (“and”), disjunction (“or”), and negation.

### `x = y`, `x ≠ y`

Equality and inequality.

### `x ∈ S`, `S ⊆ T`

Membership and subset inclusion.

### `x ≤ y`, `x < y`

Order relations supplied by the relevant ordered structure.

### `⊤` and `⊥`

The greatest and least elements of an ordered structure. Their meaning depends on the
object:

- for a `Submodule`, `⊤` is the whole space and `⊥` is `{0}`;
- for a `Set`, `⊤` behaves as the universal set and `⊥` as the empty set;
- for a lattice-valued predicate, they are its top and bottom elements.

## Definitional syntax

### `:=`

“Is defined to be.”

### `where`

Introduces the fields of a structure or local definitions attached to a declaration.

### `by`

Starts tactic-mode proof syntax.

### `sorry`

A trusted placeholder accepted by Lean with a warning. In `Suggested.lean`, it allows the
*statement* to elaborate without claiming that the theorem is proved there.

### `rfl`

Proof by reflexivity: both sides reduce to definitionally equal expressions.

### `_`

An expression Lean should infer.

### `@name`

Uses a declaration with all implicit arguments exposed explicitly.

### `name (x := value)`

Supplies a named argument explicitly.

## Coercions and subtypes

### `↑x`

A coercion. Lean converts `x` to another expected type using a registered coercion.
Examples include:

- a subtype element to its underlying value;
- a linear equivalence to its underlying function or linear map;
- a nonnegative real to a real.

### `(x : T)`

An explicit type ascription or coercion request.

### `Subtype`

A type containing values together with proofs that they satisfy a predicate. If
`U : Submodule 𝕜 E`, then an element `x : U` contains a vector `(x : E)` and a proof that
it belongs to `U`.

### `SetLike.coe`

The common coercion used by structures such as submodules and measurable sets to behave
like sets.

## Dot notation

If `LinearMap.foo` takes a linear map as its first explicit argument, Lean may allow:

```lean
LinearMap.foo A
A.foo
```

These are the same call. Dot notation is a convenience, not object-oriented dispatch in
the Python sense.

## Attributes and scopes

### `@[simp]`

Registers a theorem as a simplification rule. The `simp` tactic may use it automatically.

### `open Namespace`

Allows names in a namespace to be written without their prefix.

### `open scoped ScopeName`

Enables notation and scoped instances registered under a named scope, such as
`InnerProductSpace` or `BigOperators`.

### `classical`

Enables classical choice and classical decidability locally. It is common in finite
spectral constructions where a basis or ordering is selected nonconstructively.

## Common symbols

| Symbol | Meaning in these files |
|---|---|
| `ℕ` | natural numbers `0, 1, 2, ...` |
| `ℤ` | integers |
| `ℝ` | real numbers |
| `ℂ` | complex numbers |
| `ℝ≥0` | nonnegative real numbers (`NNReal`) |
| `ℝ≥0∞` | extended nonnegative reals (`ENNReal`), including `∞` |
| `𝕜` | conventional variable name for the scalar field |
| `∑` | finite sum, usually over a `Finset` or finite type |
| `∏` | finite product |
| `∫` | integral |
| `⨆` / `iSup` | supremum over an indexed family |
| `⨅` / `iInf` | infimum over an indexed family |
| `sSup` / `sInf` | supremum/infimum of a set |
| `‖x‖` | norm of `x` |
| `‖x‖₊` | nonnegative-real-valued norm where available |
| `⟪x, y⟫_𝕜` | inner product over scalar field `𝕜` |
| `x • y` | scalar action: scalar multiplication or a more general `SMul` action |
| `x⁻¹` | inverse; totalized in fields, so `0⁻¹ = 0` in Lean's field interface |
| `x ^ n` | natural-number power |
| `A⋆` / `star A` | star or adjoint-like involution, depending on the carrier |
| `Aᴴ` | conjugate transpose of a matrix |
| `Uᗮ` | orthogonal complement of a submodule `U` |
| `𝓝 x` | neighborhood filter at `x` |
| `atTop` | filter describing a variable tending to infinity |

---

# Part II — Maps, operators, matrices, and spaces in Lean

## `E → F`

An ordinary function from `E` to `F`. It carries no promise of linearity or continuity.

## `E →ₗ[𝕜] F` — `LinearMap`

A linear map from `E` to `F` over scalars `𝕜`. It preserves addition and scalar
multiplication:

- `A (x + y) = A x + A y`;
- `A (c • x) = c • A x`.

The notation itself is more general than real/complex vector spaces. In this family,
`[RCLike 𝕜]` commonly restricts the intended scalars to `ℝ` or `ℂ`.

If source and target are the same, `E →ₗ[𝕜] E` is a linear endomorphism.

## `E →L[𝕜] F` — `ContinuousLinearMap`

A continuous linear map. Between normed spaces, this is the formal object used for a
bounded linear operator. It contains:

- a linear map;
- a proof of continuity, equivalently boundedness in this setting.

It has an operator norm `‖A‖`.

Every continuous linear map has an underlying linear map `A.toLinearMap`. A plain
`LinearMap` is not automatically continuous in arbitrary infinite-dimensional spaces,
although finite-dimensional linear maps are continuous under the usual hypotheses.

## `E →ₗ.[𝕜] F` — `LinearPMap`

A partially defined linear map. Its domain is a submodule of `E`, not necessarily all of
`E`. This is Mathlib's model used here for an unbounded operator:

- `A.domain : Submodule 𝕜 E`;
- for `x : A.domain`, `A x : F`.

“Unbounded” does not mean the values are infinite. It means the operator is not represented
as an everywhere-defined bounded/continuous linear map. Differential operators are the
standard motivating examples.

## `E ≃ₗ[𝕜] F` — `LinearEquiv`

A bijective linear map with a linear inverse.

## `E ≃L[𝕜] F` — `ContinuousLinearEquiv`

A continuous linear equivalence whose inverse is also continuous.

## `E →ₗᵢ[𝕜] F` — `LinearIsometry`

A linear map preserving norms. It need not be onto.

## `E ≃ₗᵢ[𝕜] F` — `LinearIsometryEquiv`

A bijective linear isometry: a unitary/orthogonal equivalence in the Hilbert-space setting.
It preserves norms and inner products and has an inverse of the same kind.

## Composition notation

### `A ∘ₗ B`

Composition of linear maps. The right-hand map acts first:

```text
(A ∘ₗ B) x = A (B x)
```

### `A ∘L B`

Composition of continuous linear maps.

### `A * B`

Can denote multiplication in an algebra, including composition of endomorphisms when the
relevant multiplication instance is used. Unlike typed `∘L`, this requires both objects to
belong to a common multiplicative carrier.

That distinction is why a rectangular map `E →L[𝕜] F` cannot literally satisfy a
star-monoid formula `u * star u * u = u`: its adjoint reverses source and target, so the
three maps do not inhabit one common monoid type. The typed equation uses composition:

```text
u ∘L u.adjoint ∘L u = u
```

## `Matrix m n 𝕜`

A matrix with rows indexed by `m`, columns indexed by `n`, and entries in `𝕜`. In Mathlib,
it is definitionally a function:

```text
m → n → 𝕜
```

Finite matrices often use finite index types such as `Fin m` and `Fin n`.

## `Matrix.conjTranspose`, `Aᴴ`

The conjugate transpose: transpose the matrix and complex-conjugate its entries. Over
`ℝ`, conjugation is trivial, so this is the ordinary transpose.

## `Matrix.toEuclideanLin`

A bridge turning a matrix into a linear map between finite Euclidean spaces. It is useful
for transferring matrix statements to basis-free operator statements and back.

## `ℕ →₀ ℝ` — finitely supported function

The arrow with a subscript zero is `Finsupp`. A term `f : ℕ →₀ ℝ` is a sequence with only
finitely many nonzero entries. Mathlib's finite-dimensional singular values are represented
this way, making “zero past the rank” part of the object.

## `Fin n`

The type of natural numbers strictly less than `n`. An element carries both a value and a
proof that it is `< n`.

## `Fintype ι`

Says the type `ι` has finitely many elements and provides a computable enumeration. This
supports sums such as `∑ i : ι, ...`.

## `Finset`

A finite set with computable membership. Many finite sums and filtered index collections are
represented as `Finset`s.

## `EuclideanSpace 𝕜 ι`

A coordinate Hilbert space of vectors indexed by `ι`, with scalars `𝕜`. For finite `ι`, it
models `𝕜^n`.

## `lp`, `Lp`, and `ℓ²`

- `lp f p` is a sequence/function space whose coordinates have finite `p`-power sum, in
  the relevant Mathlib construction.
- `Lp` is a measure-theoretic space of functions modulo almost-everywhere equality.
- `ℓ²` informally means square-summable sequences; in this roadmap it also describes the
  column characterization of Hilbert–Schmidt operators.

---

# Part III — Foundational typeclasses and Mathlib concepts

## `Field 𝕜`

A commutative field: addition, multiplication, subtraction, and division, satisfying the
usual algebraic laws.

## `RCLike 𝕜`

Mathlib's shared interface for real-like and complex-like scalar fields. It provides:

- a real-part operation;
- conjugation;
- an absolute value/norm;
- facts common to `ℝ` and `ℂ`.

In ordinary use, the important instances are `ℝ` and `ℂ`. A theorem quantified over
`[RCLike 𝕜]` avoids proving separate real and complex versions.

## `NormedAddCommGroup E`

`E` is an additive commutative group with a norm compatible with its metric. You can add and
subtract vectors and measure their size.

## `SeminormedAddCommGroup E`

Like a normed additive commutative group, except distinct elements may have distance zero.
This weaker structure is useful for quotient constructions and seminorm-level statements.

## `NormedSpace 𝕜 E`

`E` is a vector space over normed scalars `𝕜`, and scalar multiplication is compatible with
the norms.

## `InnerProductSpace 𝕜 E`

`E` has an inner product over `𝕜`. The inner product determines the norm and allows notions
such as orthogonality, adjoints, and orthogonal projection.

Mathlib's inner-product convention matters when manipulating scalar factors; use the API
rather than relying on an informal first/second-slot convention.

## `CompleteSpace E`

Every Cauchy sequence in `E` converges. A complete normed vector space is a Banach space; a
complete inner-product space is a Hilbert space.

## `FiniteDimensional 𝕜 E`

`E` has finite dimension over `𝕜`. This is a proposition/typeclass, not a chosen basis. It
allows Mathlib to infer compactness of bounded closed sets, continuity of linear maps, and
existence of finite bases under the relevant assumptions.

## `T2Space X`

The topology on `X` is Hausdorff: distinct points can be separated by neighborhoods. This
ensures uniqueness of limits.

## `FirstCountableTopology X`

Every point has a countable neighborhood basis. It often permits sequential descriptions of
topological continuity and hemicontinuity.

## `MeasurableSpace X`

Specifies which subsets of `X` are measurable. It is the base structure for measures and
measurable functions.

## `BorelSpace X`

Says the measurable sets are the Borel sets generated by the topology.

## `Measure α`

A countably additive measure on measurable subsets of `α`.

## `IsFiniteMeasure μ`

The total measure `μ Set.univ` is finite.

## `Measurable f`

The preimage of every measurable set under `f` is measurable.

## `Integrable f μ`

`f` is measurable enough and has finite integral norm with respect to `μ`.

## `ENNReal` / `ℝ≥0∞`

The extended nonnegative reals: nonnegative real values together with `∞`. Measures and
integrals often naturally take values here because they may be infinite.

## `NNReal` / `ℝ≥0`

The nonnegative reals, represented as a real number plus a proof of nonnegativity.

## Filters: `𝓝`, `atTop`, and `Tendsto`

Mathlib expresses limits with filters.

- `𝓝 x` is the filter of neighborhoods of `x`.
- `atTop` means the index tends upward without bound.
- `Tendsto f l₁ l₂` means `f` maps convergence described by `l₁` to convergence described
  by `l₂`.

You do not need filter theory to read every theorem, but it explains signatures for
continuity, asymptotics, and limits of approximate minimizers.

---

# Part IV — Hilbert-space operator foundations

## Hilbert space

A complete inner-product space. Finite-dimensional real or complex inner-product spaces are
automatically complete. Infinite-dimensional Hilbert spaces include `ℓ²` and `L²` spaces.

## Bounded operator

A linear operator `A` for which there is a constant `C` such that

```text
‖A x‖ ≤ C ‖x‖
```

for all `x`. On normed spaces this is equivalent to continuity. Lean usually represents it
as `E →L[𝕜] F`.

## Operator norm

For a bounded operator `A`, `‖A‖` is the smallest bound in

```text
‖A x‖ ≤ ‖A‖ ‖x‖.
```

Equivalently, it is the supremum of `‖A x‖` over unit vectors.

## Endomorphism

A map from a space to itself, such as `E →ₗ[𝕜] E` or `E →L[𝕜] E`.

## Adjoint

For an operator `A : E → F`, the adjoint `A† : F → E` satisfies

```text
⟪A x, y⟫ = ⟪x, A† y⟫
```

with the exact conjugation convention handled by Mathlib. Lean names include `.adjoint` and,
in algebraic settings, `star A`.

## `LinearMap.IsSymmetric`

For a linear endomorphism on an inner-product space, symmetry means its inner-product action
is symmetric in the appropriate conjugate sense. In the finite-dimensional `RCLike` setting,
this is the linear-map formulation of self-adjointness.

## `IsSelfAdjoint`

A self-adjointness predicate, particularly important for bounded algebra elements and
unbounded `LinearPMap` operators. For an unbounded operator, self-adjointness includes both
formal adjoint symmetry and the correct domain/maximality condition; merely satisfying an
inner-product identity on the domain is not enough.

## `IsFormalAdjoint`

Expresses the inner-product adjoint identity for partially defined operators, including the
relevant domains. It is weaker than full self-adjointness.

## Symmetric versus self-adjoint

In finite dimensions, the distinction largely disappears under the standard hypotheses. In
infinite dimensions for unbounded operators:

- **symmetric** means the adjoint identity holds on the operator's domain;
- **self-adjoint** means the operator equals its adjoint, including domain equality.

The distinction is foundational in the unbounded spectral roadmap.

## Positive operator / `LinearMap.IsPositive`

A self-adjoint operator `A` is positive if

```text
re ⟪A x, x⟫ ≥ 0
```

for every `x`. Positive-semidefinite matrices are the coordinate version.

## Functional calculus

A construction that turns a scalar function `f` into an operator `f(A)`. For a finite
self-adjoint operator with eigenpairs `(λᵢ, eᵢ)`, the basic idea is

```text
f(A) eᵢ = f(λᵢ) eᵢ.
```

This lets one define square roots, spectral projections, absolute values/moduli, powers,
and many other operator functions uniformly.

## Continuous functional calculus / CFC

The continuous functional calculus applies continuous scalar functions to normal elements in
a suitable topological star algebra, such as bounded operators on a complex Hilbert space.
Mathlib names include `CFC.sqrt` and `CFC.abs`.

The foundations roadmap separately proposes a finite-dimensional `RCLike` functional
calculus because Mathlib's available C-star-algebra instances naturally emphasize the complex
bounded-operator setting.

## Borel functional calculus

Extends the functional calculus from continuous functions to bounded Borel measurable
functions. Characteristic functions of Borel sets then produce spectral projections.

## Positive square root

For a positive operator `A`, the positive square root is the unique positive operator `S`
with

```text
S ∘ S = A.
```

The roadmap defines it from the finite functional calculus at `Real.sqrt`.

## Operator modulus

For an operator `A`, the modulus is the positive square root of `A†A`:

```text
|A| = sqrt(A† A).
```

It satisfies `‖|A| x‖ = ‖A x‖`. The roadmap currently uses the searchable placeholder
`LinearMap.operatorAbs` for the finite-dimensional square construction and
`ContinuousLinearMap.modulus` for the rectangular bounded construction.

## Polar decomposition

Factors an operator into an isometric/partial-isometric part and a positive part:

```text
A = U |A|.
```

In finite-dimensional square settings, `U` can often be extended to a unitary. For a general
rectangular bounded operator, the canonical factor is a partial isometry.

## Isometry, unitary, and partial isometry

- An **isometry** preserves norms.
- A **unitary** is a surjective linear isometry from a Hilbert space to itself (or a linear
  isometric equivalence between spaces).
- A **partial isometry** is isometric on an initial subspace and zero on its orthogonal
  complement.

For an endomorphism in a star monoid, partial isometry can be expressed algebraically as

```text
u u† u = u.
```

For a rectangular map, the same typed equation must use composition because the adjoint
reverses source and target.

## Initial and final spaces

For a partial isometry `U`:

- the **initial space** is the subspace on which `U` acts isometrically, usually
  `(ker U)ᗮ` or the closure of the range of `|U|`;
- the **final space** is the closure of `range U`.

## Kernel and range

- `ker A` is the subspace of vectors sent to zero.
- `range A` is the subspace of outputs attained by `A`.

In Lean these are commonly `LinearMap.ker A` and `LinearMap.range A`.

## Rank-one operator

An operator constructed from two vectors, conceptually

```text
x ↦ ⟪v, x⟫ u.
```

Mathlib provides `InnerProductSpace.rankOne`. Finite-rank and singular-value expansions are
sums of rank-one operators.

## Singular values

The singular values of `A : E → F` are the nonnegative square roots of the eigenvalues of
`A†A`, sorted in decreasing order. They measure the magnitudes with which `A` stretches
orthogonal directions.

Mathlib's finite-dimensional API includes `LinearMap.singularValues : ℕ →₀ ℝ`.

## Singular vectors and singular system

Right singular vectors `vᵢ` and left singular vectors `uᵢ` satisfy

```text
A vᵢ = σᵢ uᵢ,
A† uᵢ = σᵢ vᵢ.
```

Together with the singular values `σᵢ`, they give the singular-value decomposition in a
basis-free form.

## Moore–Penrose inverse

The canonical pseudoinverse `A⁺` of a possibly noninvertible rectangular operator. It
inverts nonzero singular directions and sends the remaining directions to zero.

The four Penrose conditions are:

```text
A A⁺ A = A
A⁺ A A⁺ = A⁺
A A⁺ is self-adjoint
A⁺ A is self-adjoint.
```

A packaged predicate such as `IsMoorePenroseInverse A B` gives these conditions names and
supports a clean uniqueness theorem.

## Gram matrix

For a family of vectors `(vᵢ)`, the Gram matrix has entries

```text
Gᵢⱼ = ⟪vᵢ, vⱼ⟫.
```

It records all pairwise inner products.

## Gram operator

For an operator `A`, `A†A` is sometimes called its Gram operator. It acts on the source
space and contains the squared singular-value information.

## Gram rigidity

If two finite families have identical Gram matrices, there is an isometry between their
spans carrying one family to the other; under finite-dimensional ambient hypotheses, this
can be extended to an ambient linear isometric equivalence.

## `Submodule`

A vector subspace represented as a set closed under zero, addition, and scalar
multiplication. It is the main carrier for kernels, ranges, domains, spectral subspaces, and
orthogonal complements.

## Orthogonal complement `Uᗮ`

The subspace of vectors orthogonal to every vector in `U`.

## `HasOrthogonalProjection`

A typeclass asserting that a submodule has an orthogonal projection. Closed subspaces of a
Hilbert space have one; in finite dimension every subspace is closed.

## `Submodule.starProjection`

The bounded orthogonal projection onto a submodule. It is self-adjoint and idempotent.

## `IsStarProjection`

An algebraic predicate expressing that an element is both idempotent and self-adjoint.
Orthogonal projections are star projections.

## Invariant and reducing subspaces

A subspace `U` is:

- **invariant** for `A` if `A(U) ⊆ U`;
- **reducing** if both `U` and `Uᗮ` are invariant, equivalently the orthogonal projection
  onto `U` commutes with `A` under standard hypotheses.

For self-adjoint operators, invariance often implies reducing, but the notions should remain
separate in the API.

## Restricted operator and restricted spectrum

If `U` is invariant under `A`, one can restrict `A` to an operator on `U`. The spectrum of
that restricted operator is the **restricted spectrum**.

## Spectral subspace

The subspace spanned by eigenvectors, or more generally selected by a spectral projection,
whose spectral values lie in a set `Ω`.

## Projection gap

A distance between subspaces measured using their orthogonal projections. The foundations
roadmap emphasizes the sharp identity

```text
‖P - Q‖ = max(‖(1-Q)P‖, ‖(1-P)Q‖)
```

for orthogonal projections `P` and `Q`.

---

# Part V — Majorization, invariant seminorms, and angles

## Decreasing rearrangement

Sort the coordinates of a finite real vector in decreasing order, often after taking
absolute values. Majorization is normally stated using these sorted coordinates.

## Prefix sum

For a sequence `x₁ ≥ x₂ ≥ ...`, the `k`-th prefix sum is

```text
x₁ + ... + x_k.
```

In Lean, indexing may start at zero, so a `prefixSum k` may include indices up to `k` or the
first `k+1` entries depending on its definition. Check the declaration rather than assuming.

## Majorization

A vector `x` is majorized by `y` when the decreasing rearrangements satisfy:

- every proper prefix sum of `x` is at most the corresponding prefix sum of `y`;
- the total sums are equal.

Intuitively, `x` is more evenly distributed than `y`, without changing total mass.

## Weak majorization

Drops the equality-of-total-sum requirement and keeps prefix-sum inequalities. Because total
mass may decrease, closure under averaging/Robin-Hood transfers alone is not enough to prove
closure under weak majorization; an appropriate solidity/downward-closure or absolute
symmetry condition is needed.

## Robin Hood transfer / T-transform

Moves some mass from a larger coordinate to a smaller one while preserving the total sum.
Repeated transfers characterize strong majorization.

## Symmetric convex set

A convex set invariant under coordinate permutations and, in the gauge-ball setting,
usually sign changes. Such sets encode permutation- and sign-invariant seminorm balls.

## Schur–Horn theorem

Characterizes the possible diagonal vectors of a Hermitian matrix with prescribed
eigenvalues: the diagonal is majorized by the eigenvalue vector, and every majorized vector
occurs as a diagonal of a unitary conjugate.

## Symmetric gauge function

A seminorm or norm on finite coordinate vectors invariant under permutations and coordinate
sign changes. Applying it to the singular-value vector produces a unitarily invariant
operator seminorm/norm.

## Unitarily invariant seminorm

A seminorm `N` on operators satisfying

```text
N(U A V) = N(A)
```

for unitary `U` and `V` of compatible sizes. The generic roadmap abstraction is a
**seminorm** unless definiteness `N(A)=0 → A=0` is included.

## Unitarily invariant norm

A unitarily invariant seminorm that is definite. Schatten norms, the operator norm, trace
norm, Frobenius norm, and Ky Fan norms are standard examples in finite dimensions.

## Ky Fan `k`-sum / Ky Fan norm

The sum of the largest `k` singular values:

```text
σ₁(A) + ... + σ_k(A).
```

Ky Fan dominance says that domination of all such partial sums controls every unitarily
invariant seminorm.

## Principal angles

A sequence of angles measuring the relative position of two subspaces. Their cosines are the
singular values of the overlap map between orthonormal bases/isometric embeddings of the
subspaces.

## Overlap operator

Given isometric embeddings of two subspaces into an ambient Hilbert space, the overlap
operator is conceptually one adjoint followed by the other. Its singular values are the
cosines of the principal angles.

## Aligned bases

Orthonormal bases chosen so corresponding basis vectors realize the principal angles. They
turn abstract subspace geometry into coordinatewise cosine/sine relations.

## Sine and tangent of a subspace angle

Operators or singular-value sequences measuring the component of one subspace lying
orthogonally to another. Davis–Kahan bounds often estimate a sine-of-angle operator from a
residual divided by a spectral gap.

## Hoffman–Wielandt inequality

Bounds the squared Euclidean distance between suitably matched eigenvalue lists of normal
matrices by the squared Frobenius norm of their difference.

---

# Part VI — Approximation numbers and operator ideals

## Finite-rank operator

An operator whose range is finite-dimensional.

## Compact operator

An operator mapping bounded sets to relatively compact sets. Equivalently on Hilbert spaces,
it is a norm limit of finite-rank operators. Its singular/approximation numbers tend to zero.

## Approximation number

The `n`-th approximation number of a bounded operator `T` is the best operator-norm error
obtainable by approximating `T` with rank less than or equal to the corresponding cutoff:

```text
aₙ(T) = inf { ‖T - R‖ : rank R ≤ n }.
```

Indexing conventions vary. The roadmap fixes a zero-based Lean sequence and must state the
rank cutoff precisely.

## s-number

A sequence assigned to an operator that behaves like singular values under composition,
addition, and finite-rank approximation. Approximation numbers are one important s-number
scale.

## Operator ideal

A class of operators stable under left and right composition by arbitrary bounded operators:
if `T` is in the ideal, then `A T B` is also in the ideal when the compositions make sense.

## Ideal norm or ideal gauge

A size function on an operator ideal satisfying a composition estimate such as

```text
‖A T B‖_I ≤ ‖A‖ ‖T‖_I ‖B‖.
```

## Calkin correspondence

The relationship between two-sided ideals of bounded operators and appropriate ideals of
singular-value sequences. The exact formulation depends on separability and the chosen
operator/sequence-ideal framework.

## Schatten class `Sᵖ`

Operators whose singular or approximation numbers are `p`-summable:

```text
∑ n, σₙ(T)^p < ∞.
```

Important endpoints:

- `p = 1`: trace class/nuclear norm;
- `p = 2`: Hilbert–Schmidt class;
- `p = ∞`: bounded/compact endpoint measured by the supremum/operator norm, represented
  separately unless the exponent type explicitly contains infinity.

## Trace norm / nuclear norm

The `p = 1` Schatten norm: the sum of singular values.

## Hilbert–Schmidt operator

An operator `T` for which

```text
∑ i, ‖T eᵢ‖² < ∞
```

for one, hence every, orthonormal basis `(eᵢ)`. Its norm is the square root of this sum. In
finite dimensions this is the Frobenius norm.

## Frobenius norm

For a finite matrix, the square root of the sum of squared absolute values of all entries.
It also equals the square root of the sum of squared singular values.

## Trace

The sum of diagonal entries in finite dimensions. For trace-class operators, it extends in a
basis-independent way to infinite-dimensional Hilbert spaces.

## Eckart–Young theorem

The best rank-`n` approximation in operator or Frobenius-type norms is obtained by truncating
the singular-value decomposition. The exact norm and indexing determine the precise form.

## Antitone sequence

A decreasing sequence: `i ≤ j` implies `x j ≤ x i`. Approximation and singular-value
sequences are normally antitone.

## `tsum`

Mathlib's infinite sum over a type. It is totalized: when a family is not summable, its exact
behavior follows Mathlib's definition, so theorems usually carry `Summable` hypotheses when
mathematical convergence matters.

---

# Part VII — Self-adjoint spectral theory

## Spectrum

For a bounded operator `A`, the spectrum is the set of scalars `λ` for which `λI - A` is not
invertible. For an unbounded operator, invertibility must also account for the operator's
domain and boundedness of the inverse.

## Resolvent set

The complement of the spectrum: scalars `z` for which `A - zI` has an appropriate bounded
everywhere-defined inverse.

## Resolvent

The inverse operator

```text
R(z, A) = (A - zI)⁻¹
```

for `z` in the resolvent set. Resolvent identities encode much of spectral theory.

## `LinearPMap.resolventSet`

A proposed/shared vocabulary for the resolvent set of a partially defined operator. The
family should avoid defining incompatible copies in semigroup, spectral, and perturbation
roadmaps.

## Closed operator

An operator is closed if its graph

```text
{ (x, A x) : x ∈ domain A }
```

is a closed subspace of `E × F`.

## Closable operator

An operator whose graph closure is itself the graph of another operator. That operator is its
closure.

## Graph norm

On the domain of `A`, a norm such as

```text
‖x‖_A = sqrt(‖x‖² + ‖A x‖²).
```

`A` is closed exactly when its domain is complete in the graph norm under the standard
hypotheses.

## Core

A subspace of the domain dense in the graph norm. Restricting a closed operator to a core
determines the full operator after closure.

## Dense domain

The operator's domain is dense in the ambient Hilbert space. Dense domains are needed to
define adjoints of unbounded operators with the expected properties.

## Semibounded operator

A self-adjoint or symmetric operator whose quadratic form has a lower or upper bound, such as

```text
re ⟪A x, x⟫ ≥ c ‖x‖².
```

## Relative boundedness

An operator `B` is relatively bounded with respect to `A` if

```text
‖B x‖ ≤ a ‖A x‖ + b ‖x‖
```

on `domain A`. If the relative bound `a` is small enough, perturbation theorems preserve
closedness or self-adjointness.

## Kato–Rellich theorem

A self-adjoint operator plus a symmetric relatively bounded perturbation with relative bound
strictly less than one remains self-adjoint on the original domain.

## Projection-valued measure (PVM)

A measure whose values are orthogonal projections rather than scalars. For disjoint sets,
the projections add orthogonally; the whole space maps to the identity projection.

A self-adjoint operator can be represented as an integral of the scalar variable against its
spectral PVM.

## Spectral measure

The PVM associated with a self-adjoint operator. It provides spectral projections and the
Borel functional calculus.

## Cayley transform

Transforms a self-adjoint unbounded operator into a unitary operator, typically

```text
U = (A - i)(A + i)⁻¹.
```

It allows unitary spectral theory to construct the unbounded self-adjoint spectral measure.

## One-parameter unitary group

A family `U(t)` of unitary operators satisfying

```text
U(0) = I
U(s+t) = U(s)U(t)
```

and strong continuity in `t`.

## Strong continuity

For each vector `x`, the orbit `t ↦ U(t)x` is continuous. This is weaker than requiring
`t ↦ U(t)` to be continuous in operator norm.

## Generator

The infinitesimal derivative at zero of a strongly continuous group or semigroup. It is
generally an unbounded operator defined only on vectors for which the derivative exists.

## Stone's theorem

Strongly continuous one-parameter unitary groups correspond to self-adjoint generators:
formally,

```text
U(t) = exp(i t A).
```

The theorem includes existence and uniqueness of the generator and the converse construction.

## Yosida approximation

A bounded operator built from the resolvent of an unbounded generator, approximating the
unbounded operator while preserving enough structure to prove generation and convergence
results.

---

# Part VIII — Sylvester equations and spectral-subspace perturbation

## Sylvester equation

An operator equation of the form

```text
A X - X B = C
```

where `A` acts on the target side and `B` on the source side. The natural generality is
rectangular:

```text
A : E → E
B : F → F
X, C : F → E.
```

This is why the family owner declaration should not force `E = F`.

## Sylvester operator

The linear operator on maps `X` given by

```text
S(X) = A X - X B.
```

Solving the Sylvester equation means inverting `S` on `C`.

## Rosenblum theorem

If the spectra of `A` and `B` are disjoint under suitable hypotheses, the Sylvester operator
is invertible. Integral formulas or spectral decompositions then yield a solution and norm
bound.

## Spectral separation / spectral gap

A positive distance between two relevant spectral sets. It appears in denominators of
perturbation estimates: a larger gap makes invariant subspaces more stable.

## Residual

For an approximate invariant embedding `X`, a residual such as

```text
R = A X - X A₀
```

measures failure of exact intertwining. Davis–Kahan-type theorems bound a subspace-angle
operator by `‖R‖ / gap`.

## Intertwining relation

An equation

```text
A X = X B
```

saying that `X` transports the action of `B` to the action of `A`.

## Davis–Kahan sin Θ theorem

Bounds the angle between invariant/spectral subspaces of nearby self-adjoint operators in
terms of the perturbation or residual divided by a spectral gap.

## Directed sine operator

An operator measuring the component of one subspace lying in the orthogonal complement of
another. A theorem must construct or constrain this operator from the subspace data; an
arbitrary unconstrained argument named `sinTheta` can be scaled and cannot satisfy a fixed
bound.

## tan Θ and sin 2Θ theorems

Related perturbation estimates using tangent or double-angle formulations. Their hypotheses
and constants differ, but they share the same projection and spectral-separation vocabulary.

## Haagerup–Zsidó kernel

An extremal Fourier-analytic kernel used to obtain the sharp `π/2` constant in a Sylvester
or spectral-subspace estimate. The roadmap separates construction and Fourier-transform
properties of this kernel from the later perturbation application.

## Ideal-valued perturbation bound

A perturbation theorem measured not only in operator norm but in a unitarily invariant
seminorm or operator-ideal gauge. It allows, for example, Frobenius or Schatten control of
subspace error.

---

# Part IX — Matrix spectral statistics and optimization

## Positive semidefinite matrix / `Matrix.PosSemidef`

A Hermitian matrix `B` is positive semidefinite if

```text
xᴴ B x ≥ 0
```

for every vector `x`. Equivalently, its eigenvalues are nonnegative.

## Rank factorization

A factorization

```text
M = L R
```

where the intermediate dimension is the rank of `M`, so `L` has full column rank and `R`
has full row rank.

## Gram factorization

A positive-semidefinite matrix can be written

```text
B = Yᴴ Y
```

or, depending on conventions, `B = Y Yᴴ`. This realizes `B` as the Gram matrix of a family
of vectors.

## Classical multidimensional scaling (MDS)

Constructs an embedding of points from a distance matrix. After double centering, a
positive-semidefinite Gram matrix is spectrally factorized to recover coordinates.

## Correspondence / set-valued map

A function `K : P → Set X` assigning a set of feasible points to each parameter. Berge's
maximum theorem studies continuity of values and optimizers when `K` varies.

## Upper hemicontinuity

Informally, feasible points cannot suddenly appear far away in the limit. A common closed
graph/sequential intuition is: if `pₙ → p` and `xₙ ∈ K(pₙ)` with `xₙ → x`, then
`x ∈ K(p)` under suitable compactness/topological assumptions.

## Lower hemicontinuity

Informally, every feasible point at the limit can be approximated by feasible points for
nearby parameters. This side is essential when comparing nearby minimizers against a chosen
competitor at the limiting parameter.

## Berge maximum theorem

Under continuity of the objective and suitable compactness, nonemptiness, and upper/lower
hemicontinuity of the feasible correspondence:

- the optimal value varies continuously;
- the argmax/argmin correspondence is nonempty, compact-valued, and upper
  hemicontinuous.

Omitting lower hemicontinuity from the varying-feasible-set argmin theorem can make the
statement false.

## `IsMinOn f K x`

Says `x ∈ K` and `f x ≤ f y` for every `y ∈ K`.

## Argmin correspondence

The set of minimizers of an objective over the feasible set at each parameter.

## Approximate minimizer

A point `x` satisfying

```text
f(x) ≤ inf_{y∈K} f(y) + ε.
```

Approximate minimizers are important when numerical optimization or statistical estimation
does not return an exact optimum.

## Γ-convergence

A notion of convergence for functionals designed so minimizers and approximate minimizers
behave well. It combines a lower-bound condition with the existence of recovery sequences.

## Random matrix

A matrix-valued random variable. The roadmap focuses on selected elementary spectral
statistics and concentration results, not the full theory of random matrices.

## Sample covariance

An empirical estimate of covariance built from observations. In vector notation it is an
average of centered rank-one operators.

## Matrix concentration inequality

A probability bound controlling the spectral/operator norm of a sum of independent random
matrices. Matrix Bernstein is a central sharp example.

## Union-bound route versus matrix Bernstein

A coordinatewise argument may bound all entries or all directions and combine them with a
union bound. It is often simpler but dimensionally weaker than a dedicated matrix
concentration theorem.

## Chebyshev's inequality

Bounds tail probability using variance:

```text
P(|X - E X| ≥ t) ≤ Var(X) / t².
```

The roadmap uses elementary moment bounds where possible before requesting sharper
concentration infrastructure.

## Sorted eigenvalues and spectral transform

A measurable or continuous map assigning a Hermitian matrix its eigenvalues in a fixed
order. Such a map is needed to treat spectral statistics as random variables.

---

# Part X — Quick lookup of commonly seen Mathlib names

| Name | Reading |
|---|---|
| `LinearMap` | algebraic linear map, not inherently continuous |
| `ContinuousLinearMap` | bounded/continuous linear map |
| `LinearPMap` | partially defined linear map, used for unbounded operators |
| `LinearMap.IsSymmetric` | finite/bounded linear-map symmetry predicate |
| `LinearMap.IsPositive` | positivity via quadratic forms |
| `ContinuousLinearMap.adjoint` | Hilbert-space adjoint of a bounded map |
| `InnerProductSpace.rankOne` | rank-one operator made from two vectors |
| `Submodule` | vector subspace |
| `Submodule.starProjection` | orthogonal projection onto a submodule |
| `IsStarProjection` | self-adjoint idempotent predicate |
| `HasOrthogonalProjection` | evidence that a submodule admits an orthogonal projection |
| `HilbertBasis` | complete orthonormal basis of a Hilbert space |
| `Orthonormal` | predicate that a family is orthonormal |
| `Matrix.IsHermitian` | matrix equals its conjugate transpose |
| `Matrix.PosSemidef` | positive-semidefinite matrix predicate |
| `ConvexOn` | convexity of a function on a set |
| `IsCompact` | compact set predicate |
| `Continuous` | topological continuity |
| `Measurable` | measurability of a function |
| `Integrable` | integrability of a function |
| `Summable` | convergence of an indexed infinite sum |
| `HasSum f a` | indexed family `f` has sum `a` |
| `tsum f` | totalized infinite sum of `f` |
| `UpperHemicontinuousAt` | upper hemicontinuity of a correspondence at a point |
| `LowerHemicontinuousAt` | lower hemicontinuity of a correspondence at a point |
| `IsMinOn` | a point minimizes a function on a set |
| `IsCompactOperator` | compact bounded operator predicate |
| `IsSelfAdjoint` | self-adjointness predicate in the relevant carrier |
| `IsStarNormal` | normality: commutation with the star/adjoint |
| `ENNReal` | extended nonnegative reals `ℝ≥0∞` |
| `NNReal` | nonnegative reals `ℝ≥0` |
| `Cardinal` | cardinal-number type, used for dimensions beyond finite naturals |

## Suggested next additions

When a roadmap signature introduces a term not covered here, add it in the section owned by
the roadmap that defines the concept. Prefer entries that answer three questions:

1. What does the object mean mathematically?
2. What Lean/Mathlib type represents it?
3. Why does this roadmap need it?

That keeps the glossary useful as the proposed API evolves without turning it into a copy of
Mathlib's generated documentation.
