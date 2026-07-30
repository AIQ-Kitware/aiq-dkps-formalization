# Roadmap: singular values and the singular system

**Topic T03 of the candidate design.** Four modules. Depends on T01. T06, T07
and T09 consume it, and T17 through them.

## What this topic adds, given that Mathlib has singular values

Mathlib already defines `LinearMap.singularValues : ℕ →₀ ℝ` for a map between
finite-dimensional inner product spaces. So the question a reviewer opens with
is what four more modules are for. The answer is different for each, and only
the first is about the *values*:

| Module | What Mathlib lacks |
|---|---|
| `SingularValues` | An accessor at `ContinuousLinearMap` level. Nothing mathematical. |
| `RectangularSingularValues` | That `A†A` and `AA†` share their nonzero spectrum **with multiplicity**. |
| `SingularSystem` | The singular **vectors** — Mathlib has the values, not the system. |
| `MoorePenroseInverse` | The pseudoinverse for linear maps, with all four Penrose identities. |

### `SingularValues` is an accessor, and says so

Between finite-dimensional spaces every linear map is continuous, so the two
notions of singular value agree definitionally. The module exists because the
operator-theoretic consumers — approximation numbers, Ky Fan norms,
Eckart–Young — all work with `ContinuousLinearMap`, and without an accessor
every public statement would have to spell `T.toLinearMap.singularValues n`,
leaking the coercion into the statement and into every downstream proof.

`ContinuousLinearMap.toLinearMap_singularValues` moves freely between the two,
and the lemmas are one-line delegations. **This is a naming-surface module, not
a mathematical one**, and a reviewer should confirm exactly that: if any lemma
here had real content it would belong in Mathlib instead.

### The rest is genuinely absent upstream

`SingularSystem` is the substantial one. It builds the intrinsic singular system
directly for a rectangular map: the right singular basis is the sorted
orthonormal eigenbasis of `A†A`, and left singular vectors are the normalised
images `σᵢ⁻¹ • A vᵢ`. What it proves:

* `apply_rightSingularBasis_eq_smul_leftSingularVector` — the singular relation
  `A vᵢ = σᵢ • uᵢ`, **including the zero case**;
* `orthonormal_leftSingularVector_subtype` — left singular vectors attached to
  nonzero singular values are orthonormal;
* `selfCompAdjoint_apply_leftSingularVector` — those vectors are eigenvectors of
  `AA†` with eigenvalue `σᵢ²`;
* `singular_reconstruction` and `eq_sum_singularValue_rankOne` — the singular
  expansion of `A`;
* `exists_orthonormalBasis_extending_leftSingularVector` — the nonzero left
  singular family extends to an orthonormal basis of the codomain.

The last is the one downstream topics actually need: an expansion is only usable
if the partial family extends, and for a rectangular map that is not automatic.

## The design decision worth reviewing: intrinsic, not matrix-mediated

Everything here is stated for a **linear map between spaces**, never for a
matrix in a chosen pair of bases. That is the harder route — the easy one is to
pick bases, quote the matrix SVD, and transport — and it is chosen deliberately,
because the consumers are basis-free:

* T06 (principal angles) compares two *subspaces*;
* T07 (rectangular unitarily invariant norms) is about norms invariant under
  choice of basis;
* T17 (Davis–Kahan) states its conclusions about spectral subspaces.

If the singular system were matrix-mediated, every one of those would carry a
basis choice through its statement and then have to prove independence of it.
`RectangularSingularValues` is what makes the intrinsic route work: it shows the
two Gram operators `A†A` on `E` and `AA†` on `F` share their nonzero spectrum
including multiplicity, which is the fact that lets a rectangular map have *one*
singular sequence rather than two.

## Moore–Penrose: constructed, then identified

`MoorePenroseInverse` builds the pseudoinverse from the intrinsic right singular
basis — on `vᵢ` the Gram operator acts by `σᵢ²`, so the inverse uses coefficient
`(σᵢ²)⁻¹` against the rank-one map `y ↦ ⟪A vᵢ, y⟫ vᵢ`, and zero singular values
contribute zero through total field inversion.

**That construction is only *a* generalised inverse.** That it is *the*
Moore–Penrose inverse is the content of the four Penrose identities, and the
module proves all four rather than the two that the construction makes obvious:

1. `A A⁺ A = A`
2. `A⁺ A A⁺ = A⁺`
3. and 4., the self-adjointness of `A A⁺` and `A⁺ A`

All four are present — `comp_moorePenroseInverse_comp`,
`moorePenroseInverse_comp_comp`, `isSymmetric_moorePenroseInverse_comp`,
`isSymmetric_comp_moorePenroseInverse` — and so, better, is
**`eq_moorePenroseInverse_of_penrose`: anything satisfying the four identities
*is* this map.**

That converse is what makes the name honest. A construction satisfying only the
first two is a generalised inverse and there are many; uniqueness under all four
is the characterisation, and it is proved here rather than cited.

## What a reviewer should check

1. **That `SingularValues` has no mathematical content** — if it does, that
   content belongs upstream in Mathlib.
2. **That the singular system is intrinsic**, with no basis choice in any
   statement.
3. **That the uniqueness converse is proved**, not just the four identities —
   `eq_moorePenroseInverse_of_penrose`. Without it the module has constructed
   *a* generalised inverse and named it after Moore and Penrose.
4. **That the zero case is handled** in the singular relation — it is the case a
   rectangular treatment gets wrong first, and it is called out explicitly in
   `apply_rightSingularBasis_eq_smul_leftSingularVector`.

## Prerequisites

T01 (positive square root and functional calculus), for the Gram operator's
eigenbasis. Nothing else.
