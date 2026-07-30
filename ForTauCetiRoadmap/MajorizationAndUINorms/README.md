# Roadmap: majorization, Schur–Horn, and unitarily invariant norms

**Topic T05 of the candidate design.** Five modules. Depends on T01, T02 and
T04. Consumed by T06, T07, T08, T09, T17 and T18 — six dependents, third after
T01 and T04.

## The design decision this topic is built around

**The combinatorics is not in the operator-theory namespace, and does not import
a Hilbert space.**

`Analysis/Convex/Majorization.lean` — weak majorization and the
Hardy–Littlewood–Pólya transfer lemma, the engine underneath *every* unitarily
invariant norm inequality in this development — imports exactly:

```
Mathlib.Analysis.Convex.Basic
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.Order.Field.Basic
Mathlib.Data.Real.Basic
+ three tactic imports
```

No `InnerProductSpace`, no `HilbertBasis`, no `adjoint`. The only two textual
occurrences of `InnerProductSpace` in the file are prose, naming the two
consumers.

That is the claim worth checking in this topic, and it is cheap to check. A
majorization file that quietly depends on operator theory cannot be submitted to
`Mathlib.Analysis.Convex` — and majorization *belongs* in
`Mathlib.Analysis.Convex`, since it is a statement about real tuples. Keeping
the engine free of Hilbert spaces is what makes this topic contribute to two
different parts of the library rather than one.

**The upstream gap is precise and recorded in the source:** Mathlib has the
spectral theorem and Birkhoff's theorem, but **no majorization predicate and no
Schur–Horn theorem** — only a comment noting the absence. So neither half of
this topic is duplicating upstream work, and the combinatorial half is a
free-standing contribution.

`SchurHorn` also carries an attribution worth preserving: the proof strategy was
read from `rjwalters/lean-genius` (commit `3e09c97`, retrieved 2026-07-04, no
license declared upstream) and **independently re-derived** on this project's own
foundations. A reviewer should see that credit rather than discover the
resemblance.

## The pipeline

Each module consumes the previous one and adds exactly one idea:

| Module | Adds |
|---|---|
| `Analysis/Convex/Majorization` | Weak majorization `WeaklyMajorized`, prefix sums, and the T-transform (Robin Hood) transfer lemma. **Pure combinatorics.** |
| `SchurHorn` | The diagonal of a symmetric operator in *any* orthonormal basis is majorized by its eigenvalues, via the doubly-stochastic weight matrix `schurWeight` (`_nonneg`, `_row_sum`, `_col_sum`) and convexity. The first step from tuples to operators. |
| `KyFan` | `kyFanSum k A = ∑_{i<k} σᵢ(A)`, and the Ky Fan trace inequality: for symmetric `S` and an orthonormal family `w : Fin k → E`, `∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{i<k} λᵢ(S)`. |
| `UnitarilyInvariantNorm` | `diagOp b x` — the operator with real diagonal `x` in basis `b` — its algebra, its singular values, and the norms themselves. |
| `SingularSubspace` | Singular subspaces as spectral subspaces of the Gram operators `A⋆A`, `Â⋆Â`. |

The order matters and is not arbitrary: **Schur–Horn is what converts a
statement about an operator into a statement about a tuple**, at which point the
combinatorial engine applies. Ky Fan then packages the consequence in the form
the perturbation theory quotes, and `UnitarilyInvariantNorm` turns that into a
norm.

`diagOp` is the hinge in the other direction — it turns a tuple back into an
operator, which is how a majorization statement becomes a norm inequality.

## `SingularSubspace` is here for T18, and it shows

The other four modules form the majorization pipeline. `SingularSubspace` does
not: it defines singular subspaces as the spectral subspaces of the Gram
operators, and exists because **the Yu–Wang–Samworth singular-vector bound (T18)
applies the symmetric perturbation result to `A⋆A`**, and therefore needs the
Gram perturbation `Â⋆Â − A⋆A` bounded in terms of `Â − A`.

That is a real dependency and the module is in the right topic — the Gram bound
is a majorization-adjacent fact — but a reviewer should know it is there for one
downstream consumer rather than for the pipeline. If T18 were dropped, this
module would have no user.

## What a reviewer should check

1. **That `Majorization` imports no operator theory.** This is the topic's
   architectural claim and it is a one-command check. If it fails, the file
   cannot go to `Mathlib.Analysis.Convex` and the topic loses half its value.

2. **That Schur–Horn is stated for *any* orthonormal basis**, not for the
   eigenbasis. The theorem is vacuous in the eigenbasis, where the diagonal *is*
   the eigenvalue tuple. The mechanism is `schurWeight`, the doubly-stochastic
   matrix `|⟪vᵢ, eⱼ⟫|²`, whose row and column sums are proved to be one — that
   pair of lemmas is the whole content of "doubly stochastic" and is what
   convexity is then applied to.

3. **That the Ky Fan trace inequality is stated for an orthonormal family
   `Fin k → E`**, not for a subspace or a projection — the family form is what
   makes it usable in the perturbation arguments, which build the family from
   singular vectors.

4. **That `SingularSubspace`'s presence is justified by T18**, per the section
   above.

## Prerequisites

T01 (spectral theorem, for the eigenbasis Schur–Horn needs), T02 (polar
decomposition, for the singular values Ky Fan sums), T04 (spectral subspaces,
for `SingularSubspace`).

Note that `Analysis/Convex/Majorization` itself depends on **none** of these.
It could be submitted first, or independently of this topic altogether — which
is the practical payoff of the separation described above.
