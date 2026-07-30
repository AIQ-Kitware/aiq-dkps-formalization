# Roadmap: angle geometry and eigenvalue perturbation

**Topic T08 of the candidate design.** Five modules. Depends on T01, T02, T04,
T05, T06, T07 — six prerequisites, the most of any topic except T16. Consumed by
T17 and T18.

## What this topic is

Two things that a reader might expect to be separate, and are here because they
are the same step of the Davis–Kahan argument:

* **the angle dictionary** — cosine, sine, angle, tangent and double-angle
  objects for a pair of subspaces, each with its singular-value and projector
  description (`AngleGeometry`, on `GramOperator` and `FrameFactorization`);
* **eigenvalue perturbation** — how far the spectrum moves when the operator
  does (`HoffmanWielandt`, `EigenvalueChange`).

Davis–Kahan bounds a *subspace* rotation by an operator perturbation. The first
half is how the rotation is measured; the second is what the perturbation is
allowed to do to the spectrum. T17 needs both in the same breath.

## This topic carries T06's well-namedness

`AngleGeometry` defines `principalCosines U V` for **submodules**, as the
singular values of `P_V P_U`, and proves:

```lean
theorem principalCosines_span_eq_cosPrincipalAngles {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    principalCosines (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) =
      cosPrincipalAngles hu hv
```

**This is the theorem that makes T06's central definition well-named**, and it
lives here rather than there. T06's `cosPrincipalAngles hu hv` is indexed by
orthonormal *families*; the name says "angles between subspaces"; and the fact
that those agree is the statement above.

T06 is meant to be submittable before T08, so a reviewer of T06 alone sees a
family invariant with an aspirational name. Whoever reviews or moves this
theorem should know it is doing double duty: it is the subspace/family bridge
for T08's own dictionary *and* the well-namedness of the topic upstream.

The T06 roadmap records the same fact from the other side.

## The estimate T17 consumes

```
∑ᵢ(λ'ᵢ − λᵢ)² ≥ ‖𝒞H‖²_F − ‖𝒞⊥H‖²_F
```

for self-adjoint `T`, `S` with `H = S − T`, where `𝒞H` is the diagonal part of
`H` in `T`'s eigenbasis and `𝒞⊥H` the off-diagonal part, under a `γ`-separated
spectrum for `S` and `‖𝒞H‖_F ≤ γ/√2`.

**The proof route is the design decision.** Davis argues in the real Hilbert
space of Hermitian matrices; since every matrix involved is diagonal in `T`'s
eigenbasis, the argument reduces to `EuclideanSpace ℝ (Fin n)` and a point in
the convex hull of a permutation orbit — and the convex-hull membership is
discharged from **Birkhoff's theorem**.

Note what that avoids: *"no vector-majorization API is needed."* T05 supplies a
majorization engine and this module deliberately does not use it, because
Birkhoff is already in Mathlib and the permutation-orbit hull is exactly what
Birkhoff gives. A reviewer might reasonably expect T05 to be the tool here; it
is not, and that is a choice rather than an oversight.

`HoffmanWielandt` goes the other way and factors through the **von Neumann trace
inequality**, whose sorted core is the rearrangement inequality — recorded in
that module rather than assumed.

## The modules

| Module | Role |
|---|---|
| `GramOperator` | `A⋆A` on `E` and `AA⋆` on `F`: symmetric, positive semidefinite, eigenvalues the squared singular values. The carrier of the angle theory. |
| `AngleGeometry` | The cosine/sine/angle/tangent/double-angle dictionary for a subspace pair, with singular-value and projector descriptions — and the T06 bridge above. |
| `FrameFactorization` | Isometric range factorization of an injective trial map. **Independent of Davis–Kahan spectral-gap assumptions**, and says so. |
| `HoffmanWielandt` | `ℓ²` distance between sorted spectra bounded by the Frobenius norm of the difference, via von Neumann. |
| `EigenvalueChange` | The displacement estimate above, via Birkhoff. |

`FrameFactorization` being gap-free is the same kind of deliberate boundary as
`ReducingSubspace` in T04: it means the factorization can be read and reviewed
without any perturbation theory, and reused by anything that needs a trial map
factored.

## What a reviewer should check

1. **That `EigenvalueChange` really uses Birkhoff and not a majorization API** —
   it is the cheaper route and the module claims it; if a majorization import
   crept in, the claim is stale.
2. **That `HoffmanWielandt`'s rearrangement core is proved here**, not cited —
   it is the sorted heart of von Neumann's inequality.
3. **That `FrameFactorization` has no spectral-gap hypothesis anywhere.**
4. **That the angle dictionary agrees with T06** — the bridge theorem above is
   the only thing tying two independently-stated notions together.

Checks 1–3 hold as of 2026-07-30. `EigenvalueChange` has **zero** references to
`Majorization` and imports `Mathlib.Analysis.Convex.Birkhoff` directly, with
`diag_mem_convexHull_perm_spectrum` as the bridge. `HoffmanWielandt` proves the
rearrangement inequality itself, as
`sum_mul_comp_perm_le_sum_mul_of_antitone`. And `FrameFactorization`'s only
occurrence of the word "gap" is the docstring line asserting independence — there
is no spectral-gap hypothesis in the file.

## Prerequisites

T01, T02, T04, T05, T06, T07. The count is high because the topic sits where the
geometry and the norms meet: it needs the angles (T06), the norms they are
measured in (T05, T07), the projections they are stated with (T04), and the
polar/positive machinery underneath (T01, T02).
