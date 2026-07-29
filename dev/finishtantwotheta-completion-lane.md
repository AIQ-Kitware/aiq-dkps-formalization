# FinishTanTwoTheta completion lane (T1/T2/T3)

Owner: `jon (toothbrush)`. Inherited 2026-07-28 from the stopped `jon (yardrat)`
agent. Read this before reclaiming any part of the lane.

## State

`lake build FinishTanTwoTheta` fails at exactly **one** declaration:

```
FinishTanTwoTheta/FinishTanTwoTheta/DavisKahan/Unbounded.lean
  exists_unboundedApproximateLeadingSingularFamily
```

Everything else in the library compiles. The fifteen failures the lane started
with were fourteen tactic/coercion repairs plus this one; the fourteen are
fixed and merged against jon (namek)'s `LinearPMap` retyping of the same file.

**This declaration was never proved.** Its proof body ends in `aesop`, preceded
by a comment block naming the inputs a proof would use. `aesop` does not
discharge the goal and never did. It is not a compile-repair item: it is
`PROOF_OBLIGATIONS.md` #5, the one genuinely new unbounded seam the library was
created to close.

## What the statement demands

For every `k` and every `ε > 0`, orthonormal families
`xᵢ ∈ dom A₀`, `yᵢ ∈ dom A₁` (`i < count ≤ k`) with `aᵢ := aᵢ(X) > ε`, such
that both singular defects are small **in the graph norms**:

```
e0ᵢ := X xᵢ - aᵢ yᵢ ∈ dom A₁   with  ‖e0ᵢ‖ ≤ ε  and  ‖A₁ e0ᵢ‖ ≤ ε
e1ᵢ := X* yᵢ - aᵢ xᵢ ∈ dom A₀   with  ‖e1ᵢ‖ ≤ ε  and  ‖A₀ e1ᵢ‖ ≤ ε
```

## Why the sketched proof cannot work

The docstring proposes: take the bounded spectral-band family from
`SpectralSelection`, use density of `dom A₀` / `dom A₁`, and apply a finite
Gram--Schmidt correction.

Density gives approximation in `‖·‖` only. It gives no control whatsoever on
`‖A₀ ·‖` or `‖A₁ ·‖` of the approximants — that is precisely the content of
`dom A₀` not being closed. Gram--Schmidt corrections are norm corrections and
are equally silent about graph norms. So the sketch cannot produce the two
`_apply_norm` fields, and no amount of tactic work on it will.

## The actual obstruction

Write `T := X*X` and drop the index. The two defect equations eliminate `y`:

```
a·e1 = X*(X x - e0) - a² x = (T - a²) x - X* e0
  ⟹  (T - a²) x = a·e1 + X* e0,     so  ‖(T - a²) x‖ = O(ε).
```

So `x` is forced to be an approximate eigenvector of `T` at `a²` — expected,
and consistent.

Now apply `A₀`. Two Riccati identities are available:

* **Riccati** (`S.strongSolvesRiccati`), for `x ∈ dom A₀`:
  `A₁(X x) = X(A₀ x) + X B₀₁ X x - B₁₀ x`.
* **Adjoint Riccati** (from `S.reduces`: the orthogonal complement of the graph
  is `{(-X* z, z)}` and is invariant), for `z ∈ dom A₁`:
  `A₀(X* z) = B₀₁ z + X* A₁ z - X* B₁₀ X* z`.

Composing them gives the commutator identity on `dom A₀`:

```
A₀ T - T A₀ = G,        G := B₀₁X + X*X B₀₁X - X*B₁₀ - X*B₁₀X*X
```

with `G` **bounded**, `‖G‖ ≤ 2(‖B₀₁‖ + ‖B₁₀‖) = 4‖B₀₁‖`. Applying `A₀` to the
displayed elimination and using the adjoint Riccati on `X* e0` (which is where
`‖A₁ e0‖ ≤ ε` is consumed) yields

```
(T - a²)(A₀ x)  +  G x   =   a·A₀ e1 + A₀(X* e0),
‖A₀(X* e0)‖ ≤ (‖B₀₁‖ + 1 + ‖B₁₀‖)·ε
  ⟹  ‖(T - a²)(A₀ x) + G x‖  ≤  (a + 1 + ‖B₀₁‖ + ‖B₁₀‖)·ε  =  O(ε).
```

So the statement demands a unit `x ∈ dom A₀` that simultaneously

1. nearly lies in the kernel of `T - a²`, and
2. has `A₀ x` an approximate **solution** of `(T - a²) w = -G x`,

where `‖G x‖` is generically of order `‖B₀₁‖` — a fixed constant that does
**not** shrink with `ε`. Requirement 2 forces `‖A₀ x‖ ≳ ‖G x‖ / ‖(T - a²)‖`
restricted to the band `x` lives in, which blows up exactly as requirement 1 is
enforced. The two requirements pull against each other, and nothing in
`UnboundedBlockData` couples the spectral decomposition of `A₀` to that of
`X*X` strongly enough to reconcile them.

I did not produce a counterexample, so this is an obstruction, not a disproof.
But the statement should be treated as **unproved and plausibly false as
written**, not as a tactic problem.

Note the finite-dimensional case is not a counterexample and never will be:
there the singular values are attained, one takes exact singular vectors,
`e0 = e1 = 0`, and every clause holds trivially. The whole difficulty is the
standing guard "do not use exact singular-vector attainment for an arbitrary
bounded operator" — correctly imposed, since `aₙ(X)` need not be attained.

## The structure is over-specified

The two `_apply_norm` fields are strictly stronger than anything the consumer
uses. In `unboundedStableSingularPair_doubleAngleTangent_le`:

* `‖A₁ e0‖ ≤ ε` is used **only** to get `hA1err : |Re ⟪A₁ e0, y⟫| ≤ ε`;
* `‖A₀ e1‖ ≤ ε` is used **only** to get `hA0err : |Re ⟪A₀ x, e1⟫| ≤ ε`
  (via symmetry of `A₀`).

Replacing the two norm fields by exactly those two pairing bounds weakens the
selection theorem, leaves `sharp_unbounded_doubleAngleTangentOperator_kyFan`
and `sharp_unbounded_standardSymmetricIdeal_scaled` **verbatim unchanged**, and
keeps the `PROOF_OBLIGATIONS` guard "no factors `‖A₀‖` or `‖A₁‖`" satisfied.

This is worth doing regardless. It does not by itself close the seam: the
pairing form still needs `‖A₀ x‖ · ‖(T - a²) x‖ = O(ε)`, i.e. a band width
chosen *after* the vector it is supposed to contain. But it is the honest
statement of what the argument consumes, and it is a strictly larger target to
aim a real proof at.

## Options, in the order I would take them

1. **Weaken the structure to the pairing fields** (above). Mechanical, safe,
   strictly improves the target. Does not close the seam.
2. **Add the missing hypothesis and say so.** The natural one is that the
   spectral projections of `X*X` for the selected bands have nontrivial
   intersection with the low-energy spectral subspaces of `A₀` — i.e. a
   quantitative compatibility between `A₀` and `X*X`. This is a real theorem
   with a real hypothesis rather than a false theorem.
3. **Change route entirely.** Do not go through approximate singular vectors.
   The exact pairing computation, for `x ∈ dom A₀` and `y := X x / ‖X x‖`, is
   clean and needs no defects at all:
   pairing the Riccati identity with `X x` gives
   `d‖Xx‖² ≤ Re⟪A₀x, Tx⟫ + Re⟪B₀₁Xx, Tx⟫ - Re⟪B₀₁(Xx), x⟫`,
   and if `x` is an **exact** eigenvector of `T` this collapses to the sharp
   `d·tan2θ(s) ≤ 2(-Re⟪x, B₀₁ y⟫)` with **no error term**. The whole problem is
   concentrated in `Re⟪A₀x, (T - a²)x⟫ ≤ small`. A variational/compression
   argument that never names an individual approximate singular vector may
   avoid the obstruction; a finite-dimensional compression of the Ky Fan sum is
   the obvious thing to try.
4. **The unbounded Sylvester route — promising, but not the naive form.**
   The repository already carries the machinery that produces *exactly* the
   sharp shape, proved by bounded spectral truncations rather than approximate
   singular vectors (so the obstruction above does not apply to it):

   ```
   DavisKahan/Sylvester/Unbounded/OrderedCutoff.lean
     kyFan_unbounded_sylvester_le_of_semibounded_direct
       (hAc : SemiboundedBelow A (c + δ)) (hBc : SemiboundedAbove B c)
       (hEq : HasClosedSylvesterEquation A B X C) :
     ∀ k, δ * kyFanApproximationGauge k X ≤ kyFanApproximationGauge k C
   ```

   With `c = 0`, `δ = d`, `A = A₁`, `B = A₀`, `X = tan2Θ`, `C = -2B₁₀` this is
   verbatim `sharp_unbounded_doubleAngleTangentOperator_kyFan`. So the whole
   theorem would follow from one operator identity.

   **But that identity is false as stated.** I checked it. Writing
   `T := X*X`, `T' := XX*`, `R := (I-T)⁻¹`, `K := B₀₁X`, and using the Riccati
   equation plus the commutator `A₀T - TA₀ = (I+T)K - K*(I+T)`, the claim
   `A₁·(2XR) - (2XR)·A₀ = -2B₁₀` reduces after clearing `R` to

   ```
   2 X B₀₁ X  =  B₁₀ X*X + XX* B₁₀ .
   ```

   That holds in the commuting/scalar case (both sides agree, which is why it
   looks right), but it is false in general: take `E₀ = E₁ = ℂ²`,
   `X = diag(x₁,x₂)` with `x₁ ≠ x₂` and `B₀₁ = e₁₂`. The `(1,2)` entry of the
   left side is `2x₁x₂`; of the right side, `0`.

   So the Sylvester route needs the **rotated** (block-diagonalised) diagonal
   blocks, as in the classical Davis--Kahan tan 2Θ argument, not `A₀` and `A₁`
   themselves. Establishing that the rotated blocks inherit
   `SemiboundedAbove _ 0` / `SemiboundedBelow _ d` is then the real content, and
   it is the same content the bounded proof gets for free. This is the route I
   would bet on, and it reuses machinery that is already proved and green.

5. **Record it as an open obligation** with an explicit `sorry` so the library
   is green and the debt is visible and greppable. `PROOF_OBLIGATIONS.md`
   currently forbids `sorry` in this library; that guard was written on the
   assumption the seam was provable by the sketched route, which it is not.
   Changing the guard is jon's call, not mine.

## Do not

- Do not "fix" this by adding a structure field or a hypothesis to
  `unboundedStableSingularPair_doubleAngleTangent_le` that hides the seam.
- Do not reintroduce `‖A₀‖` / `‖A₁‖` factors — the diagonal blocks are
  unbounded and those norms do not exist.
- Do not weaken `sharp_unbounded_doubleAngleTangentOperator_kyFan` or
  `sharp_unbounded_standardSymmetricIdeal_scaled`. They are the public results
  and they are believed true.
