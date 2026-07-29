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

   **What the Sylvester equation actually is.** I worked the identity out in
   full rather than guessing. Write `T' := X*X` on `E₀`, `T'' := XX*` on `E₁`,
   `R := (I-T')⁻¹`, `R'' := (I-T'')⁻¹`, `K := B₀₁X`, `tan2Θ = 2XR`. Two facts:

   * `X` intertwines: `XT' = T''X`, hence `XR = R''X`.
   * The commutator is bounded. Feeding `z := Xu` into the adjoint Riccati and
     then eliminating `A₁(Xu)` with the Riccati gives, on `dom A₀`,

     ```
     A₀T' - T'A₀  =  G  :=  (I + T')K - K*(I + T')          (K* = X*B₁₀)
     ```

   Then for `u ∈ dom A₀`, using the Riccati at the vector `Ru` and
   `A₀R - RA₀ = RGR`:

   ```
   A₁(tan2Θ · u) - tan2Θ · (A₀ u)  =  2[ XRG + XK - B₁₀ ] R u
   ```

   so `tan2Θ` **does** satisfy `SylvesterEquation A₁ A₀ tan2Θ C` with the
   explicit **bounded** right-hand side `C = 2(XRG + XK - B₁₀)R`. Collapsing it
   (`(I+T'')R'' + I = 2R''`) gives the clean form

   ```
   C  =  -2B₁₀ + 2 R'' D R,      D := 2XB₀₁X - XX*B₁₀ - B₁₀X*X
                                    =  -(XS + S''X),
       S  := X*B₁₀ - B₀₁X   (anti-self-adjoint on E₀)
       S'' := B₁₀X* - XB₀₁  (anti-self-adjoint on E₁)
   ```

   `D = 0` exactly in the commuting/scalar case, which is why `C = -2B₁₀` looks
   plausible. **`D ≠ 0` in general**: with `X = diag(x₁,x₂)` and `B₀₁ = e₁₂`,
   `D₁₂ = 2x₁x₂` and `D₂₁ = -(x₁² + x₂²)`.

   **Consequence — this route is sound but lossy.** `MapsDomainTo A₁ A₀ tan2Θ`
   holds (`T'` preserves `dom A₀`, and `A₀(T')ⁿ = (T')ⁿA₀ + O(n‖X‖^{2(n-1)})`
   from the commutator, so the Neumann series for `R` converges in the graph
   norm and `R` preserves `dom A₀`). So
   `kyFan_unbounded_sylvester_le_of_semibounded_direct` applies verbatim and
   yields

   ```
   d · kyFan_k(tan2Θ)  ≤  kyFan_k(C)  ≤  2·kyFan_k(B₀₁) + 2·kyFan_k(R''DR)
   ```

   This is a genuine, fully unbounded, arbitrary-ideal theorem with an explicit
   defect, and it is strictly better than the cosine-denominator surrogate in
   `DavisKahan/TanTwoTheta/UnboundedIdeal.lean`. It is **not** the sharp
   theorem: sharpness needs `kyFan_k(C) ≤ 2 kyFan_k(B₀₁)`, and `D ≠ 0` blocks
   that. Rotating the blocks does not rescue it either — in the scalar case
   `Ã₀ = A₀ + B₀₁X`, `Ã₁ = A₁ - B₁₀X*` give
   `Ã₁·tan2Θ - tan2Θ·Ã₀ = -2b(1+x²)/(1-x²)` and the mixed pairs give
   `-2b/(1-x²)`, none of which is `-2b`. Only the **original** `A₀, A₁` give the
   sharp right-hand side, and only when `D = 0`.

   Recommendation: land the Sylvester equation and the defect-form estimate as
   real theorems (they are provable now and reusable), and treat
   `kyFan_k(R''DR) = 0`-or-absorbable as the remaining sharpness question.

## The seam collapses to a single scalar inequality

This is the most useful thing I found. The four graph-norm clauses are an
artefact of insisting that the selected scalar be `aᵢ(X)`. Take instead

```
xᵢ ∈ dom A₀ orthonormal,   sᵢ := ‖X xᵢ‖,   yᵢ := X xᵢ / sᵢ
```

Then `yᵢ ∈ dom A₁` automatically (domain preservation), and

* `e0ᵢ = X xᵢ - sᵢ yᵢ = 0` **exactly** — both `‖e0ᵢ‖ ≤ ε` and `‖A₁ e0ᵢ‖ ≤ ε`
  hold trivially, and the whole `A₁` side of the seam disappears;
* `e1ᵢ = X* yᵢ - sᵢ xᵢ = (T' - sᵢ²) xᵢ / sᵢ`, and note `sᵢ² = ⟪T'xᵢ, xᵢ⟫`, so
  `e1ᵢ ⊥ xᵢ`.

Replacing `aᵢ` by `sᵢ` costs only a **bounded-norm** bookkeeping step, because
`t ↦ 2t/(1-t²)` is Lipschitz on `[0,r]` for `r < 1` — the same estimate
`sum_doubleAngleTangent_le_selected_add_tail` already performs.

In fact the defect vector drops out too. The only place the `A₀` side is used
is `hA0upper : Re ⟪X(A₀x), y⟫ ≤ ε`, and with `y = X x / s` that is literally

```
Re ⟪X(A₀x), y⟫  =  Re ⟪A₀x, X*y⟫  =  Re ⟪A₀ x, X*X x⟫ / s .
```

So **the entire unbounded seam is this one statement**:

> For every `ε > 0` and `k`, there are orthonormal `x₁,…,x_m ∈ dom A₀`
> (`m ≤ k`) whose values `sᵢ := ‖X xᵢ‖` track the leading approximation
> numbers `aᵢ(X)` to within `ε`, and which satisfy
> ```
> Re ⟪A₀ xᵢ , X*X xᵢ⟫  ≤  sᵢ · ε .
> ```

No graph norms, no defect vectors, no Gram--Schmidt, no `A₁` clause at all —
the `A₁` side is discharged exactly by `yᵢ := X xᵢ / sᵢ`, and the `sᵢ`-versus-`aᵢ`
slack is bounded-norm bookkeeping because `t ↦ 2t/(1-t²)` is Lipschitz on
`[0,r]`.

Two remarks on that inequality:

* It says `A₀` and `X*X` **approximately commute in the selected directions**.
  If they commuted exactly it is free: `Re⟪A₀x, Tx⟫ = ⟪TA₀x, x⟫ ≤ 0` because a
  product of commuting `≤ 0` and `≥ 0` operators is `≤ 0`.
* It is *not* free in general. The relevant object is the symmetrised product
  `W := (A₀T + TA₀)/2`, and the requirement is `⟪Wxᵢ, xᵢ⟫ ≤ sᵢε`. `W ≰ 0` in
  general — already for `A₀ = -P`, `T = Q` with `P, Q` non-commuting
  projections, `PQ + QP` has a negative eigenvalue and `W` a positive one. So
  the whole content is the *choice* of `xᵢ`, and the commutator identity
  `A₀T - TA₀ = G` gives no help: pairing it with `x` only reproduces
  `Re⟪x, Gx⟫ = 0`, which is automatic.

This is what I would rewrite `UnboundedApproximateLeadingSingularFamily` around.
It is a far better target than the twenty-field structure now in the file, and
it is small enough to attack a counterexample against if it is false.

## The mechanism that makes it work — and the one gap left

Work from the exact Riccati pairing rather than from defect vectors. For unit
`x ∈ dom A₀`, pairing `A₁(Xx) = X(A₀x) + X B₀₁ Xx - B₁₀x` with `Xx` and taking
real parts gives, with `T := X*X` and `s := ‖Xx‖`:

```
d s²  ≤  Re⟪A₀x, Tx⟫ + Re⟪B₀₁(Xx), Tx⟫ - Re⟪B₀₁(Xx), x⟫          (★)
```

If `Tx = s²x` **exactly**, (★) collapses to `d·2s/(1-s²) ≤ 2(-Re⟪x, B₀₁y⟫)`
with `y = Xx/s` — the sharp estimate, **with no error term at all**. So the
entire problem is how far `x` is from being an exact eigenvector of `T`, in two
separate senses:

* the `B₀₁` terms need `‖(T - s²)x‖ ≤ β` — costs only `‖B₀₁‖·β`, harmless;
* the `A₀` term needs `Re⟪A₀x, (T - s²)x⟫` small — this is the whole difficulty,
  because the naive bound is `‖A₀x‖·β` and `‖A₀x‖` is unbounded.

**The mechanism.** Let `P := E_T(J)` be the spectral projection of `T` for a
band `J` of half-width `β` and let `Ã` be the compression of `A₀` to `Ran P`.
Because `P` commutes with `T`, the vector `(T - s²)x` stays in `Ran P` for
`x ∈ Ran P`, so the component of `A₀x` orthogonal to `Ran P` drops out:

```
Re⟪A₀x, (T - s²)x⟫  =  Re⟪Ãx, (T - s²)x⟫          (x ∈ Ran P)
```

Now take `x` an **approximate eigenvector of `Ã`**, `‖Ãx - μx‖ ≤ ν`, and choose
`s² := ⟪Tx, x⟫`. Then `⟪x, (T - s²)x⟫ = 0` identically, so

```
Re⟪A₀x, (T - s²)x⟫  =  μ·0 + O(ν·β)  =  O(ν·β).
```

**This breaks the circularity.** Choose the band `J` (hence `β`) first, from
`‖B₀₁‖` and the target error; *then* choose `ν ≤ ε/β`, which is free because a
self-adjoint operator has approximate eigenvectors at every spectral value.
Nothing depends on `‖A₀x‖` at all. Disjoint bands give orthogonality for free —
exactly what `gramBands_disjoint` and `GramSpectralBandModel` already do here —
and multiplicity inside a band is handled by taking orthonormal approximate
eigenvectors of `Ã` restricted to that band.

**The remaining gap.** The argument needs `Ran P ∩ dom A₀` to be dense in
`Ran P`, so that `Ã` is a densely defined symmetric operator there and its
approximate eigenvectors lie in `dom A₀`. That is *not* automatic: `dom A₀` is
dense in `E₀`, but a dense subspace need not meet a closed subspace densely, and
`E_T(J)` need not preserve `dom A₀` — the commutator `A₀T - TA₀ = G` is bounded
for the polynomial `T`, but sharp spectral projections are not polynomials.

Two ways to close it, in order of preference:

1. **Smooth band functions via the unitary group — the route I recommend.**
   Replace the sharp `E_T(J)` by `φ(T)` for a smooth bump `φ` supported in `J`.
   The usual justification is a Helffer--Sjöstrand commutator expansion, which
   the pinned Mathlib does not have. **But `T = X*X` is bounded**, and that
   makes the Fourier route sufficient and far more formalizable:

   ```
   ‖[A₀, e^{itT}]‖ ≤ |t|·‖G‖          (Duhamel:
       [A₀, e^{itT}] = ∫₀ᵗ e^{isT} [A₀, iT] e^{i(t-s)T} ds)

   φ(T) = (2π)^{-1/2} ∫ φ̂(t) e^{itT} dt

   ⟹  φ(T) preserves dom A₀,  and  ‖[A₀, φ(T)]‖ ≤ ‖G‖ ∫ |t| |φ̂(t)| dt < ∞
   ```

   Every ingredient is elementary for a bounded self-adjoint `T`: `e^{itT}` is
   an honest exponential series, Duhamel is an integration by parts, and the
   only analytic input is Fourier inversion against a Schwartz bump. **The repo
   already builds this object** — `gramUnitaryGroup X` in
   `FinishTanTwoTheta/ApproximationNumber/`, with
   `gramUnitaryGroup_generator_apply` and `gramUnitaryGroup_generator_domain`
   already proved. Start there.

2. **Show `E_T(J)` preserves `dom A₀` directly.** Cheaper if it works. The
   resolvent does: for `|z| > ‖T‖` the Neumann series gives
   `‖A₀Tⁿx‖ ≤ ‖T‖ⁿ‖A₀x‖ + n‖T‖ⁿ⁻¹‖G‖‖x‖`, which is summable against `z^{-n-1}`,
   and `A₀` is closed, so `(T-z)⁻¹` preserves `dom A₀`; extend by the resolvent
   identity. That upgrades to `E_T(J)` **only when the band endpoints lie in
   the resolvent set**, via a Riesz contour projection. Since we choose the
   bands, this is often arrangeable — but not always (`spec T` can contain an
   interval), so (1) is the route that always works.

I did **not** close this gap, so the seam is still open. But the shape of the
proof is now fixed, the circularity is gone, and the remaining obligation is a
standard operator-theory statement about one spectral projection rather than an
open question about the whole theorem.

## Ticket board

Ordered, each self-contained. T1.1 is the only one with no prerequisite and it
is the one to start on: nothing downstream can be stated without it.

**T1.1 — the adjoint Riccati equation. — MOSTLY DONE (2026-07-29).**
Landed in `DavisKahan/Riccati/UnboundedAdjointRiccati.lean`, axiom-clean:
`mem_unboundedBlockGraph_orthogonal_iff`, `PreservesAdjointRiccatiDomains`,
`unboundedBlockGraphOrthogonalDomainVector`, and
`adjoint_riccati_of_invariant_orthogonal`. **Still open:** deriving
`PreservesAdjointRiccatiDomains` itself from the projection-preserves-domain
half of `ReducesSubspace` — the projection onto the complement is
`P(a,b) = (-X†w, w)` with `w = (I + XX†)⁻¹(b - Xa)`, so domain preservation of
the projection gives `(I + XX†)⁻¹` preserving `dom A₁`, and `X†z = (I+T)X†w`
then needs `T` preserving `dom A₀`, which T1.2 supplies. Until that is closed,
it is an explicit hypothesis, not a `sorry`.

Original statement:
`ContractiveReducingGraphSelection.reduces` is
`ReducesSubspace (unboundedBlockOperatorCorePMap H) (unboundedBlockGraph X)`,
which by definition includes `InvariantSubspace _ (unboundedBlockGraph X)ᗮ`.
The orthogonal complement of the graph is `{(-X*z, z) : z ∈ E₁}`. Unfolding
invariance there gives, for `z ∈ dom A₁`:

```
X* z ∈ dom A₀     and     A₀(X* z) = B₀₁ z + X*(A₁ z) - X*(B₁₀ (X* z))
```

The forward direction already exists in the shape to copy —
`strongSolvesRiccati_iff_pointwise` in
`DavisKahan/Riccati/UnboundedReduction.lean` — so this is the same derivation
run against `ᗮ` instead of the graph. It belongs beside it, in
`DavisKahan/Riccati/`, not in this completion lane: it is a general fact about
reducing Riccati graphs and other consumers will want it.

**T1.2 — the bounded commutator. — DONE (2026-07-29).**
`riccatiGramCommutator`, `gram_mem_domain`, `gram_commutator_eq` and
`norm_riccatiGramCommutator_le` are proved and axiom-clean in the same file.
For `x ∈ dom A₀`, feeding `z := Xx` into T1.1 and eliminating `A₁(Xx)` with the
forward Riccati gives `T := X*X` preserving `dom A₀` and

```
A₀ T - T A₀ = G := (I + T)K - K*(I + T),   K := B₀₁X,  K* = X*B₁₀
‖G‖ ≤ 2(‖B₀₁‖ + ‖B₁₀‖) = 4‖B₀₁‖
```

**T1.3 — smooth band functions preserve `dom A₀`.** *Needs T1.2.*
Duhamel for the bounded self-adjoint `T`: `‖[A₀, e^{itT}]‖ ≤ |t|·‖G‖`, then
`φ(T) = (2π)^{-1/2}∫ φ̂(t)e^{itT}dt` for Schwartz `φ`. Build on
`gramUnitaryGroup X` and `gramUnitaryGroup_generator_{apply,domain}` in
`FinishTanTwoTheta/ApproximationNumber/GramBandPolar.lean`. This is the largest
ticket and the only one needing real analysis.

**T1.4 — band-compressed approximate eigenvectors.** *Needs T1.3.*
For a smooth band `φ` supported in `J`, the compression `Ã` of `A₀` to
`Ran φ(T)` is densely defined and symmetric; produce orthonormal
`x₁,…,x_m ∈ dom A₀` in the band with `‖Ãxᵢ - μᵢxᵢ‖ ≤ ν` for prescribed `ν`.
Disjoint bands give orthogonality across bands — reuse `gramBands_disjoint`.

**T1.5 — restate the selection structure and rewire.** *Needs T1.4.*
Replace `UnboundedApproximateLeadingSingularFamily` by the one-condition form
(`sᵢ := ‖Xxᵢ‖`, `yᵢ := Xxᵢ/sᵢ`, single inequality
`Re⟪A₀xᵢ, X*X xᵢ⟫ ≤ sᵢ·ε`), reprove
`unboundedStableSingularPair_doubleAngleTangent_le` against it — it gets
*shorter*, since the `A₁` side is now identically zero — and keep
`sharp_unbounded_doubleAngleTangentOperator_kyFan` and
`sharp_unbounded_standardSymmetricIdeal_scaled` verbatim.

**T1.6 — the `sᵢ` versus `aᵢ(X)` bookkeeping.** *Independent of T1.1–T1.4, can
be done in parallel.* `t ↦ 2t/(1-t²)` is Lipschitz on `[0,r]` for `r < 1`;
`sum_doubleAngleTangent_le_selected_add_tail` already performs the analogous
estimate and is the template.

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
