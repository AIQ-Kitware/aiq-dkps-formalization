# namek status — Spectra removal, serial phase

**Updated 2026-07-29.  Read this before touching anything Spectra-facing.**

## Where the campaign is

`import Spectra` outside `vendor/` and `external/`: **26 → 7**, of which **5 are
real work** and both others are deliberate:

| file | status |
|---|---|
| `Interop/Spectra/HilbertSchmidt{Tensor,ColumnExpansion}.lean` | SR-D — **mine, in progress** |
| `Sources/DavisKahan1970/Sylvester/HilbertSchmidt{DefectFirst,Pairwise}.lean` | SR-D — mine, in progress |
| `Sources/DavisKahan1970/Audits/SylvesterHilbertSchmidt.lean` | SR-D — mine, in progress |
| `scripts/ExportSpectraDeclClosure.lean` | **not a defect** — it is the tool that measures the surface, so it is *supposed* to import Spectra |
| `FinishTanTwoTheta/…/GroundedImports.lean` | **out of scope** — jon, 2026-07-29: "leave FinishTanTwoTheta alone, we will fix that later" |

**Lanes SR-A, SR-B, SR-C, SR-E and SR-F are closed.**  Convergence Wave 3 is
closed too.  Everything is on `origin/namek-work` and merged to `main`.

## What S6 now requires — this changed twice, read it

jon, 2026-07-29:

1. **`vendor/Spectra` is not deleted.**  The requirement is that *nothing
   depends on it*.
2. **It is moved to a `retired/` folder**, not removed — *"that will prevent
   other agents from reusing it"*, which is exactly the point.  Retiring stops
   new dependencies forming while keeping every line available for reference and
   for the ports still to come.

So S6 is now: drop the `[[require]] Spectra` block from `lakefile.toml`, confirm
green, move the vendored tree to `retired/`, and relocate to `ForTauCeti` the
DKPS-authored files that have an API home there.

**The old hazard is gone.**  Deleting `vendor/` would have destroyed the 2,589
lines of our own mathematics still sitting in it; retiring destroys nothing.  Do
not plan around deleting the directory, and do not treat "retired" as a synonym
for "deleted" — the distinction is the whole reason for the move.

Provenance was also scoped down: **authorship pointer plus divergence notes**,
not the nine-field schema.  The record for all six lanes is in
[`spectra-to-tauceti-port-ledger.md`](spectra-to-tauceti-port-ledger.md) under
"Authorship record for the 2026-07-29 lanes".

## What I am working on right now

**SR-D, and it is smaller than it was measured to be.**  edward sized the donor
closure at 21,581 lines because Spectra builds the Hilbert tensor product by
hand.  It does not have to be built: the column map `T ↦ (T eᵢ)` identifies
`HS(F, E)` with `lp (fun _ => E) 2`, and Mathlib already carries the inner
product (`lp.instInnerProductSpace`) and completeness.  Landed so far in
`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtLp.lean`:

* `memLp_columns_iff` — Hilbert–Schmidt membership *is* `ℓ²` membership of the columns;
* `summable_norm_columnSeries` — the column series of an `ℓ²` family converges absolutely.

**D1 is finished.**  `ofLp`'s bound is Cauchy–Schwarz in the rescaled form
`ab ≤ (s a² + b²/s)/2` at `s = ‖f‖/‖x‖`, which avoids building the `ℓ²` inner
product of the two norm families and so avoids the `lp`-inner plumbing entirely.
The round trips are continuity plus the basis expansion one way, and
orthonormality (`b.repr (b i)` is a single) the other.

**I am now on D3 unless someone claims it first** — say so in `LANES.md` and I
will hand over rather than duplicate.

## What you can expect from me, in order

1. ~~The `HS ≃ lp` bijection~~ — **done**, `8c5539d6`.
2. **The Sylvester operator on it and its spectral-gap inverse.**  This is where
   the sharp `δ⁻¹` lives and it is the only irreducible part of SR-D.
3. **The four consumer repoints** — `HilbertSchmidt{DefectFirst,Pairwise}`,
   `SylvesterHilbertSchmidt`, `HilbertSchmidtTensor`.
4. **S6**: drop `[[require]] Spectra` from `lakefile.toml`, confirm green, and
   relocate the DKPS-authored `vendor/` files that have an API home.

## D3's crux, measured — and the two routes compose

**The remaining obstacle in D3 is self-adjointness of the Sylvester operator**
`𝒮 : Z ↦ A Z - Z B` on `HS(F, E)`.  Everything downstream needs it, because
`spectralPVM` and therefore `gapInverse` are stated for self-adjoint operators.

Spectra gets it from Stone: `𝒮` is the generator of the unitary group
`W t Z = U_A t ∘ Z ∘ (U_B t)⋆`, and generators of one-parameter unitary groups
are self-adjoint.  **The tree does not have that direction.**  `genToGroup` is
the converse (self-adjoint → group), and searching `ForTauCeti` for
`IsSelfAdjoint (generator …)` returns nothing.  Proving it would need the
Hille–Yosida resolvent integral `R(∓i) = ∓i ∫₀^∞ e^{∓t} U(t) dt`.

**That is avoidable, and the way round is the pleasing part.**  What the tree
*does* have is von Neumann's criterion,
`OneParameterUnitaryGroup.isSelfAdjoint_of_surjective_addSub`: a symmetric
operator whose `A + i` and `A - i` are both surjective is self-adjoint.  So `𝒮`
is self-adjoint as soon as `𝒮 ± i` are surjective — and **surjectivity is exactly
what the Fourier/semigroup formula already in the tree provides**
(`Experimental/…/Sylvester/FourierSemigroup.lean`):
`X = ∫ μ_δ(t) U(-t) C V(t) dt` solves `A X - X B = C` whenever the two spectra
are separated, and for `𝒮 ± i` they are separated by `1` in the imaginary
direction for free.

**The constant does not matter there.**  The Fourier route was ruled out for the
*theorem* because it yields `π/(2δ)` instead of the sharp `δ⁻¹` — but
surjectivity is a existence statement and is indifferent to constants.  So:

* **Fourier** ⟹ `𝒮 ± i` surjective ⟹ `𝒮` self-adjoint (von Neumann);
* **spectral** ⟹ the sharp `δ⁻¹` (`apply_gapInverse`, landed).

The two routes compose, each used for the thing it is actually good at, and
Stone's forward direction is not needed anywhere.

**Remaining concrete steps in D3:**

1. `𝒮` as a `LinearPMap` on `lp (fun _ : ι => E) 2` via D1's bijection — no new
   type is needed, since `lp` already carries the inner product and
   completeness;
2. symmetry of `𝒮` (a two-line computation from self-adjointness of `A` and `B`);
3. surjectivity of `𝒮 ± i` from the Fourier formula;
4. self-adjointness by `isSelfAdjoint_of_surjective_addSub`;
5. the vector gap from the pairwise spectral gap, then `apply_gapInverse`.

## Two things worth taking from the closed lanes

**The bypass keeps working, and three times the advertised blocker did not
exist.**  SR-C needed no second moment (the consumer wanted a *form* bound, and
the bounded form bound was already in the tree).  SR-F's polar work already
existed in `ForTauCeti`.  SR-E needed no Borel functional calculus at all.
Before porting a donor theorem, ask what the consumer actually consumes.

**For fable specifically** — your analysis ruling out the CFC shortcut for SR-E
was correct in every particular, and the conclusion was one step short: the
obstruction is the single point `1`, and `{1}` is null for every diagonal
measure, so a damped *sequence* of continuous symbols does what no single one
can.  Rosenblum is proved on that route, built on your
`cfcHom_cayley_intertwines`.  The generalisable form is: *a Borel step that
exists only to reach one null point can be replaced by a damped sequence.*

## SR-D is now SPLIT — three pieces are open, take them

I claimed the whole remainder as one serial lane when the other Spectra lanes
had been dropped.  That is no longer the situation and holding it serially is
blocking people.  **Only D1 is mine.**  The other three are specified below and
are free; claim in `dev/LANES.md` before the first edit.

### D1 — the `HS ≃ lp` bijection  *(**DONE** — namek, `8c5539d6`)*

**D3 is unblocked as of now.**  `HS(F, E)` has a Hilbert-space home built from
Mathlib's `lp`, with no tensor-product development anywhere in the route.
Importable API in `ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtLp.lean`:

| declaration | content |
|---|---|
| `columns b T` | the column family `i ↦ T (b i)` |
| `memLp_columns_iff` | Hilbert–Schmidt membership **is** `ℓ²` membership of the columns |
| `ofLp b f` | the bounded operator with prescribed columns, `‖ofLp b f‖ ≤ ‖f‖` |
| `ofLp_columns`, `columns_ofLp` | the two round trips — so this is a bijection, not an embedding |
| `summable_sq`, `tsum_sq_eq_norm_sq` | the two `lp`-norm facts everything above will use |

Whoever takes D3 needs nothing further from me.


`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtLp.lean`.  Landed:
`memLp_columns_iff`, `summable_norm_columnSeries`, `summable_sq`,
`tsum_sq_eq_norm_sq`.  In flight: `ofLp` and the round trips.

### D2 — `HilbertSchmidtColumnExpansion`  *(OPEN, but **I mis-specified it — read this**)*

**Correction, same day.**  I released D2 as "independent of D1, needs only
`columns` and `memLp_columns_iff`, a re-base rather than a port".  **That is
wrong and I checked it after publishing.**  The eleven declarations are stated
about the tensor model itself — `columnTensor b z i`, `HilbertTensor.mapL`,
`HilbertTensor.{norm_tmul, norm_mapL, inner_tmul_tmul}` — and about the
antilinear conjugate space `Conj.map`, which edward measured as **not
dissolvable** against Mathlib.  So this is a *restatement*, not a substitution,
and it is not independent of anything: it is the tensor model's own column
theory.

What that means for the lane:

* under the `lp` route the *content* of these declarations — the column
  expansion of a Hilbert–Schmidt operator — is what `HilbertSchmidtLp.lean`
  supplies natively, so they are **superseded**, not re-based;
* but edward measured them as externally unused and **deliberately retained for
  upstreaming**, so deleting them silently is the wrong call;
* and per jon the file must stop *depending* on `vendor/Spectra`, so leaving
  them as they are is not an option either.

**So D2 is a judgement call, not a mechanical job**, and it needs whoever takes
it to decide between restating the eleven over `lp` (real work, and the honest
preservation of the intent) and retiring them with a note pointing at the `lp`
equivalents.  My view is the second, because the `lp` statements *are* the same
mathematics in the representation Tau Ceti will actually take — but it is
edward's retention call to overturn, not mine, so ask them.

Estimated properly: **not** the free lane I advertised.

### D3 — the Sylvester operator on `HS` and its spectral-gap inverse  *(OPEN once D1 lands)*

The only irreducible part of SR-D, and where the sharp `δ⁻¹` lives.  Statement
wanted, over `HS(F, E)` once D1 makes it a Hilbert space:

* the Sylvester group `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` is a one-parameter unitary
  group on `HS`, generated by `Z ↦ i (A Z - Z B)`;
* across a spectral gap `δ` its generator is invertible with
  `‖𝒮⁻¹‖ ≤ δ⁻¹`.

**Do not try to get this from the Fourier/semigroup formula.**  That route is
already in the tree (`Experimental/…/Sylvester/FourierSemigroup.lean`) and gives
`π/(2δ)`, not `δ⁻¹` — the exact `L¹` mass of the Haagerup–Zsidó kernel.  The
removal plan already records that an `L¹` mass of `1/δ` would assert a false
estimate.  The gap inverse is genuine content.

### D4 — the consumer repoints  *(OPEN once D3 lands)*

`Sources/DavisKahan1970/Sylvester/HilbertSchmidt{DefectFirst,Pairwise}.lean`,
`Sources/DavisKahan1970/Audits/SylvesterHilbertSchmidt.lean`,
`Interop/Spectra/HilbertSchmidtTensor.lean`.  Mechanical once D3 exists —
`paperHilbertSchmidt_sylvester_defectFirst` is the only real consumer and its
proof is 40 lines.

**D3 is the clean parallel lane**, not D2 — it is blocked only on D1's API, and
I will say here the moment that is importable.  D2 needs a decision from edward
first.

---

## Update 2026-07-29 — D3's crux is closed: Stone's theorem, forward direction

`ForTauCeti/Analysis/InnerProductSpace/OneParameterUnitaryGroup/Stone.lean`
(new, 11 declarations, tree green at 9277 jobs, axioms `propext` /
`Classical.choice` / `Quot.sound` only).

**`isSelfAdjoint_generator : IsSelfAdjoint (generator U)`** — the generator of a
one-parameter unitary group is self-adjoint.

Why this was the crux: everything spectral in the tree — `spectralPVM`, the
Borel calculus, `apply_gapInverse` — is built from a *self-adjoint*
`LinearPMap`, and nothing could produce one from a group.  Symmetry
(`generator_isFormalAdjoint`) was already there and is a different statement.
The earlier measurement recorded here said the tree lacked Stone's forward
direction and that von Neumann's criterion was the way around it.  That was
right; what the measurement missed is how little the criterion actually costs.

### Two things other agents should take from this, independent of SR-D

1. **Density is free.**  A symmetric `A` with `A + i` surjective has dense
   domain: for `x ⊥ Dom A`, pick `ψ` with `A ψ + i ψ = x`; then
   `0 = ⟪ψ, x⟫ = ⟪ψ, A ψ⟫ + i‖ψ‖²`, and symmetry makes the first term real, so
   the imaginary part is `‖ψ‖²` and `ψ = 0`, hence `x = 0`.
   **The Gårding/mollifier argument that normally carries half of Stone is not
   needed anywhere.**  If you are reaching for
   `isSelfAdjoint_of_surjective_addSub`, you no longer owe it a density proof —
   use `dense_domain_of_surjective_add_I`.
2. **`ℝ`-linearity of the upstream resolvent is not an obstacle.**  Tau Ceti's
   `StronglyContinuousSemigroup.resolvent` is only `ℝ`-linear, which looks
   fatal for a `ℂ`-scalar argument.  It is not: both surjectivity statements
   come out by **choosing the input vector** `∓i • φ`, never by moving a scalar
   through `R`.  Same trick should work for any other complex statement someone
   wants off that library.

The third supplied piece is the **converse of the Wave 3 generator bridge**: the
semigroup sees only `t → 0⁺`, so its domain is a priori larger than the group's.
For a unitary group it is not, because
`genDiffQuot U ψ (-t) = U (-t) (genDiffQuot U ψ t)` and `U (-t) → 1` strongly.
`SemigroupBridge.lean` named this as the deliberately-omitted direction when it
was written; it is now supplied, and `SemigroupBridge.lean` itself was not
touched.

### What is left in D3

The self-adjointness step is closed.  Remaining:

* the Sylvester group `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` as a
  `OneParameterUnitaryGroup` on `HS(F, E)` — note this needs **no tensor
  product**, only that conjugating by unitaries preserves the Hilbert–Schmidt
  norm, which `hilbertSchmidtEnergy_indep` already gives;
* identifying `-i · generator W` with `Z ↦ A Z - Z B`;
* then `apply_gapInverse` applies directly.

### The board warning was respected

`dev/LANES.md` item 1 says not to derive SR-D3 from the Fourier/semigroup route,
because it yields `π/(2δ)` rather than the sharp `δ⁻¹`.  That still stands.
Stone uses the semigroup route **only for surjectivity**, which is indifferent
to the constant — no bound in `Stone.lean` comes from an `L¹` mass, and the
sharp `δ⁻¹` still comes from `SpectralGapInverse.lean`.
