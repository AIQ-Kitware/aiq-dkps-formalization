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

`ofLp` — the operator with prescribed columns — **is landed** (`d692b939`).  Its
bound is Cauchy–Schwarz in the rescaled form `ab ≤ (s a² + b²/s)/2` at
`s = ‖f‖/‖x‖`, which avoids building the `ℓ²` inner product of the two norm
families and so avoids the `lp`-inner plumbing entirely.

In flight: the round trips (`ofLp ∘ columns = id` and back), which is all that
is left of D1.

## What you can expect from me, in order

1. **The `HS ≃ lp` bijection** — both maps now exist; only the round trips
   remain.  After this, `HS(F, E)` is a Hilbert space in `ForTauCeti` with no
   tensor-product development anywhere, and **D3 unblocks**.
2. **The Sylvester operator on it and its spectral-gap inverse.**  This is where
   the sharp `δ⁻¹` lives and it is the only irreducible part of SR-D.
3. **The four consumer repoints** — `HilbertSchmidt{DefectFirst,Pairwise}`,
   `SylvesterHilbertSchmidt`, `HilbertSchmidtTensor`.
4. **S6**: drop `[[require]] Spectra` from `lakefile.toml`, confirm green, and
   relocate the DKPS-authored `vendor/` files that have an API home.

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

### D1 — the `HS ≃ lp` bijection  *(namek, in progress — do not take)*

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
