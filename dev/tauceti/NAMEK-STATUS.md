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

## What S6 now requires — this changed, and it is easier than the plan says

jon, 2026-07-29: **`vendor/Spectra` does not have to be deleted.**  The
requirement is that *nothing depends on it*.  Our own mathematics inside it
moves to `ForTauCeti` where there is an API home; where there is not, it may stay
in `vendor/` as inert provenance.

So the old worry — that deleting `vendor/` would destroy the 2,589 lines of
DKPS-authored mathematics still sitting there — is no longer a hazard.  Do not
plan around deleting the directory.

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

In flight: `ofLp`, the operator with prescribed columns, and the round trips.

## What you can expect from me, in order

1. **The `HS ≃ lp` bijection** — next.  After this, `HS(F, E)` is a Hilbert
   space in `ForTauCeti` with no tensor-product development anywhere.
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

## Do not take

SR-D, in any part.  It is one coherent piece and I am mid-way through it.
Everything else Spectra-facing is closed.
