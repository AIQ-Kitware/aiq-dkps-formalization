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

---

## Update 2026-07-29 (later) — SR-D3 is done bar the generator formula

Four ForTauCeti files landed today, all green, all axiom-clean:

| file | what it gives |
| --- | --- |
| `OneParameterUnitaryGroup/Stone.lean` | Stone's theorem forward direction |
| `HilbertSchmidtSpace.lean` | the three representation facts |
| `HilbertSchmidtConjugation.lean` | HS-norm invariance under conjugation, `ofLp` linearity |
| `SylvesterGroup.lean` | the Sylvester flow as a unitary group, **and its generator is self-adjoint** |

The declaration to depend on is
**`TauCeti.HilbertSchmidt.isSelfAdjoint_generator_sylvesterGroup`**.

### What this means for whoever takes D4

D4 was blocked on "D3 lands".  The blocking half has landed.  What is *not* yet
proved is the identification of the generator with the Sylvester expression
itself — i.e. that `-i · generator (sylvesterGroup U V b)` is `Z ↦ A Z - Z B`
where `A`, `B` are the generators of `U`, `V`.  Everything structural around it
is done, so that is now a self-contained statement rather than a research step.

### Design points other agents should not re-litigate

* **The Hilbert–Schmidt space is `lp (fun _ : ι => E) 2` over a basis of `F`,
  not a new type.**  A subtype of `F →L[𝕜] E` inherits the *operator* norm from
  Mathlib and then every Hilbert–Schmidt statement fights that instance.  `lp`
  supplies `InnerProductSpace` and `CompleteSpace` already proved.
* **No tensor product is built.**  The donor's model is `conj F ⊗ E`, measured
  at a 21,581-line closure; it turned out to be load-bearing for exactly three
  declarations, each of which follows directly from D1's round trips.
* **Conjugation invariance needs no basis-independence argument.**  Both
  computations happen in one fixed basis; the adjoint step is what moves
  between the left and right cases.
* **Hilbert–Schmidt strong continuity is the part with real content** — the
  columns must go to zero together — and the `ε`-split is best done in `ℝ≥0∞`,
  where `ENNReal.sum_add_tsum_compl` and `ENNReal.tendsto_tsum_compl_atTop_zero`
  carry no summability side conditions.  `tendsto_energy_sub_comp` is stated
  more generally than the application needs (no group structure assumed), so it
  should be reusable for any other Hilbert–Schmidt continuity argument.

---

## Update 2026-07-29 (final) — **SR-D3 is complete**

`generator_sylvesterGroup_apply` landed.  Tree green at 9281 jobs; every
declaration below depends only on `propext`, `Classical.choice`, `Quot.sound`.

SR-D3 in full, all five files landed today, all in `ForTauCeti`:

| file | statement |
| --- | --- |
| `OneParameterUnitaryGroup/Stone.lean` | Stone's theorem, forward direction |
| `HilbertSchmidtLp.lean` (D1, earlier) | the column bijection |
| `HilbertSchmidtSpace.lean` | the three representation facts |
| `HilbertSchmidtConjugation.lean` | HS-norm invariance under conjugation |
| `SylvesterGroup.lean` | the flow is a unitary group; **generator self-adjoint** |
| `SylvesterGenerator.lean` | **the generator satisfies `A Z - Z B = C`** |

**Nothing in SR-D3 is outstanding.**

### SR-D4 is unblocked and is the next lane worth taking

It is the re-point of the five remaining in-scope `import Spectra` files onto
the API above, and it is the last thing between the tree and **zero** in-scope
Spectra imports.  It is mechanical in the sense that the mathematics is done;
it is not zero-effort, because the donor's names have to be mapped one by one.

The mapping to start from:

* `Spectra.HilbertSchmidtTensor.Space E F` → `lp (fun _ : ι => E) 2`, `ι` the
  index of a Hilbert basis of `F`
* `Spectra.HilbertSchmidtTensor.toOperator` → `TauCeti.HilbertSchmidt.ofLp b`
* `toOperator_injective` → `ofLp_injective`
* `existsUnique_tensor_iff_summable_columns` → `existsUnique_ofLp_iff_summable`
* `norm_sq_eq_tsum_column_norm_sq` → `norm_sq_eq_tsum_norm_column_sq`
* `Spectra.HilbertSchmidtTensor.sylvesterGroup` → `HilbertSchmidt.sylvesterGroup`
* `Spectra.OneParameterUnitaryGroup.generator` → `TauCeti.OneParameterUnitaryGroup.generator`
* `Spectra.QuantumMechanics.SpectralTheory.spectralGapSolution` and its three
  companions → `LinearPMap/SpectralGapInverse.lean`'s `gapInverse` and
  `apply_gapInverse`, applied to the self-adjoint operator supplied by
  `isSelfAdjoint_generator_sylvesterGroup`
* `toOperator_hasGeneratorSylvesterEquation` → `generator_sylvesterGroup_apply`

One caveat to check rather than assume: `Audits/SylvesterHilbertSchmidt.lean`
and `Sylvester/HilbertSchmidtPairwise.lean` also import Spectra's BornRule /
PVM / Observable modules, which are **not** Hilbert–Schmidt infrastructure and
may need a different replacement or may turn out to be unused `open`s.

---

## Update 2026-07-29 — S6 groundwork: the authorship debt is measurably shrinking

Two S6 steps that do **not** wait on SR-D4b, both landed.

### 1. The namespace gate is future-proofed

`scripts/check_spectra_namespace.py` walks every `.lean` file in the repo and
forbids declaring into `namespace Spectra` outside an exempt prefix.  The S6
plan moves `vendor/Spectra` to `retired/Spectra`; without `retired/` in
`EXEMPT_PREFIXES` **that move alone would turn 427 legitimately-vendored files
into reported violations**, failing the gate on a commit that changes no Lean
source. `retired/` is now listed, ahead of the move, so the two concerns stay
separable.  Gate still green today (the prefix matches nothing yet).

### 2. Four of the eleven DKPS-authored vendor files are now unreachable

`dev/tauceti/spectra-vendor-authorship-baseline.json` lists 11 files inside
`vendor/Spectra` that are ours rather than the donor's.  Computing the
transitive import closure of the **three** remaining in-scope consumers into the
vendored tree (100 vendored modules reachable) gives:

| authored file | still reachable? |
| --- | --- |
| `Spaces/Tensor/HilbertSchmidt.lean` | reachable |
| `Spaces/Tensor/HilbertSchmidtFlow.lean` | reachable |
| `Spaces/Tensor/HilbertSchmidtGeneratorBridge.lean` | reachable |
| `Spaces/Tensor/HilbertSchmidtSpectralGap.lean` | reachable |
| `SpectralTheory/Calculus/SpectralGapInverse.lean` | reachable |
| `OneParameterUnitaryGroup/Product.lean` | reachable |
| `QuantumMechanics/BornRule/POVMCore.lean` | reachable |
| `ProjValMeasure/GeneralMap.lean` | **dead** |
| `QuantumMechanics/BornRule/Joint/ProjectivePVM.lean` | **dead** |
| `SpectralTheory/SeparatedIntertwiner.lean` | **dead** |
| `YosidaHille/RectangularIntertwining.lean` | **dead** |

`ProjectivePVM.lean` became dead today, when the vestigial Born-rule import was
dropped from `Audits/SylvesterHilbertSchmidt.lean`.
`SeparatedIntertwiner.lean` was already superseded by
`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`.

Per jon's instruction the bar for these is *"nothing depends on it"*, not
deletion — so the four dead ones are **done**, and porting them to `ForTauCeti`
is optional rather than required.

**All seven survivors are the SR-D4b cluster.**  That is the useful conclusion:
there is no separate authorship backlog left to work off.  Closing D4b closes
the authorship ledger at the same time.

---

## Update 2026-07-29 — SR-D4b: a better attack than the one I posted earlier

I earlier recommended extending `FourierSemigroup.lean` to unbounded generators
and to the Hilbert–Schmidt norm.  **I now think that is the worse of the two
routes**, and this supersedes it.  The reduction chain below is unchanged and
still correct; only the final step's proof strategy is different.

### The chain, restated

1. `HasVectorSpectralGap hS δ f` unfolds to
   `(spectralPVM hS).diag f (Ioo (-δ) δ) = 0`.
2. `diag_eq_zero_of_subset_resolventSet` supplies that **for every `f` at once**
   given `∀ real s, |s| < δ → (s : ℂ) ∈ resolventSet 𝒮`.
3. `𝒮` is self-adjoint, so for **real** `s` the resolvent condition follows from
   a **lower bound alone**: `𝒮 - s` bounded below is injective with closed
   range, and self-adjointness makes `ran(𝒮-s)^⊥ = ker(𝒮-s) = 0`, so the range
   is dense and therefore everything.  This is the pattern already written for
   the imaginary-shift case in `SelfAdjointResolvent.lean`
   (`isClosed_range_shiftMap`, `surjective_shiftMap`); only the input estimate
   changes.
4. So the entire lane is: **`(δ - |s|) ‖Z‖ ≤ ‖𝒮 Z - s Z‖` on `dom 𝒮`.**

### The better proof of step 4: finite partitions, not product measures

Let `P_i = E_A(S_i)` and `Q_j = E_B(T_j)` be the spectral projections of `A` and
`B` for finite Borel partitions of the two spectra into pieces of diameter `≤ ε`.
Then:

* `P_i` commutes with `A` and `Q_j` with `B`, so `P_i (𝒮 Z) Q_j = 𝒮 (P_i Z Q_j)`
  — the Sylvester operator preserves each block;
* on the block, `A` is within `ε` of a scalar `λ_i` and `B` within `ε` of `α_j`,
  so `‖𝒮 (P_i Z Q_j)‖ ≥ (|λ_i - α_j| - 2ε) ‖P_i Z Q_j‖ ≥ (δ - 2ε) ‖P_i Z Q_j‖`;
* **Pythagoras in Hilbert–Schmidt**: since `∑_i P_i = 1` and `∑_j Q_j = 1` with
  the pieces mutually orthogonal, `∑_{i,j} ‖P_i Z Q_j‖² = ‖Z‖²`, and likewise
  for `𝒮 Z`.

Summing the block estimates gives `‖𝒮 Z‖ ≥ (δ - 2ε) ‖Z‖`, and `ε → 0` finishes.
Shifting `B` by `s` (`σ(B + s) = σ(B) + s`) gives the `s` version.

**Why this is better than the Fourier route.**  It needs no operator-valued
integral, no characteristic-function identity, no Haagerup–Zsidó multiplier, and
no bounded-to-unbounded extension — the spectral projections of an unbounded
self-adjoint operator are already in the tree (`specProjection`), and they are
exactly what the argument consumes.  The Fourier route needs all four.

**The one genuinely new ingredient** is the Hilbert–Schmidt Pythagoras identity
`∑_{i,j} ‖P_i Z Q_j‖² = ‖Z‖²` for orthogonal families acting on the two sides.
In the `lp`-of-columns model the right-hand projections act on the index and the
left-hand ones columnwise, so this is a genuine lemma and is the natural first
commit of the lane — and it is worth having independently of D4b.

---

## Update 2026-07-29 — SR-D4b: the block estimate, worked out

Five commits have landed toward D4b.  What follows is the remaining argument in
executable detail, because the shape matters and one obvious version of it is
**wrong**.

### Do the estimate at the Hilbert–Schmidt level, not pointwise

The tempting route is to use `generator_sylvesterGroup_apply` pointwise —
`(𝒮 W)(x) = A (W x) - W (B x)` — and estimate vector by vector.  **That
degrades**: the error terms come out as `‖Z‖_op ‖Q x‖`, which cannot be compared
to `‖W‖_HS`, so the blocks do not reassemble.

Do it at the operator level instead, using idempotence to keep every bound
relative to the block's *own* Hilbert–Schmidt norm:

* `W = P W`, so `(A - λ) W = ((A - λ) P) W` and hence
  `‖(A - λ) W‖_HS ≤ ‖(A - λ) P‖_op · ‖W‖_HS ≤ ε ‖W‖_HS`;
* `W = W Q`, so `W (B - α) = W ((B - α) Q)` and hence
  `‖W (B - α)‖_HS ≤ ‖W‖_HS · ‖(B - α) Q‖_op ≤ ε ‖W‖_HS`;
* subtracting, `𝒮 W - (λ - α) W = (A - λ) W - W (B - α)`, so
  `‖𝒮 W‖_HS ≥ (|λ - α| - 2ε) ‖W‖_HS ≥ (δ - 2ε) ‖W‖_HS`.

Both operator bounds are the two ideal properties
(`hilbertSchmidtEnergy_comp_left_le`, `_comp_right_le`), already in the tree.

### The one construction still missing

`(A - λ) P` has to exist **as a bounded operator** of norm `≤ ε`.  The tree
gives the estimate pointwise —
`norm_sub_smul_le_of_mem_specRange : ‖A ⟨y, _⟩ - c • y‖ ≤ r ‖y‖` for `y` in the
spectral range — so what is missing is only the bundling of `y ↦ A y - λ y` on
`ran P` into a `→L`, with `specProjection_mem_domain` supplying that the range
lands in `dom A`.  That is the next commit.

### Then the assembly

Partition `ℝ` into `[kε, (k+1)ε)` for `k : ℤ` (countable, which is why the
Pythagoras lemmas were stated for an arbitrary index type rather than a
`Finset`).  A block with `P_k = 0` or `Q_l = 0` contributes nothing, and a
**nonzero** projection forces its interval to meet the spectrum
(`specProjection_eq_zero_of_subset_resolventSet`, contrapositive), which is what
licenses `|λ_k - α_l| ≥ δ` on the surviving blocks.  Sum with
`tsum_tsum_energy_blocks`, let `ε → 0`, and feed the resulting lower bound into
the closed-range argument of `SelfAdjointResolvent.lean` to get resolvent
membership — after which `diag_eq_zero_of_subset_resolventSet` gives the vector
gap for every `f` at once.

---

## Correction 2026-07-29 — the "21,581-line tensor closure" figure is misattributed

I have cited **21,581 lines** repeatedly — in commit messages, in `dev/LANES.md`,
and in module docstrings — as the cost of the donor's Hilbert tensor product,
and used it to justify modelling the Hilbert–Schmidt space as `lp` instead.
**The number is real but it is not the tensor product's.**  Measured:

`Spectra/Spaces/Tensor/HilbertSchmidt.lean` has four Spectra imports:

| import | closure |
| --- | --- |
| `Spaces.Tensor.Map` (the tensor product itself) | 2 modules, 599 lines |
| `SpectralTheory.Antilinear.ConjugateSpace` | 1 module, 151 lines |
| `Operator.AdjointClosure` | 4 modules, 908 lines |
| **`QuantumMechanics.BornRule.Joint.Basic`** | **86 modules, 20,268 lines** |

So ~20k of the ~21.6k is a *single* import — the joint Born-rule stack — and the
genuine tensor machinery is about 2,300 lines.

**And the Hilbert tensor product proper is 324 lines in one file that imports
only Mathlib.**  `Spectra/Spaces/Tensor/Hilbert.lean` is essentially
`abbrev HilbertTensor := Completion (E ⊗[𝕜] F)` plus a convenience API, resting
on `Mathlib.Analysis.InnerProductSpace.TensorProduct` and
`Mathlib.Analysis.InnerProductSpace.Completion`, both of which exist.

### What this does and does not change

It does **not** rescue the donor's spectral-gap proof: that proof is the thing
that reaches into the Born-rule stack (joint PVMs, product measures), so porting
the tensor product would not have unlocked SR-D4b.  The `lp` model remains the
right way to finish D4b.

It **does** mean the reason I gave was wrong.  The honest reason is *"the
donor's gap proof drags in 20k lines of quantum-measurement machinery"*, not
*"tensor products are expensive"*.  Those are different claims and I conflated
them, then repeated the conflation as established fact.

### A separate, cheap opportunity — not part of this campaign

A Hilbert tensor product in `ForTauCeti` would be ~324 lines over Mathlib, is
not an API break (it is a Mathlib-shaped construction Mathlib simply lacks), and
is worth having on its own merits.  It would need a Tau Ceti roadmap entry,
since the roadmap gates *new* mathematics.  **Deliberately not bundled into the
Spectra removal** — Davis–Kahan does not need it, and tying it to this campaign
is what produced the confusion above in the first place.

---

## Update 2026-07-29 — SR-D4b instantiation: an honest inventory

I have twice called the remaining D4b work "connecting the pieces" or
"bookkeeping".  Working it through, that is wrong again, and the pattern is
worth naming: **the reusable pieces were the easy part, and each one I finish
makes the remainder look smaller than it is.**  Here is the actual inventory.

### What is genuinely done (8 files, all green, all axiom-clean)

`HilbertSchmidtPythagoras`, `Commutant`, `HilbertSchmidtBlock`,
`ProjValMeasure/Additivity`, `SpectralCutOperator`, `RealLowerBound`,
`BlockLowerBound` — plus the per-block estimate and the resolvent-to-gap step,
which were already in the tree.  The *chain* is complete and every link is
proved:

`partition norm split → blockwise bound → global lower bound → resolvent point → gap for every vector`

### What instantiating it at the Sylvester operator still needs

Each of these is standard mathematics and none is hard, but each is a Lean
lemma that does not yet exist:

1. **Spectral projections of `generator V` commute with `V t`.**  The block map
   only commutes with the Sylvester flow (`blockCLM_comm_sylvesterGroup`) if `P`
   and `Q` commute with their groups.  For a spectral projection that is
   standard but needs the Borel calculus to be shown commuting with the group —
   which is *not* in the tree.
2. **`Q` commutes with the unbounded `B` on its domain**, and maps `dom B` into
   itself.  Follows from (1) via `generator_commute`, once (1) exists.
3. **The block operator identity**, extended by density.
   `generator_sylvesterGroup_apply` gives the Sylvester equation only at
   `x ∈ dom B`; the identity wanted is between *bounded operators* on all of `F`.
   Both sides are continuous and `dom B` is dense, so this is an `ext_on`
   argument — but it has to be written.
4. **The partition itself**: `I k = Ico (kε) ((k+1)ε)` for `k : ℤ`, with
   measurability, pairwise disjointness and covering, and the fact that a
   *nonzero* projection forces its interval to meet the spectrum
   (`specProjection_eq_zero_of_subset_resolventSet`, contrapositive).
5. **The `ε → 0` limit**, and the shift `σ(B + s) = σ(B) + s`.

### Estimate, stated as a range rather than a point

Three to five more files.  I am not going to give a tighter number: my estimates
on this cluster have been wrong in both directions four times today, while the
*measurements* — build counts, importer counts, closure sizes — have held up
every time.  Treat the inventory above as the reliable artefact and ignore any
schedule I attach to it.
