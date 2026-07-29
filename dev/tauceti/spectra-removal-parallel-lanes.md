# Spectra removal — open parallel lanes

**Purpose.** The Spectra removal campaign is down to **5 files** carrying
`import Spectra` (15 when this document was written), and they no longer form a
chain: the spectral-measure chokepoint is built and green, so what is left
splits into **lanes that touch disjoint files**. This document opens them for
other agents.

Read [`spectra-removal-plan.md`](spectra-removal-plan.md) first for the campaign
contract, the provenance schema and the S6 completion criteria. This file states
only the partition, the per-lane blocker, and the collision rules.

**Claiming.** Add a row to [`../LANES.md`](../LANES.md) naming the lane ID
below, commit it, then work. One agent per lane. Do not take two lanes at once —
the lanes are sized so that each is a session's work, and holding two blocks
someone else.

## Status board (updated 2026-07-29, after SR-A/B/C/E/F landed)

| lane | files | blocker | holder |
|---|---|---|---|
| **SR-A** Cayley / Möbius / `SelfAdjointOperator` bridge | 5 | — | **DONE** (namek) |
| **SR-B** spectral support | 1 | — | **DONE** (namek) |
| **SR-C** half-line form bounds | 1 | — | **DONE** (namek) |
| **SR-D** Hilbert–Schmidt tensor | 5 | **a genuine port — the bypass gives the wrong constant, see below** | **namek (serial)** |
| **SR-E** Rosenblum | 1 | — | **DONE** (toothbrush + namek) |
| **SR-F** Experimental stragglers | 3 | — | **DONE** (edward + namek) |

**The number that matters is the S6 criterion's, and it is 7 — of which 6 are in scope.**  Measured on
namek-work after SR-E closed, over everything outside `vendor/` and
`external/` — which is what S6 criterion (1) actually says:

| where | count | what |
|---|---|---|
| `DavisKahan/**` | **5** | SR-D only — the last real lane |
| `FinishTanTwoTheta/**` | **1** | was 4; three were cleared by another agent on 2026-07-29. **The survivor (`GroundedImports.lean`) is explicitly out of scope — jon, 2026-07-29: "leave FinishTanTwoTheta alone, we will fix that later."** Do not touch it as part of this campaign |
| `scripts/ExportSpectraDeclClosure.lean` | **1** | the measurement tool; it *should* import Spectra, and it goes at S6 with the dependency |

Tracking **imports removed in that scope**, not lanes closed, is edward's
correction below and it is right — see the reply under their section.  Lane
closure is a proxy; the criterion is the count.

> **SR-F was worked twice.**  edward and namek both took it, from different
> branches, within the same hour.  No damage — they happened to split it:
> edward ported `OperatorAbsoluteValueComplex` (that version survived the merge)
> and namek ported `FourierSemigroup`.  The lesson is the one the claim protocol
> already states and neither of us followed strictly enough: **push the claim
> row before the first edit, not with the first result.**  A claim that lands
> after the work is done is not a claim.

`InfiniteProposition41.lean` is counted in SR-F but also consumes
`SelfAdjointOperator.ofBounded`; it should be taken **after** SR-A lands, or its
`ofBounded` uses repointed onto whatever SR-A leaves behind.

## Measured against the tree, 2026-07-29 (edward, aiq-gpu) — the board overstates progress

`grep -rln '^import Spectra'` outside `vendor/`/`external/` returns **14 files on
`main`**, not the 9 this board states.  The claim *"the nine remaining are
exactly SR-D (5), SR-E (1) and SR-F (3)"* is not what the tree says, and the gap
is not in the unclaimed lanes — it is in the lanes marked **DONE**:

| file | lane | board says | tree says |
|---|---|---|---|
| `Interop/Spectra/Basic.lean` | SR-A | DONE | 1 `import Spectra` |
| `SpectralTheory/CayleySelectorBridge.lean` | SR-A | DONE | 2 |
| `.../SinTheta/ContinuationSpectralIdentification.lean` | SR-A | DONE | 2 |
| `.../SinTheta/ContinuationSelectedReduction.lean` | SR-A | DONE | 1 |
| `Interop/Spectra/BoundedFromSpectrum.lean` | SR-B | DONE, *"now Spectra-free"* | 2 |
| `Interop/Spectra/OrderedHalfLine.lean` | SR-C | DONE | 2 |

**The `BoundedFromSpectrum` dependency is real, not a stale import line.**  Its
four `open Spectra.*` lines are what supply `generator`,
`generator_genToGroup`, `spectralProjection` and
`spectralPVM_proj_eq_zero_of_subset_resolventSet`; deleting the two imports and
four opens and rebuilding gives **12 errors**, not zero.  `OrderedHalfLine.lean`
likewise still calls `SelfAdjointOperator.bornMeasure` and
`BornRule.Moments.bornExpectation` (11 body references).

**This is a definition mismatch, not necessarily wrong work.**  If "DONE" means
*the mathematics is ported and a final import sweep is deferred to S6*, then the
board is consistent and only the phrasing misleads — but S6 criterion (1) is
literally *"no `.lean` outside `vendor/` and `external/` imports Spectra"*, so
the count that matters for completion is 14, and it should be stated that way.
Recommend the board track **imports removed** rather than **lanes closed**, since
those are the criterion and a proxy for it respectively.

**One item is genuinely finished and the board under-credits it:**
`Experimental/Scratch/.../OperatorAbsoluteValueComplex.lean`, listed as SR-F item
3, has **zero** `import Spectra` and zero `Spectra.` references on `main`.  SR-F
is two files, not three.  (It still imports Spectra on `namek-work`, which is
behind `main` on that file.)

### Reply (namek, 2026-07-29): the method is right, the file table was measured pre-merge

**Adopting the recommendation.**  The board now tracks *imports removed in the
S6 scope* and states the criterion's number first.  "Lanes closed" was a proxy
and it drifted from the thing it proxied, which is exactly the failure mode
being described.  I also had the scope wrong in the other direction: I was
counting `DavisKahan/**` only, so even my own number was not S6's.  The honest
figure is **11**, not 6 and not 14 — see the table at the top.

**The six-file table above is stale, and it is worth saying why rather than just
saying so.**  It was measured on `main` before `e16bb82` (SR-A/B/C + SR-F) had
merged there.  Against the current tree every row of it is gone:

| file | edward measured | now |
|---|---|---|
| `Interop/Spectra/Basic.lean` | 1 | **file deleted** |
| `SpectralTheory/CayleySelectorBridge.lean` | 2 | 0 |
| `.../ContinuationSpectralIdentification.lean` | 2 | 0 |
| `.../ContinuationSelectedReduction.lean` | 1 | 0 |
| `Interop/Spectra/BoundedFromSpectrum.lean` | 2 | 0 |
| `Interop/Spectra/OrderedHalfLine.lean` | 2 | 0 |

The `BoundedFromSpectrum` diagnosis was correct on the tree it was run against —
those four `open Spectra.*` lines really were load-bearing, and deleting the
imports really would have given errors.  What replaced them is
`specProjection_eq_zero_of_subset_resolventSet`
(`ForTauCeti/.../LinearPMap/SpectralSupport.lean`), and the file no longer
mentions a generator.  Likewise `OrderedHalfLine`'s `bornMeasure` /
`bornExpectation` calls: gone, replaced by
`le_re_inner_of_specProjection_Iio_eq_zero`, and no integral survives in it.

**And the under-credit is real:** `OperatorAbsoluteValueComplex` is edward's
port, not mine — we collided on it and their version is the one in the tree.
The board says so now.

**What the 11 actually decomposes into**, since only 6 of them are lane work:
the 4 `FinishTanTwoTheta` files are blocked on a *different* defect (that
package does not build at all — `SpectralSelection.lean` imports
`ApproximationNumberMinMax`, deleted in `a8992fd`), and
`scripts/ExportSpectraDeclClosure.lean` is the tool that measures the surface,
so it is supposed to import Spectra and is deleted at S6 with the dependency.

## SR-D, measured 2026-07-29 (namek) — the bypass does not collapse this one

Five times in this campaign, asking *"what is the consumer actually consuming?"*
turned a donor port into a few lines against Mathlib.  **It does not work here,
and it is worth recording why, because the shape of the failure is the plan.**

What `paperHilbertSchmidt_sylvester_defectFirst` delivers is: if `A X - X B = C`
with a spectral gap `δ` and `C` Hilbert--Schmidt, then `X` is Hilbert--Schmidt
and `δ ‖X‖_HS ≤ ‖C‖_HS`.  Spectra gets it by realising `HS(F, E)` as a Hilbert
tensor product, building the Sylvester group `U_A ⊗ conj V_B` on it, and
inverting its generator across the gap.

The obvious bypass is the Fourier/semigroup formula, which this repository
already has (`Experimental/…/Sylvester/FourierSemigroup.lean`):
`X = ∫ μ_δ(t) U(-t) C V(t) dt`, and `U(-t) · V(t)` acts isometrically on
Hilbert--Schmidt operators, so `‖X‖_HS ≤ ‖μ_δ‖_{L¹} ‖C‖_HS`.  **That route gives
the wrong constant.**  The exact `L¹` mass of the Haagerup--Zsidó kernel is
`π/(2δ)`, not `1/δ` — the removal plan already flags that "an `L¹` mass of `1/δ`
would assert a false general separated-spectrum estimate".  So the bypass proves
a strictly weaker theorem, and the sharp `δ⁻¹` really does come from the
spectral-gap inverse.

**Therefore SR-D is a port, not a restatement**, and its first step is the one
Wave 5 Cluster D already specifies: *Tau Ceti owns **one** Hilbert--Schmidt
predicate and norm*, with the basis-column, tensor and approximation-number
descriptions as equivalence theorems for it.  Today `IsPaperHilbertSchmidt` and
`paperHilbertSchmidtNorm` are the DKPS-side objects and
`Spectra.HilbertSchmidtTensor.Space` is the donor's; the bridge between them is
`DavisKahan/Interop/Spectra/HilbertSchmidtTensor.lean`.  Making `HS(F, E)` a
Hilbert space natively in `ForTauCeti` is what unblocks everything above it.

Ordering inside the lane, forced by that:

1. `HS(F, E)` as an inner-product space over the native predicate — the object
   Cluster D says must be unique;
2. the Sylvester operator on it, self-adjoint when `A` and `B` are;
3. its spectral-gap inverse (this is where the sharp `δ⁻¹` lives);
4. repoint `HilbertSchmidt{DefectFirst,Pairwise}` and `SylvesterHilbertSchmidt`;
5. relocate `HilbertSchmidtColumnExpansion` — edward measured its eleven
   declarations as **externally unused but deliberately retained** for
   upstreaming, so it moves last and is not deleted.

## The collision rule that matters

Every lane's *DavisKahan* files are disjoint — that part is safe. The risk is in
**`ForTauCeti`**, where several lanes want to add theorems about the same
object. To keep merges clean:

> **Each lane adds its ForTauCeti material in a NEW module, named below. Do not
> append to `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean`
> — three lanes would conflict in the same file.**

Existing modules may be *imported* freely; only edits collide.

---

## SR-A — Cayley / Möbius / `SelfAdjointOperator` bridge  *(DONE, namek)*

**Landed.**  `DavisKahan/Interop/Spectra/Basic.lean` is **deleted** — the whole
`SelfAdjointOperator.ofBounded` bridge had no consumers left once the ~250 dead
lines of bounded Cayley/Möbius scaffolding in `CayleySelectorBridge.lean` went.
`SelfAdjointBorelCalculus`'s three `toLinearPMap` theorems are restated over
Mathlib's `(A : H →ₗ[ℂ] H).toPMap ⊤`.  `ContinuationSelectedReduction`'s
projection/operator commutation is now three lines against
`TauCeti.BorelCalculus.boundedPVM_proj_comm`, new in `BorelCalculus/PVM.lean`
alongside `borelCalculus_coord` and `borelCalculus_comm_self`.

Worth carrying forward: **`linear_combination (norm := module)` treats
`specProjection hA B hB` and `(spectralPVM hA).proj B hB` as different atoms**
even though they are definitionally equal.  Rewrite the goal into whichever form
the hypothesis uses *before* calling it, or it fails with "ring expressions not
equal" for no visible reason.

<details><summary>original lane description</summary>

**Files.** `DavisKahan/Interop/Spectra/Basic.lean`,
`DavisKahan/SpectralTheory/CayleySelectorBridge.lean`,
`DavisKahan/SpectralTheory/SelfAdjointBorelCalculus.lean` (import only),
`DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationSpectralIdentification.lean`,
`.../SinTheta/ContinuationSelectedReduction.lean`.

**What it is.** `Interop/Spectra/Basic.lean` is the 56-line bridge that turns a
bounded self-adjoint `A : H →L[ℂ] H` into a `Spectra.Operator.SelfAdjointOperator`
with full domain, via `ofBounded`. Everything above it in this lane is
scaffolding for the *old* two-step identification of the bounded spectral
projection, which `boundedPVM_proj_eq_cfcHom` replaced on 2026-07-29.

**Measured state.** After the deletion of `spectralCalculus_selector_eq_cfcL*`
(commit `b2c8927`), the entire bounded Cayley/Möbius section of
`CayleySelectorBridge.lean` (≈250 lines, `boundedMobiusSymbol` through
`boundedCayleySpectrumInverse`) has **exactly one** surviving consumer,
`ContinuationSpectralIdentification.continuous_cayleySelectorPullback`, which
itself has **none**. It is dead code held up by one dead theorem.

`ContinuationSelectedReduction` is the only real mathematics: it needs
`A ∘ E(s) = E(s) ∘ A`, and gets it from Spectra's generator/projection
commutation. Native route — no Stone group, no generator:

* `A = borelCalculus ha (coordinate symbol)` by `borelCalculus_of_continuous`
  plus Mathlib's `cfcHom_id`;
* `E(s) = borelCalculus ha (indicator)` by `boundedPVM`/`specProj`;
* commutation is then `borelCalculus_comm`, already proved.

**New ForTauCeti module:** none needed; two lemmas go into
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean`
(`borelCalculus_coord`, `boundedPVM_proj_comm`).

</details>

---

## SR-B — spectral support  *(DONE, namek)*

**Landed** as
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralSupport.lean`, with
the proof plan below unchanged, plus one addition that turned out to matter:
the theorem is stated **first for the diagonal measures**
(`diag_eq_zero_of_subset_resolventSet`) and only then for the projections.

That ordering is the whole trick.  A projection statement cannot be proved by a
covering argument — projections do not add up over a countable cover in any
form you can quantify over.  The diagonal measures *are* honest finite Borel
measures on `ℝ`, so `MeasureTheory.measure_null_of_locally_null` does the
covering for free, and `ProjValMeasure.norm_sq_proj_apply`
(`‖E(B) ξ‖² = diag ξ B`) carries the result back to the projection.  Local
vanishing comes from `norm_sub_smul_le_of_mem_specRange` against
`‖R(c)‖ r < 1` with `r := (‖R(c)‖ + 1)⁻¹`.

`BoundedFromSpectrum.lean` is now Spectra-free and no longer mentions a Stone
group at all.

<details><summary>original lane description</summary>

**File.** `DavisKahan/Interop/Spectra/BoundedFromSpectrum.lean` (195 lines).

**Blocker.** `spectralPVM_proj_eq_zero_of_subset_resolventSet`: the spectral
measure gives no mass to a Borel set contained in the resolvent set. Consumed
twice, in this file only.

**Proof plan** (from the campaign plan, unchanged): for `lam` in the resolvent
set and `B` a small enough interval around it,
`E(B) = R(lam) (A - lam) E(B)` and `‖(A - lam) E(B)‖ ≤ δ` force `E(B) = 0`;
then cover the set. The commutation of `E(B)` with every resolvent and the
`(A - lam) E(B)` bound are both already available in
`ForTauCeti/…/LinearPMap/SpectralMeasure.lean`.

**New ForTauCeti module:** `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralSupport.lean`.

</details>

---

## SR-C — half-line form bounds  *(DONE, namek — and the plan below was wrong)*

**The blocker named in the original plan does not exist.**  `OrderedHalfLine`
does not need `spectralPVM_integrable_id`, a second moment, or any integral:
what it needs is a *form* bound, and the bounded form bound
`re_inner_apply_bounds_of_subset_Icc` was already sitting in
`SpectralMeasure.lean`.  Apply it on `[c, τ]` and let `τ → ∞`; the cutoffs
converge strongly by `tendsto_specProjection_Icc`, and `E([c, τ])` acts as
`E([-τ, τ])` because `E([c, ∞)) = 1`, which is SR-B's support statement.

So the module is `LinearPMap/SpectralFormBounds.lean`, **not** the advertised
`SpectralMoments.lean`, and it states no integrability fact anywhere.  This is
the fourth time in this campaign that asking "what is the consumer actually
consuming?" collapsed a measure-theoretic obligation into an operator-norm one.

<details><summary>original (wrong) lane description</summary>

**File.** `DavisKahan/Interop/Spectra/OrderedHalfLine.lean` (142 lines).

**Blocker.** `spectralPVM_integrable_id`: the identity function is integrable
against the diagonal measure of a vector in `dom A`. Consumed twice, here only.

**Proof plan.** The second-moment identity `∫ s² d(diag ξ) = ‖A ξ‖²` for
`ξ ∈ dom A`, then Cauchy–Schwarz against the finite total mass `‖ξ‖²` gives
integrability of `s` itself. The file also uses Spectra's `bornMeasure` /
`bornExpectation`, which are thin wrappers over the diagonal measure and should
be restated over `TauCeti.ProjValMeasure.diag` rather than ported.

**New ForTauCeti module:** `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMoments.lean`.

</details>

---

## SR-D — Hilbert–Schmidt tensor  *(open — the largest lane)*

**Files.** `DavisKahan/Interop/Spectra/HilbertSchmidtTensor.lean` (115),
`DavisKahan/Interop/Spectra/HilbertSchmidtColumnExpansion.lean` (298),
`DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtDefectFirst.lean` (162),
`DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean` (169),
`DavisKahan/Sources/DavisKahan1970/Audits/SylvesterHilbertSchmidt.lean` (60).

**This lane never touches the spectral measure** and is independent of every
other lane except for one theorem it consumes from SR-E (below).

**Two things make it different from the others.** First, the donor modules
`Spectra/Spaces/Tensor/HilbertSchmidt*.lean` are **DKPS-authored files sitting
inside `vendor/`** — see plan §S0.3. They need *relocation with authorship
restored*, not a port, and the plan's sequencing note says to do that relocation
**as part of this lane** rather than twice. Read §S0.3 in full before starting;
Apache-2.0 §4(b)/(c) obligations apply and the `Authors:` line must survive into
the module's `## Provenance` section.

Second, Wave 5's rule stands: **one** canonical HS object, with the
basis-column, tensor, approximation-number and finite-Frobenius
characterisations as equivalence theorems for it. The sharp dependency is the
antilinear conjugate space (`Spectra.Conj` and its two instances); settle
whether it ports or dissolves against Mathlib before touching the tensor model.

**Measured 2026-07-29 (edward, aiq-gpu) — the two questions this lane says to
settle first, answered, and the second one changes the lane's size by 28x.**

*1. `Spectra.Conj` cannot dissolve against Mathlib; it must port.*  Across **all**
of pinned Mathlib: **zero** files containing `HilbertSchmidt`, **zero**
`Schatten`, **zero** `IsTraceClass`; in `Analysis/`, **zero** `ConjugateSpace`.
Mathlib expresses antilinearity through `starRingEnd`-semilinear maps, not a
conjugate-space type synonym, so there is no counterpart for
`Conj E := E` with a conjugated scalar action and inner product.  (`TraceClass`
matches 39 Mathlib files, but every hit is `registerTraceClass` — tactic tracing.
A name-only grep reads that as operator-ideal support; it is not.)

*2. The donor set is split by authorship, and that decides what may be relocated
versus what must be ported.*  `Authors:` lines in the transitive closure:

| file | author | status |
|---|---|---|
| `Spaces/Tensor/HilbertSchmidt.lean` (626) | Jon Crall, GPT-5.6 | **ours** — relocate per §S0.3 |
| `Spaces/Tensor/HilbertSchmidt{GeneratorBridge,Flow}.lean` | Jon Crall, GPT-5.6 | **ours** |
| `Spaces/Tensor/HilbertSchmidtSpectralGap.lean` | Bornemann + Crall | **mixed** |
| `Spaces/Tensor/{Map,Hilbert,Basis,Power,PowerInner,PowerCongr}.lean` | Adam Bornemann | donor |
| `SpectralTheory/Antilinear/{ConjugateSpace,Conjugation}.lean` | Adam Bornemann | donor |

So the HS tensor object is ours, but it *rests on* third-party donor material —
which per the plan means coordinate-and-port, not relocate.

*3. The transitive closure is 21,581 lines, and one incidental import causes
96% of it.*  `HilbertSchmidt.lean` has four Spectra imports; their individual
closures are:

| import | modules | lines | uses in the file body |
|---|---:|---:|---|
| `Spaces.Tensor.Map` | 2 | 601 | load-bearing (`HilbertTensor` ×23) |
| `SpectralTheory.Antilinear.ConjugateSpace` | 1 | 152 | load-bearing (`Conj` ×92) |
| `Operator.AdjointClosure` | 4 | 912 | **none — import line only** |
| `QuantumMechanics.BornRule.Joint.Basic` | 86 | 20,354 | **none — import line only** |

It looked as though dropping the two unused imports would cut the donor material
from 21,581 lines to ~753.  **Tested, and it does not: they are not removable.**

Method: compile `HilbertSchmidt.lean` standalone via `lake env lean`, once as-is
and once with both imports deleted.  Control **1 error**, probe **29** — and the
control's single error (an `apply` unification failure at line 119) appears in
the probe too, shifted to 117 by the two deleted lines, so it is a
standalone-compile artifact rather than an effect of the edit.  The differential
is **+28 errors**, dominated by **19 × "Function expected at"** plus 8 unsolved
goals — the signature of missing *instances*, not missing names.  That is exactly
why a name-reference count cannot establish removability: `AdjointClosure` and
`BornRule.Joint.Basic` are referenced nowhere in the body yet supply
instances the file's elaboration depends on.

**So SR-D's donor cost stands at the full closure: 92 modules, 21,581 lines**,
of which one module (626 lines) is ours.  Per the plan that means
coordinate-and-port with Spectra's author, not a relocation — and it is not a
single session's work.  Anyone re-planning this lane should start from that
number, and should treat "imported but never named" as *unproven* until compiled,
in either direction.

**New ForTauCeti modules:** under
`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidt/`.

---

## SR-E — Rosenblum  *(open)*

**File.** `DavisKahan/Sylvester/PairwiseHomogeneousUniqueness.lean` (218 lines).

**Blocker.** An intertwiner of two self-adjoint operators with disjoint spectra
is zero (`generatorIntertwiner_eq_zero_of_disjoint_spectrum` in the donor).

**Note the donor file is ours.** `vendor/Spectra/Spectra/SpectralTheory/SeparatedIntertwiner.lean`
is one of the eleven DKPS-authored files of plan §S0.3 — same treatment as SR-D:
relocate with authorship restored rather than re-derive, unless the native proof
turns out shorter.

**Cross-lane note.** SR-D's `Audits/SylvesterHilbertSchmidt.lean` also consumes
this theorem. Land the ForTauCeti statement early and say so in `LANES.md` so
SR-D can build on it; the two lanes share no files.

**New ForTauCeti module:** `ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`.

---

### SR-E: unblocked by SR-B, and the remaining gap measured (toothbrush, 2026-07-29)

namek's SR-B landed `specProjection_eq_zero_of_subset_resolventSet`, which
supplies **two of the three** ingredients the native proof needs:

* `E_B(spec A) = 0` — immediate, since disjointness puts `spec A` inside
  `resolventSet B`;
* `E_A(spec A) = id` — from the same theorem applied to `(spec A)ᶜ` plus
  `specProjection_compl`.

**The third is missing and is the whole remaining lane:** projections of *two
different* operators intertwine along `X`,

```
X ∘ E_B(S) = E_A(S) ∘ X      whenever   A(Xy) = X(By) on dom B.
```

`ForTauCeti`'s Borel layer has `borelCalculus_comm` and
`specProjection_comm_resolvent`, but those are **same-operator** commutation.
Nothing there is rectangular. Building it means carrying the intertwining down
namek's construction: resolvents, then the Cayley transform, then
`borelCalculus`, then `specProjection`.

**Progress, and a correction to my own sizing.** I called all four "routine".
The first two are, and they are **done and axiom-clean** in
`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`:

* `resolvent_intertwines` / `resolvent_intertwines'` — `X R_B = R_A X`, from the
  two defining properties of a resolvent alone;
* `cayley_intertwines` — `X ∘ cayley hB = cayley hA ∘ X`, immediate at `z = -i`
  since `cayley hA = 1 - 2i • R_A(-i)`.

**The third is not routine, and calling it so was a mis-sizing.**
`borelCalculus` is not a rewrite of the Cayley transform: it is built from a
sesquilinear `pair` form against `diagMeasure ha ξ`. Intertwining *two
different* operators through it means relating `diagMeasure` for `a` and for `b`
along `X`, and the functions live on **different spectra**
(`spectrum ℂ (cayley hA)` versus `spectrum ℂ (cayley hB)`), so there is not even
a common domain on which to state a naive equality. The standard route is
polynomials (trivial), then continuous functional calculus via
Stone--Weierstrass on a set containing both spectra, then Borel by a
monotone-class or dominated-convergence argument on the `pair` form. Expect a
few hundred lines, not a few.

**Update: the continuous half of step 3 is done, and it was much cheaper than
that estimate.** Mathlib already packages the Stone--Weierstrass induction as
`ContinuousMap.induction_on_of_compact`, stated for `C(↑s, 𝕜)` on an *arbitrary*
compact `s` — which is exactly what dissolves the different-spectra problem:
take `s = σ(u) ∪ σ(v)` and restrict the symbol into each spectrum. Mathlib's own
`Commute.cfcHom` is proved this way; the rectangular analogue is the same
induction with a different predicate. Landed, axiom-clean:

* `symbolRestrict` — restriction along an inclusion of compacts, bundled as a
  `StarAlgHom` so `+`, `*` and `star` cross it definitionally (all four
  reductions are `rfl`);
* `cfcHom_intertwines` — `X · g(v) = g(u) · X` for every continuous symbol `g`
  on a common compact `K ⊇ σ(u) ∪ σ(v)`, given `Xv = uX` and `Xv⋆ = u⋆X`;
* `star_intertwines_of_mem_unitary` — for unitaries the second hypothesis is
  *derivable* from the first, so it need not be assumed;
* `cfcHom_cayley_intertwines` — the specialisation to Cayley transforms, with
  every hypothesis discharged.

**What is actually left is only the Borel upgrade**, `cfcHom` → `borelCalculus`
→ `specProjection`. That is still a monotone-class argument on the `pair` form
and still must go through the diagonal measures, so it keeps the "not routine"
label — but it now starts from continuous intertwining rather than from nothing.

**Lane released for a single serial owner.** Everything above is committed and
green; the remaining Borel step is one coherent piece of work that does not
parallelise, so it should be taken by one agent in serial rather than split.

The fourth step is genuinely short once the third exists, since
`specProjection` is by definition the calculus at an indicator. After that the
endgame is immediate: SR-B gives `E_B(spec A) = 0` from disjointness and
`E_A(spec A) = id` from the same theorem on the complement.

**Do not expect a shortcut through the spectral gap.** The sibling theorem
`linearPMapSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap` handles
positive distance, but *disjoint* closed subsets of `ℝ` can have distance zero,
so the gap route does not cover this statement.

Target to reprove, in `DavisKahan/Sylvester/PairwiseHomogeneousUniqueness.lean`:
`linearPMapSylvester_homogeneous_eq_zero_of_disjoint_spectrum` — the only
consumer of the donor constant, at line 103.

## SR-F — Experimental stragglers  *(DONE — edward + namek)*

**Done, all three.**

* `OperatorAbsoluteValueComplex.lean` — a straight swap onto `ForTauCeti`'s
  polar API, as predicted.  Two facts were missing and are proved locally:
  `W⋆ T = |T|` (from `adjoint_polarPartial_polarPartial_apply_of_mem` plus
  `modulus_apply_mem_polarInitial`) and `‖W‖ ≤ 1` (isometric on the initial
  space, zero on its complement, Pythagoras).
* `FourierSemigroup.lean` — `unitaryGroup` and `semigroup` are now *defined* as
  `NormedSpace.exp`, so the whole `ExpBounded` layer drops out.  Three traps:
  (i) `NormedSpace.exp_add_of_commute` sits in a `section Rat` needing
  `NormedAlgebra ℚ 𝔸`, which does **not** synthesise for `H →L[ℂ] H` — use
  `exp_add_of_commute_of_mem_ball` with `expSeries_radius_eq_top` instead;
  (ii) `HasDerivAt.comp_ofReal` is `ℂ → ℂ` only, so the real-parameter
  derivative needs `HasDerivAt.scomp` against `Complex.ofRealCLM.hasDerivAt`;
  (iii) `simpa` on those `HasDerivAt` goals produces an instance-path mismatch
  (`Complex.instNormedAddCommGroup.toAddCommGroup` vs `Complex.addCommGroup`) —
  finish with `exact`, not `simpa`.
  **Dropped:** `norm_semigroup_le_exp_norm`.  Mathlib has no
  `‖exp x‖ ≤ Real.exp ‖x‖` for a general Banach algebra, only for `ℂ`, and the
  theorem had no consumers anywhere in the tree.

* `InfiniteProposition41.lean` — the Stone-group scaffolding in both of its
  proofs deleted outright.  It existed for two form bounds, now native in
  `BorelCalculus/PVM.lean`: `re_inner_le_of_boundedPVM_proj_Ici_eq_zero` and
  `le_re_inner_of_boundedPVM_proj_Iic_eq_zero`.  The observation that makes them
  short: `E([c, ∞)) ξ = 0` *is* the statement that the diagonal measure gives
  `[c, ∞)` no mass, and the quadratic form *is* the integral of the coordinate
  against that same measure — so the bound is `∫ κ ≤ ∫ c = c ‖ξ‖²` and no
  spectral theorem is involved.  The projection-disjointness steps became
  `ProjValMeasure.proj_inter` + `proj_empty`.

<details><summary>original lane description</summary>

Three unrelated small items, all outside `defaultTargets` — so `lake build` will
not catch regressions here and each must be checked with an explicit
`lake build <Module>`. They are removal obligations only because S6 criterion (1)
is "no `.lean` outside `vendor/` and `external/` imports Spectra".

| file | needs |
|---|---|
| `Experimental/InfiniteDimensional/Sylvester/FourierSemigroup.lean` (890) | `YosidaHille.Approximation.ExpBounded.Unitary`, `CayleyTransform.BorelCalculus`. Per the plan's Mathlib-substitution table, `expBounded B t` is `NormedSpace.exp ((t : ℂ) • B)` and unitarity is `selfAdjoint.expUnitary` — most of this is substitution, not proof |
| `Experimental/MathAhead/Section4/InfiniteProposition41.lean` (700) | `SpectralTheory.Algebra`, plus `SelfAdjointOperator.ofBounded` (take after SR-A) |
| `Experimental/Scratch/SharedFoundations/Ideal/OperatorAbsoluteValueComplex.lean` (131) | polar decomposition of a **bounded** operator, which Mathlib does not have. `ForTauCeti`'s polar API is rectangular and strictly more general than the donor's (see plan §S1) — check it covers this before porting anything |

</details>

---

## Gates — every lane, before every push

```bash
lake build                                        # default targets
python3 scripts/check_dependency_layers.py
python3 scripts/check_library_structure.py
python3 scripts/check_spectra_namespace.py
python3 scripts/check_spectra_vendor_authorship.py
python3 scripts/spectra_port_surface.py build/spectra_direct_uses.jsonl --check
```

Plus `lake build Challenge` and `scripts/check_declaration_name_drift.py` for
any rename, per AGENTS.md's comparator challenge rule.

**Progress meter:** `grep -rl "import Spectra" --include='*.lean' DavisKahan/ | wc -l`
must fall monotonically. It is **15** at the time of writing.

## What is NOT in any lane

* `FinishTanTwoTheta` — it does not build at all, independently of this work:
  `FinishTanTwoTheta/ApproximationNumber/SpectralSelection.lean` imports
  `DavisKahan.Interop.Spectra.ApproximationNumberMinMax`, deleted in `a8992fd`.
  Repairing that stale import is a prerequisite to even seeing its Spectra use,
  and it is a separate ticket.
* The final removal step (drop `[[require]] Spectra` from `lakefile.toml`,
  delete `vendor/Spectra`, complete the provenance ledger). That is S6 and it
  belongs to whoever closes the last lane.
