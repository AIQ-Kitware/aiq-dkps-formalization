# Spectra removal — open parallel lanes

**Purpose.** The Spectra removal campaign is down to **9 files** carrying
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

## Status board (updated 2026-07-29, after SR-A/B/C landed)

| lane | files | blocker | holder |
|---|---|---|---|
| **SR-A** Cayley / Möbius / `SelfAdjointOperator` bridge | 5 | — | **DONE** (namek) |
| **SR-B** spectral support | 1 | — | **DONE** (namek) |
| **SR-C** half-line form bounds | 1 | — | **DONE** (namek) |
| **SR-D** Hilbert–Schmidt tensor | 5 | the HS tensor development itself | *open* |
| **SR-E** Rosenblum | 1 | intertwiner of disjoint spectra vanishes | claimed |
| **SR-F** Experimental stragglers | 3 | three unrelated small items | *open* |

`import Spectra` in `DavisKahan/**`: **15 → 9**.  The nine remaining are exactly
SR-D (5), SR-E (1) and SR-F (3).

`InfiniteProposition41.lean` is counted in SR-F but also consumes
`SelfAdjointOperator.ofBounded`; it should be taken **after** SR-A lands, or its
`ofBounded` uses repointed onto whatever SR-A leaves behind.

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

## SR-F — Experimental stragglers  *(open)*

Three unrelated small items, all outside `defaultTargets` — so `lake build` will
not catch regressions here and each must be checked with an explicit
`lake build <Module>`. They are removal obligations only because S6 criterion (1)
is "no `.lean` outside `vendor/` and `external/` imports Spectra".

| file | needs |
|---|---|
| `Experimental/InfiniteDimensional/Sylvester/FourierSemigroup.lean` (890) | `YosidaHille.Approximation.ExpBounded.Unitary`, `CayleyTransform.BorelCalculus`. Per the plan's Mathlib-substitution table, `expBounded B t` is `NormedSpace.exp ((t : ℂ) • B)` and unitarity is `selfAdjoint.expUnitary` — most of this is substitution, not proof |
| `Experimental/MathAhead/Section4/InfiniteProposition41.lean` (700) | `SpectralTheory.Algebra`, plus `SelfAdjointOperator.ofBounded` (take after SR-A) |
| `Experimental/Scratch/SharedFoundations/Ideal/OperatorAbsoluteValueComplex.lean` (131) | polar decomposition of a **bounded** operator, which Mathlib does not have. `ForTauCeti`'s polar API is rectangular and strictly more general than the donor's (see plan §S1) — check it covers this before porting anything |

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
