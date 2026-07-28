# Spectra → Tau Ceti port ledger (declaration level)

**Measured 2026-07-28** against `namek-work` after merging `origin/main`,
`origin/fable/sylvester-upstream-leaves` and `origin/aiq-gpu-work`; default build
green at 9290 jobs. Spectra upstream `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`;
Tau Ceti pinned at `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7`.

This fills the Wave 5 seed matrix of
[`convergence-matrix.md`](convergence-matrix.md), whose own heading says
"to be filled to the declaration level". Wave 5 sized the donor surface as
"≈59 direct Spectra import lines"; that is a textual proxy, and it is both too
big and too small — too big because most of those imports are inherited rather
than load-bearing, too small because it says nothing about *which* declarations
have to be re-homed.

Machine-readable companion: [`spectra-port-surface.json`](spectra-port-surface.json).
Regenerate both with

```bash
lake build
lake env lean --run scripts/ExportSpectraUsage.lean > build/spectra_direct_uses.jsonl
python3 scripts/spectra_port_surface.py build/spectra_direct_uses.jsonl
```

`--check` fails if the committed ledger has drifted from the tree. That gate
exists because the previous figure of record — "the `DavisKahan.All` import
closure currently reaches 119 Spectra modules", in
[`spectra-provenance-map.md`](spectra-provenance-map.md) — is now **152**, and
nothing detected the drift.

## How the surface was measured

From the **compiled environment**, not from import lines and not from textual
name matching: for every declaration whose defining module is a production
module, `Expr.getUsedConstants` over its type and value, filtered to `Spectra.*`.

This matters more than it sounds. A textual scan cannot tell
`Spectra.Operator.SymmetricOperator.DomainConditions.A` from a local binder
named `A`; run naively it reports ~790 "uses" of `Spectra.Operator.Symmetric`,
a module the production build does not reference at all. Import-line counting
has the opposite failure: `DavisKahan/Interop/Spectra/` has 28 modules, of which
only 18 still `import Spectra` — the other 10 were already severed and an import
census would keep crediting them to Spectra.

`DavisKahan.Experimental` is excluded throughout: it is outside `defaultTargets`,
so it is not part of the surface that must be repointed before Spectra can leave
the normal build.

## The headline numbers

| quantity | value |
|---|---|
| vendored Spectra modules on disk | 464 |
| Spectra modules in the **production** import closure | 152 (~39,200 lines) |
| Spectra modules the production build actually **references** | **27** |
| distinct Spectra **constants** referenced | **61** |
| production declarations that reference one | **178**, in **42** modules — all under `DavisKahan/**` |
| production modules that `import Spectra` directly | 35 (18 `Interop/Spectra`, 10 elsewhere, 7 Experimental) |
| tracked upstream Tau Ceti modules | 629 |

**The port surface is 61 declarations, not 464 files or 152 modules.** That is
the single most useful fact in this document: the transitive closure is large
because Spectra's own internal dependencies are large, not because Davis–Kahan
consumes much of it. The mathematics we actually depend on is small enough to
port deliberately, one dependency-closed cluster at a time, with a provenance
record per declaration.

Two structural facts make it cheaper still:

- **`ForTauCeti` and `ForMathlib` are already completely Spectra-free** — not one
  declaration in either library touches a `Spectra.*` constant. The canonical
  layer is clean; all 178 consumers are in `DavisKahan/**`.
- **Spectra's unbounded layer is already on the canonical carrier.**
  `Spectra.Resolvent.resolventSet`, `Spectra.Resolvent.spectrum` and
  `Spectra.OneParameterUnitaryGroup.generator` are all stated over Mathlib's
  `H →ₗ.[ℂ] H`, and `Spectra.Operator.SelfAdjointOperator` is a structure
  *storing* a `LinearPMap`. So U1's representation decision and the Spectra port
  agree; neither has to be undone for the other.

## Where the weight actually is

One declaration dominates: **`Spectra.Resolvent.spectrum`, used 75 times across
26 DKPS modules** — a third of the entire surface. It is a *two-line definition*:

```lean
def resolventSet (A : H →ₗ.[ℂ] H) : Set ℂ := { z | ∃ R : H →L[ℂ] H, … }
def spectrum (A : H →ₗ.[ℂ] H) : Set ℝ := { lam : ℝ | (lam : ℂ) ∉ resolventSet A }
```

in a 90-line file whose only other content is two lemmas placing non-real points
in the resolvent set of a self-adjoint operator. Re-homing that one definition,
with its two lemmas, detaches the largest single block of the surface — and it is
the piece with the sharpest *design* question attached, discussed under Cluster A
below. Do not read "75 uses" as "expensive"; read it as "decide this first,
because everything downstream inherits the decision".

## The clusters

The tables below are a rendering of `spectra-port-surface.json`; the JSON is the
source of truth and also carries, per constant, the list of consuming modules.
Counts are *distinct production declarations referencing the constant*, so a
lemma used once inside a 200-line proof counts once.

#### Cluster A — self-adjoint unbounded operators, resolvent and spectrum

`upstream: partial` · `staged: collides` · 22 constants · 6 donor modules · 1590 donor lines · 31 DKPS consumer modules

| donor module | lines | constants used (uses) |
|---|---|---|
| `Spectra.Resolvent.Spectrum` | 90 | `spectrum` (75), `resolventSet` (6) |
| `Spectra.Operator.SelfAdjoint` | 143 | `toLinearPMap` (20), `SelfAdjointOperator` (10), `selfAdjoint` (10), `domain` (5), `mk` (3), `bornMeasure` (1), `dense` (1), `spectralPVM` (1), `isFormalAdjoint_self_of_isSelfAdjoint` (1) |
| `Spectra.Resolvent.SpecialCases` | 318 | `Rimag` (3), `resolventAtImaginary` (2), `resolventAtNegI` (2), `Rplus` (1), `_proof_1` (1), `_proof_2` (1), `_proof_3` (1) |
| `Spectra.Operator.Unitary.Conjugation` | 191 | `unitaryConj` (4) |
| `Spectra.Operator.Bounded` | 208 | `boundedExtension` (1), `ofBounded` (1) |
| `Spectra.Operator.KatoRellich` | 640 | `perturbedOp` (1) |

#### Cluster B — PVMs, spectral measures and Borel functional calculus

`upstream: absent` · `staged: partial` · 14 constants · 9 donor modules · 1789 donor lines · 13 DKPS consumer modules

| donor module | lines | constants used (uses) |
|---|---|---|
| `Spectra.ProjValMeasure.Basic` | 228 | `ProjValMeasure` (14), `proj` (9), `diag` (2), `mk` (1) |
| `Spectra.SpectralTheory.Measure.Convergence` | 215 | `spectralProjection` (7), `indicator_one_bdd` (1) |
| `Spectra.SpectralTheory.Calculus.Bounded` | 367 | `spectralCalculus` (5) |
| `Spectra.Bochner.Borel.CDF` | 277 | `borelMeasure` (3) |
| `Spectra.SpectralTheory.ResolventForm` | 208 | `spectralPVM` (2), `selfAdjointResolvent` (1) |
| `Spectra.QuantumMechanics.BornRule.PVM` | 144 | `bornMeasure` (2) |
| `Spectra.SpectralTheory.Calculus.SpectralGapInverse` | 224 | `HasVectorSpectralGap` (2) |
| `Spectra.QuantumMechanics.BornRule.Moments` | 62 | `bornExpectation` (1) |
| `Spectra.SpectralTheory.Measure.PVM` | 64 | `spectralPVM` (1) |

#### Cluster C — polar decomposition and partial isometries

`upstream: absent` · `staged: collides` · 3 constants · 1 donor modules · 144 donor lines · 2 DKPS consumer modules

| donor module | lines | constants used (uses) |
|---|---|---|
| `Spectra.QuantumMechanics.Channels.PolarDecomp` | 144 | `absOp` (2), `polarIsometry` (2), `polarRange` (1) |

#### Cluster D — Hilbert-Schmidt, tensor products and trace class

`upstream: absent` · `staged: collides` · 11 constants · 4 donor modules · 1379 donor lines · 4 DKPS consumer modules

| donor module | lines | constants used (uses) |
|---|---|---|
| `Spectra.Spaces.Tensor.HilbertSchmidt` | 625 | `Space` (16), `toOperator` (11), `columnTensor` (4), `ofOperator` (3) |
| `Spectra.SpectralTheory.Antilinear.ConjugateSpace` | 151 | `Conj` (11), `instInnerProductSpace` (11), `instNormedAddCommGroup` (11), `toConj` (1) |
| `Spectra.Spaces.Tensor.Hilbert` | 324 | `HilbertTensor` (1), `tmul` (1) |
| `Spectra.Spaces.Tensor.HilbertSchmidtFlow` | 279 | `sylvesterGroup` (2) |

#### Cluster F — Cayley transform, Stone bridge and one-parameter groups

`upstream: collides` · `staged: absent` · 10 constants · 6 donor modules · 1248 donor lines · 11 DKPS consumer modules

| donor module | lines | constants used (uses) |
|---|---|---|
| `Spectra.YosidaHille.Basic` | 132 | `genToGroup` (22) |
| `Spectra.OneParameterUnitaryGroup.Basic` | 292 | `generator` (6), `OneParameterUnitaryGroup` (5), `U` (4), `genDiffQuot` (2), `mk` (1) |
| `Spectra.CayleyTransform.Generator.InverseAction` | 360 | `cayley` (6) |
| `Spectra.CayleyTransform.Mobius` | 135 | `inverseMobius` (3) |
| `Spectra.CayleyTransform.Generator.Pushforward` | 90 | `inverseMobiusReal` (1) |
| `Spectra.YosidaHille.Helpers` | 239 | `isSelfAdjoint_to_surjective` (1) |

#### Cluster X — DKPS-authored declarations living inside `namespace Spectra.*` — not donor material, and a provenance hazard until re-homed

`upstream: n/a` · `staged: n/a` · 1 constants · 1 donor modules · 0 donor lines · 1 DKPS consumer modules

| donor module | lines | constants used (uses) |
|---|---|---|
| `X` | — | `mathAhead_summable_column_norm_sq` (1) |

**The census undercounts this cluster, by construction.** It reports constants
that *cross declaration boundaries*, and only one of these theorems is consumed
by a sibling declaration; the rest are used only inside the proof that follows
them, so the kernel never records a reference. A source scan of the two files
finds **14** declarations sitting in the donor's namespace — 11 `mathAhead_*`
theorems under `namespace Spectra.HilbertSchmidtTensor`
(`DavisKahan/Interop/Spectra/HilbertSchmidtColumnExpansion.lean:44`) and 3 under
`namespace Spectra.QuantumMechanics.SpectralTheory`
(`DavisKahan/Interop/Spectra/GapResolvent.lean:54`, closing at line 248). Treat
14 as the number to re-home; the census entry is the tripwire, not the count.

## What conflicts with Tau Ceti, and what does not

The word "Tau Ceti" is ambiguous in this repository and the ambiguity is
dangerous here. The `external/TauCeti` **working tree** currently contains 712
`.lean` files, but only **629 are tracked**; the other 83 are an untracked copy
of our own `ForTauCeti/` staging export, written in place by
`scripts/export_for_tauceti.py`. Comparing against the working tree makes our own
staged work look like pre-existing upstream coverage — including for polar
decomposition, Hilbert–Schmidt and approximation numbers, which is exactly where
the port decisions are. Every judgement below is against the **tracked** 629, with
`ForTauCeti` reported separately.

### The one genuine upstream collision: Cluster F (semigroups and generators)

Tau Ceti ships `Analysis/Semigroups/**` — 16 tracked modules with
`StronglyContinuousSemigroup`, a `LinearPMap`-valued `generator`, generator
domains, `resolvent`, resolvent identities, contraction semigroups and power
bounds. Spectra ships the *same idea from the other side*: `OneParameterUnitaryGroup`
(a ℝ-indexed **unitary group**, i.e. Stone), `YosidaHille.genToGroup`, and the
Cayley transform. These are not duplicates, but they are two hierarchies over one
subject, and porting Spectra's verbatim would install the second one permanently.

The concrete conflicts:

- **Two `resolvent`s.** `TauCeti.StronglyContinuousSemigroup.resolvent` is the
  Laplace transform of the semigroup (indexed by a semigroup); `Spectra.Resolvent.resolvent`
  is `(A − z)⁻¹` (indexed by an operator). Different objects, same name, and the
  theorem that links them — Hille–Yosida — is the bridge neither side states.
- **Semigroup vs group.** Tau Ceti's is `ℝ≥0`-indexed and contractive; Spectra's
  is `ℝ`-indexed and unitary. Davis–Kahan needs the group (spectral flow runs
  both directions), so Tau Ceti's object does not simply absorb it.
- **`generator` is defined twice**, over the same carrier, by different limits.

Wave 3 of the convergence matrix already gives the right instruction here — *do
not port that subsystem wholesale; rebuild our proofs on Tau Ceti's objects and
port only the gaps*. This ledger adds the measurement Wave 3 was missing: the
DKPS surface is only **10 constants**, of which `YosidaHille.genToGroup` (22 uses,
10 modules) is the one that matters. That is a Stone-theorem-shaped hole in Tau
Ceti, and it is the right size for a focused upstream addition rather than a
subsystem transplant.

### The one genuine gap: Cluster B (PVMs and Borel calculus)

Tracked Tau Ceti has **no** projection-valued measures, no spectral measure, no
Borel functional calculus, no spectral projections for unbounded operators.
Spectra is a real donor here and this cluster needs **its own roadmap target** —
it cannot ride the approximation-number roadmap.

Two near misses must not be mistaken for coverage, which is why this cluster is
`staged: partial` rather than `staged: absent`:

- `ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean` is
  built on `eigenvectorBasis` — **finite-dimensional**.
- `ForTauCeti/Analysis/InnerProductSpace/SpectralCutoff.lean` is CFC over
  **bounded positive** `E →L[ℂ] E`.

Neither reaches the unbounded, measure-theoretic generality the Davis–Kahan
unbounded sin-Θ theorems consume. Anyone who greps for "functional calculus" in
`ForTauCeti` and concludes the cluster is covered will be wrong.

### Already-resolved collisions: Clusters C and D

These collide with **`ForTauCeti`, not upstream**, and the reconciliation has
largely happened:

- **C (polar).** `ForTauCeti` owns `PolarDecomposition`, `PolarIsometry`,
  `PolarPartialIsometry`, `PartialIsometry`, `OperatorModulus`. Per
  [`LANES.md`](../LANES.md) the Spectra polar consumers are *already repointed*
  and `operatorAbs` is deleted. Residual surface: **3 constants** (`absOp`,
  `polarIsometry`, `polarRange`), only in `Interop/Spectra/OperatorAbsoluteValue.lean`
  and one consumer. This cluster is nearly closed.
- **D (Hilbert–Schmidt).** `ForTauCeti` owns `HilbertSchmidtEnergy`,
  `SchattenNorm`, `OperatorIdeal/Family/{HilbertSchmidt,TraceClass}`. What
  Spectra still supplies is the **tensor model** — `HilbertSchmidtTensor.Space`,
  `toOperator`, `columnTensor`, and the antilinear `Conj` space (11 uses of the
  conjugate-space instances alone). Wave 5's instruction stands: one canonical HS
  object, everything else becomes an equivalence theorem. The `Conj` dependency is
  the sharp bit — three instance constants (`Conj`, `instInnerProductSpace`,
  `instNormedAddCommGroup`) are load-bearing in four modules, and Mathlib's
  conjugate-space support is what determines whether they port or dissolve.

### Cluster A: the decision that gates everything

`upstream: partial` — Tau Ceti has semigroup resolvents but no spectrum for an
unbounded operator; `staged: collides` — `ForTauCeti/.../LinearPMap/Closed.lean`
(935 lines) owns the closed-operator layer and `LinearPMap/Sylvester.lean` the
equation layer.

The design question, and it must be settled before anything is ported:

> **`Spectra.Resolvent.spectrum` returns `Set ℝ`, not `Set ℂ`.**

That is a deliberate choice suited to self-adjoint operators, and it is at odds
with Mathlib's `spectrum 𝕜 a : Set 𝕜` convention. Every one of the 75 uses
inherits it. A Tau Ceti PR proposing a real-valued `spectrum` for a complex
`LinearPMap` will be asked why, and "the donor did it" is not an answer. The two
defensible outcomes are a `Set ℂ` spectrum plus a self-adjointness lemma placing
it in `ℝ`, or a separate `realSpectrum` abbreviation over the canonical complex
one. **Decide this before porting Cluster A**, because it is a 26-module rewrite
either way, and doing it twice is the expensive failure mode.

Note also that `Spectra.Operator.SelfAdjointOperator` is a **bundled structure over
`LinearPMap`** — precisely the shape U1 spent this month removing from DKPS in
favour of "raw `LinearPMap` + property predicates". Porting it verbatim would
re-introduce the pattern U1 deleted. Per Wave 5 Cluster A: port the lemmas, not
the wrapper.

## Provenance: what has to be recorded, and what currently defeats it

The eventual removal of Spectra makes attribution *more* important, not less —
once the imports are gone, nothing in the build points at the donor. The
per-declaration record required by
[`tauceti-adaptation-and-spectra-extraction.md`](../../docs/planning/tauceti-adaptation-and-spectra-extraction.md)
("Spectra provenance policy") is the right schema. `spectra-port-surface.json`
supplies its first four fields mechanically — donor module, donor declaration,
use count, DKPS consumer modules — so the ledger cannot be written from memory.

What it does **not** supply, and a human must: the classification
(copied / ported / generalized / specialized / redesigned) and the semantic
delta. Note that the policy is explicit that *a proof rewritten from scratch may
still owe attribution when the theorem selection or proof architecture came from
Spectra* — so "I reproved it" does not discharge the record.

Three concrete hazards found while measuring, all of which corrupt attribution if
left until port time:

1. **DKPS theorems are being declared inside the donor's namespace.**
   `DavisKahan/Interop/Spectra/HilbertSchmidtColumnExpansion.lean:44` opens
   `namespace Spectra.HilbertSchmidtTensor` and declares **11 `mathAhead_*`
   theorems** into it; `.../GapResolvent.lean:54` opens
   `namespace Spectra.QuantumMechanics.SpectralTheory` and declares 3 more. These
   are **ours**, and after a port they are indistinguishable from donor material
   by name. The census flags them as cluster `X` precisely because they are the
   one thing in the surface that must *not* be attributed to Spectra.
   `LANES.md` already records the rule ("nothing outside `vendor/` should declare
   into `namespace Spectra`") and notes a gate was wanted; it does not exist yet.
2. **One vendored file carries an edit not recorded in the compatibility patch.**
   `vendor/Spectra/Spectra/Spaces/Tensor/Hilbert.lean` differs from upstream (a
   genuine and well-commented `notation`-elaboration fix), but
   `vendor/patches/Spectra/0001-*.patch` does not list the file. `Spectra.UPSTREAM.md`
   requires the snapshot to be byte-identical to upstream with all deltas in the
   managed patch. This is a documentation defect, not a mathematical one, but it is
   exactly the kind that makes a later "what did we change?" question unanswerable.
3. **The Spectra toggle scripts are stale and would silently no-op.**
   `scripts/{enable,disable}_spectra_lake_dependency.py` search for the markers
   `# BEGIN local Spectra development dependency`; `lakefile.toml` has said
   `# BEGIN vendored upstream Spectra snapshot` for some time, so `disable` prints
   "Spectra Lake dependency was not enabled" and changes nothing.
   `scripts/check_spectra_parent_only_bridge.sh` invokes two scripts that no longer
   exist and builds `DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.*`
   modules that are gone. Anyone reaching for these to verify a de-Spectra step
   will get a false pass.

## Recommended order

Dependency order, not size order. Each step is independently green and
independently reviewable.

1. **Settle the `spectrum` codomain** (`Set ℂ` vs `Set ℝ`). Documentation only;
   gates Cluster A and therefore 26 of the 31 Cluster-A consumer modules.
2. **Fix the three provenance hazards above** — re-home the 14 DKPS theorems out
   of `namespace Spectra.*`, record the `Hilbert.lean` delta in the managed patch,
   and either repair or delete the stale toggle scripts. Cheap, and it is the work
   that stops being possible once the port starts.
3. **Cluster A core**: `Resolvent/Spectrum.lean` (90 lines, 2 defs, 2 lemmas) to a
   canonical Tau Ceti location under the settled convention. Largest single
   detachment on the surface.
4. **Cluster C closeout** (3 constants) — nearly done already.
5. **Cluster F**: rebuild on Tau Ceti's `Analysis/Semigroups`, then propose
   Stone's theorem (`genToGroup`) as a focused upstream addition. Blocks the
   unbounded Sylvester theory, per Wave 3.
6. **Cluster D**: one canonical HS object; resolve the antilinear `Conj`
   dependency against Mathlib.
7. **Cluster B last, with its own roadmap.** It is the only cluster where Spectra
   is a genuine donor with no counterpart anywhere, it is the largest
   (1,789 donor lines), and it needs coordination with Spectra's author before a
   line of it moves.

## Out of scope for this ledger

`DavisKahan/Experimental` (outside `defaultTargets`), the 405-module
`external/Spectra` reference checkout, and the 152-module transitive closure that
production does not reference. None of those are port obligations.
