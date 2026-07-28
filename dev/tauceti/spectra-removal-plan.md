# Spectra removal execution contract

**Goal (AGENTS.md, "Intermediate dependency policy"):** *the final migration
target removes Spectra from the normal build.* This document is the execution
contract for getting there. It is the Spectra counterpart of
[`u1-linearpmap-migration.md`](u1-linearpmap-migration.md).

**Do not re-measure the surface.** It is measured, generated and drift-gated in
[`spectra-to-tauceti-port-ledger.md`](spectra-to-tauceti-port-ledger.md) +
[`spectra-port-surface.json`](spectra-port-surface.json). Read those first; this
document assumes them and states only what to *do*.

## Decision

Spectra leaves the normal build by **re-homing the remaining 57 declarations**, cluster by
cluster, each cluster landing green, with a per-declaration provenance record.
It does not leave by a bulk copy of `vendor/Spectra` into Tau Ceti, and it does
not leave by reproving everything from scratch — the attribution policy in
`docs/planning/tauceti-adaptation-and-spectra-extraction.md` is explicit that a
proof rewritten from scratch still owes attribution when the theorem selection or
proof architecture came from Spectra.

## Baseline (2026-07-28)

| | |
|---|---|
| port surface | **56 constants**, 25 donor modules (was 61 / 27 before S0) |
| consumers | **97 declarations** (was 178), all under `DavisKahan/**` |
| `ForTauCeti` / `ForMathlib` | **already entirely Spectra-free** |
| vendored tree | 464 modules; 152 in the production closure; 27 referenced |
| default build | 9290 jobs green |

## The gating decision — settle before writing any Lean

**`Spectra.Resolvent.spectrum` returns `Set ℝ`, not `Set ℂ`.**

It is a two-line definition over `H →ₗ.[ℂ] H` with 75 uses in 26 modules — a
third of the whole surface — and Mathlib's convention is `spectrum 𝕜 a : Set 𝕜`.
A Tau Ceti PR proposing a real-valued spectrum for a complex `LinearPMap` will be
asked to justify it, and "the donor did it" is not a justification.

**DECIDED 2026-07-28 (jon): canonical `Set ℂ`, plus a real-containment lemma for
self-adjoint operators. No `realSpectrum` abbreviation.**

```lean
def spectrum (A : H →ₗ.[ℂ] H) : Set ℂ
theorem spectrum_subset_real (hA : IsSelfAdjoint A) : spectrum A ⊆ Complex.ofReal '' Set.univ
```

Rationale: it is the form a Tau Ceti reviewer will expect, because it is
Mathlib's (`spectrum 𝕜 a : Set 𝕜`). The cost is a coercion at the DK call sites —
`(lam : ℂ) ∉ spectrum A` where they currently read `lam ∉ spectrum A` — which is
mechanical. The rejected alternative (shipping `realSpectrum : Set ℝ` alongside)
would have kept the call sites unchanged at the price of a second name for one
object, which is the kind of parallel API the convergence matrix exists to
eliminate.

This is a 26-module rewrite. **Doing it twice is the expensive failure mode**,
which is why it was settled before phase S2 rather than during it.

## Ordering is forced by chokepoints, not by cluster size

30 of the 42 consumer modules depend on exactly **one** cluster and can be freed
independently. 12 are chokepoints spanning several:

| consumer module | clusters it depends on |
|---|---|
| `Interop.Spectra.BoundedSelfAdjointSpectralProjection` | A, B, F |
| `Interop.Spectra.GapResolvent` | A, B, F |
| `Interop.Spectra.SpectralRestrictionLocalization` | A, B, F |
| `SpectralTheory.CayleySelectorBridge` | A, B, F |
| `SpectralTheory.SelfAdjointBorelCalculus` | A, B, F |
| `Sources.DavisKahan1970.Sylvester.HilbertSchmidtDefectFirst` | B, D, F |
| `Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise` | B, D, F |
| `Interop.Spectra.BoundedTruncation` | B, F |
| `Interop.Spectra.SpectralCutoff` | B, F |
| `Interop.Spectra.SpectralRestriction` | B, F |
| `Interop.Spectra.OrderedHalfLine` | A, B |
| `Interop.Spectra.SpectralRestrictionOperator` | A, F |

**Cluster F has no single-cluster consumers at all.** Every module that needs
Stone/Cayley material also needs A or B. So F *cannot* be closed on its own, and
the intuitive order — "do the small collision-heavy cluster early" — is wrong.
B is the deepest chokepoint; B and F converge at the end, together.

Single-cluster consumer counts: **A 24, B 2, C 2, D 2.** Cluster A alone frees
more than half the surface.

## Phases

### S0 — decisions and provenance preservation (no mathematics)

Cheap now, impossible later. Nothing else starts until this lands.

1. **Settle the `spectrum` codomain** (above). Record the decision and its reason
   in this file; it is a one-paragraph edit and a permanent constraint.
2. **Re-home the 14 DKPS-authored theorems out of `namespace Spectra.*`.**
   - `DavisKahan/Interop/Spectra/HilbertSchmidtColumnExpansion.lean:44` —
     11 `mathAhead_*` theorems under `namespace Spectra.HilbertSchmidtTensor`;
   - `DavisKahan/Interop/Spectra/GapResolvent.lean:54–248` — 3 theorems under
     `namespace Spectra.QuantumMechanics.SpectralTheory`.

   These are **ours**. Once Spectra's imports are gone, nothing distinguishes
   them from donor material by name, and the attribution ledger will credit
   Spectra for our theorems. `LANES.md` already records the rule — *nothing
   outside `vendor/` should declare into `namespace Spectra`* — but no gate
   enforces it. **Add the gate with the fix**, or it recurs.
3. **Get our own mathematics out of `vendor/Spectra` — 11 files, 2,589 lines.**
   `scripts/spectra_compatibility_patch.py status` reports `diverged`: the tree
   differs from the recorded patch by 172,661 bytes against 23,378 recorded.
   20 files sit outside the managed patch — 9 upstream files edited, and **11
   that do not exist upstream at all**, carrying a `Spectra Formalization
   Project` copyright and `Authors: Jon Crall, OpenAI GPT-5.6 Thinking`.
   Inventory and ratchet:
   [`spectra-vendor-authorship-baseline.json`](spectra-vendor-authorship-baseline.json)
   / `scripts/check_spectra_vendor_authorship.py`.

   **This is the largest provenance hazard in the repository, and it is also the
   piece of good news in the campaign.** Bad: a file under `vendor/` reads as the
   donor's work, three of these are load-bearing in the port surface (6 of the 61
   constants), and step 3 of `Spectra.UPSTREAM.md` — "replace `vendor/Spectra/`
   with `git archive <new-upstream-commit>`" — deletes all 2,589 lines if anyone
   follows the documented update procedure. Good: these modules need **no port
   and no donor coordination**. They are ours already; they move to `ForTauCeti`
   and get reconciled against Tau Ceti's API like any other staged module.

   **Do not "fix" this with `spectra_compatibility_patch.py refresh`.** The patch
   is documented as compatibility-only and explicitly "not the place for
   Davis–Kahan-specific mathematical APIs"; refreshing would launder our
   mathematics into a compatibility record and make the problem invisible rather
   than smaller. The 9 genuine compatibility edits *should* be recorded that way;
   the 11 files should leave.

   **Verified against the whole public history, not just the pin.** None of the
   11 exists at *any* commit on *any* branch of `external/Spectra` (82 commits;
   `origin/master` is not ahead of the pinned `8dbaaf67`). They are not a newer
   upstream revision that drifted in. Authorship splits three ways and the
   difference matters for what may be submitted upstream:

   | authorship (from the file headers) | files |
   |---|---|
   | Jon Crall + OpenAI GPT-5.6 Thinking | 7 |
   | Adam Bornemann + Jon Crall + GPT-5.6 | 3 |
   | Adam Bornemann alone (`BornRule/POVMCore.lean`, 378 lines) | 1 |

   **Licensing: there is no permission problem.** Every one of the 11 carries
   `Released under Apache 2.0 license as described in the file LICENSE`, and
   `vendor/Spectra/LICENSE` is the real Apache License 2.0. Apache-2.0 §2 grants
   a perpetual, worldwide, irrevocable licence to reproduce, prepare derivative
   works of, and distribute the work. DKPS and Tau Ceti are both Apache-2.0 too,
   so there is no compatibility question either. **No sign-off is required to
   relocate these or to submit them upstream.** Telling Adam is a courtesy, and
   worth doing because Spectra is a live collaboration — but it is not a gate.

   What Apache-2.0 *does* require, and what this campaign is uniquely likely to
   get wrong, is §4:

   - **§4(b) — modified files must carry prominent notices stating you changed
     them.** Reshaping a file into a new library's house style is a modification.
   - **§4(c) — retain all copyright and attribution notices from the source.** So
     `Copyright (c) 2026 Spectra Formalization Project` and the `Authors:` line
     must survive relocation.
   - §4(a) ship the licence (Tau Ceti already does); §4(d) N/A — Spectra has no
     `NOTICE` file.

   §4(c) is the trap. **Tau Ceti's header convention has no `Authors:` line** —
   its files read `Copyright (c) 2026 The Tau Ceti contributors` and stop. Porting
   one of these into that template verbatim silently drops the attribution the
   licence requires. Put the retained notice in the module's `## Provenance`
   section, which this repository already uses for exactly this.

   `POVMCore.lean` is also the only one with a structural complication: two
   upstream files (`BornRule/POVM.lean`, `BornRule/Joint/Defs.lean`) import it,
   and comparing them with upstream shows `POVM.lean` was **split** here — the
   vendored copy is materially shorter and delegates to `POVMCore`. That is a
   genuine fork of an upstream file, not a compatibility repair, so it cannot be
   unpicked by moving one file. Do `POVMCore` last, as its own step.

   **DECIDED 2026-07-28 (jon): relocate all 11 to `ForTauCeti`**, with DKPS
   authorship restored and reconciled against Tau Ceti's API like any other
   staged module — rather than moving only the three in the port surface, or
   documenting and leaving them. Leaving them would mean `vendor/Spectra` can
   never be deleted at S6 and the attribution stays inverted.

   **Ordering correction, measured 2026-07-28 — the relocation is *gated*, not
   independent.** "They need no port" is true of their *authorship* and false of
   their *dependencies*: **all 11 import genuine upstream Spectra modules**, and
   `ForTauCeti` may import only Mathlib / TauCeti / ForTauCeti
   (`scripts/check_dependency_layers.py`). So none of them can land in
   `ForTauCeti` until its donor dependencies are ported. Measured deps:

   | file | upstream Spectra deps |
   |---|---|
   | `Spaces/Tensor/HilbertSchmidt.lean` | 4 — `Tensor.Map`, `Antilinear.ConjugateSpace`, `Operator.AdjointClosure`, `BornRule.Joint.Basic` |
   | `YosidaHille/RectangularIntertwining.lean` | 3 |
   | `SpectralTheory/SeparatedIntertwiner.lean` | 3 |
   | `Spaces/Tensor/HilbertSchmidtSpectralGap.lean` | 2 |
   | the remaining 7 | 1 each, or 0 plus a sibling of ours |

   Two consequences. First, **S0.3 cannot be finished before S4** — the
   Hilbert–Schmidt tensor files sit on the PVM/Born-rule layer, which is Cluster
   B. Second, if the deletion risk needs defusing sooner, there is a cheaper
   intermediate: move the 11 out of `vendor/Spectra` into
   `DavisKahan/Interop/Spectra/`, which *is* allowed to import Spectra. That ends
   the attribution inversion and takes them out of reach of the `git archive`
   refresh immediately, at the cost of renaming their namespaces (they are
   declared into `Spectra.*`, so consumers move with them). The ratchet in
   `check_spectra_vendor_authorship.py` measures either route.

   Sequencing note: `Spaces/Tensor/HilbertSchmidt.lean` (625 lines) is the
   biggest and is Cluster D's core, so this step and S3 are the same work — do
   the relocation as part of S3 rather than twice.
4. **Retire the stale toggle scripts.** All three encoded the pre-vendoring
   architecture and are now loud-failing stubs (kept as files because historical
   `dev/` notes reference the paths; deleting them would dangle those records).
   Measured behaviour before the fix — they differed, and only one was dangerous:

   - `disable_spectra_lake_dependency.py` **exited 0 while changing nothing**
     (wrong marker), so a "disable Spectra and confirm the build" check passed
     without disabling anything. For a campaign about removing this dependency,
     a verification step that silently succeeds is the worst failure available.
   - `enable_spectra_lake_dependency.py` was worse than inert: it inserts
     `path = "external/Spectra"`, repointing the build at the read-only
     provenance submodule and undoing the vendoring architecture.
   - `check_spectra_parent_only_bridge.sh` exited 2 on a missing script — loud,
     dead, not hazardous.

### S1 — Cluster C closeout (polar), 3 constants — **DONE 2026-07-28**

Surface **60 → 57 constants**, 26 → 25 donor modules, 178 → 173 consumers.

`Interop/Spectra/OperatorAbsoluteValue.lean` already proved
`spectraOperatorAbsoluteValue = T.modulus` and
`spectraPolarIsometry = T.polarPartial` against `ForTauCeti`, so the work was
to make those the *definitions* rather than theorems: the two bridge lemmas
collapse to `rfl` and the `Spectra.QuantumMechanics.Channels.PolarDecomp` import
is gone. `absOp`, `polarIsometry` and `polarRange` left the surface, and
`Geometry/Polar/PolarIntertwining.lean` came off Spectra with them without being
edited at all — its dependency was inherited through the bridge.

Two things worth carrying forward:

- **`ForTauCeti`'s polar API is strictly more general than the donor's**
  (rectangular `E →L[ℂ] F`, not square), so this was a strict improvement rather
  than a like-for-like swap. Where a cluster has a `staged: collides` disposition,
  check which side is more general before assuming the donor is the richer one.
- **Orientation bites.** `polarPartial_adjoint` is stated `W(M⋆) = W(M)⋆` while
  the bridge name is stated the other way round; the fix is `.symm`, but it is the
  kind of mismatch that reads as a broken port if you are not expecting it.

Deliberately **not** done: the `spectra*` names are now misnomers with ~400 call
sites across ten modules. Renaming them is a naming-audit sweep that would
collide with edward's active naming rows, so it is a follow-on, not part of the
dependency removal. Tracked below under "Follow-ons".

### S2 — Cluster A core, 22 constants, 31 consumer modules — **step 1 DONE**

Under the S0 decision. Order inside the cluster:

1. **`Resolvent/Spectrum.lean` — DONE 2026-07-28.** Re-homed to
   `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Resolvent.lean` as
   `TauCeti.LinearPMap.{resolventSet,spectrum}`, `Set 𝕜` per the S0 decision,
   generalised from `ℂ`/inner-product to `NontriviallyNormedField`/normed space
   (nothing in the definitions used the inner product). **Consumers 173 → 97**;
   `spectrum` went from 75 uses in 26 modules to 0.

   Three things worth knowing before the next cluster:

   - **The faithful translation of a real-set inclusion is the *preimage*, not the
     image.** `spectrum A ⊆ Set.Icc β α` over `Set ℝ` becomes
     `Complex.ofReal ⁻¹' spectrum A ⊆ Set.Icc β α`, not
     `spectrum A ⊆ Complex.ofReal '' Set.Icc β α`. The image form silently asserts
     the spectrum is real, which *strengthens hypotheses* (weakening the theorem)
     and makes conclusions unprovable. I wrote the image form first and it broke
     `Sylvester/Unbounded/LegacyGap.lean` — correctly, because that implication
     genuinely needs realness.
   - **One place does need realness**, and it is where a `Set ℂ` gap predicate is
     built from a real-points hypothesis
     (`Sources/.../HilbertSchmidtPairwise.lean`). The canonical statement
     `spectrum_subset_real_of_isSelfAdjoint` now lives in
     `Interop/Spectra/RealSpectrumBridge.lean` with a **canonical statement and a
     borrowed proof** — it still routes through
     `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`, because the native proof
     needs `±i` deficiency-surjectivity from Spectra's Yosida–Hille layer (phase
     S5). Isolating it there keeps the remaining dependency to *one lemma in one
     file* instead of 26 modules.
   - `GenuinePairwiseSpectrumGap` improved rather than merely moved: separation is
     now `‖lam - α‖` in `ℂ`. The old real version was not the honest condition —
     two operators with separated real slices but colliding complex spectra
     satisfied it.
2. `Resolvent/SpecialCases.lean` and `Operator/Unitary/Conjugation.lean` — used
   only by `CayleySelectorBridge` and `UnitaryConjugation`; they can wait for F.
3. `Operator/SelfAdjoint.lean` — **port the lemmas, not the wrapper.**
   `SelfAdjointOperator` is a bundled structure *storing* a `LinearPMap`, i.e.
   exactly the pattern U1 is deleting from DKPS. Re-introducing it upstream
   would undo U1's architecture at the moment it completes.
4. `Operator/Bounded.lean`, `Operator/KatoRellich.lean` — one constant each
   (`ofBounded`/`boundedExtension`, `perturbedOp`); trivial once 3 lands.

Coordinate with the U1 lane: A's canonical carrier is `LinearPMap`, so A and U1
agree by construction, but they touch overlapping consumer modules.

### S3 — Cluster D (Hilbert–Schmidt), 11 constants

Two single-cluster consumers (`Interop/Spectra/HilbertSchmidt{ColumnExpansion,Tensor}.lean`)
can be freed immediately; the two `Sources/**` consumers are B/D/F chokepoints
and wait for S5.

Wave 5's rule stands: **one** canonical HS object; basis-column, tensor,
approximation-number and finite-Frobenius characterisations become equivalence
theorems for it. The sharp dependency is the antilinear conjugate space —
`Spectra.Conj` and its two instances are load-bearing in four modules, and
whether they port or dissolve depends on Mathlib's conjugate-space support.
Settle that before touching the tensor model.

### S4 — Cluster B (PVM and Borel calculus), 14 constants — needs its own roadmap

The only cluster where Spectra is a genuine donor with no counterpart anywhere:
tracked Tau Ceti has no PVMs, no spectral measure, no Borel functional calculus,
no spectral projections for unbounded operators. 1,789 donor lines, the largest
cluster.

**Two near misses that are not substitutes** — anyone who greps `ForTauCeti` for
"functional calculus" and concludes this is covered will be wrong:

- `ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean` is
  built on `eigenvectorBasis` — **finite-dimensional**;
- `ForTauCeti/Analysis/InnerProductSpace/SpectralCutoff.lean` is CFC over
  **bounded positive** `E →L[ℂ] E`.

Per Wave 5: identify the minimal DK-needed slice → **coordinate with Spectra's
author** → port dependency-closed modules to canonical Tau Ceti locations →
preserve license and declaration provenance → rewrite the DKPS bridges → remove
the imports. This cannot ride the approximation-number roadmap.

### S5 — Cluster F (Stone, Cayley, one-parameter groups), 10 constants

Lands with or after S4, because F has no independent consumers.

The **one genuine upstream collision.** Tau Ceti ships `Analysis/Semigroups/**`
(16 tracked modules): `StronglyContinuousSemigroup`, a `LinearPMap`-valued
`generator`, generator domains, `resolvent`, resolvent identities, contraction
semigroups, power bounds. Spectra ships the same subject from the other side:
`OneParameterUnitaryGroup` (ℝ-indexed, unitary — Stone), `YosidaHille.genToGroup`,
the Cayley transform.

Concretely conflicting:

- **two `resolvent`s** — TauCeti's is the semigroup Laplace transform (indexed by
  a semigroup); Spectra's is `(A − z)⁻¹` (indexed by an operator). Different
  objects, same name; the theorem linking them is Hille–Yosida, which neither
  side states.
- **semigroup vs group** — TauCeti's is `ℝ≥0`-indexed and contractive, Spectra's
  is `ℝ`-indexed and unitary. Davis–Kahan needs the group (spectral flow runs
  both directions), so TauCeti's object does not simply absorb it.
- **`generator` defined twice** over the same carrier by different limits.

Wave 3's instruction is right and this is the measurement it lacked: **do not
port the subsystem.** Rebuild our proofs on TauCeti's objects; the DKPS surface
is 10 constants dominated by `YosidaHille.genToGroup` (22 uses, 10 modules) —
a Stone-theorem-shaped hole in Tau Ceti, sized for one focused upstream addition.

### S6 — removal and proof of completion

Not done until all of:

1. no `.lean` file outside `vendor/` and `external/` contains `import Spectra`;
2. no production declaration references a `Spectra.*` constant —
   `scripts/ExportSpectraUsage.lean` emits **zero** lines;
3. the `[[require]] Spectra` block is gone from `lakefile.toml` and the build is
   green without it;
4. `vendor/Spectra/`, `external/Spectra/`, the compatibility patch and the
   Spectra scripts are deleted **or** explicitly retained as provenance-only with
   a stated reason;
5. the per-declaration provenance ledger covers all 61 constants with a
   copied/ported/generalized/specialized/redesigned classification and semantic
   delta, and survives the removal of the code it describes.

(5) is the one that cannot be reconstructed afterwards. It is the deliverable
this campaign exists to protect.

## Provenance record — the required schema

Per `docs/planning/tauceti-adaptation-and-spectra-extraction.md`, every re-homed
declaration carries: original repository and commit (`8dbaaf67…`); original path
and declaration name; author and license (Apache-2.0); local name and destination
module; classification (copied / ported / generalized / specialized / redesigned);
semantic differences from the donor statement; downstream DKPS users; Tau Ceti
target and upstream status.

`spectra-port-surface.json` supplies the first four and the downstream-user list
**mechanically**, so no row is written from memory. Classification and semantic
delta are human judgements and must be recorded at the time of the port, not
reconstructed.

## Gates (every phase)

```bash
lake build                                        # default targets, 9290 jobs
lake build Challenge                              # outside defaultTargets
python3 scripts/check_dependency_layers.py
python3 scripts/check_declaration_name_drift.py   # required for any rename
python3 scripts/check_library_structure.py
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_spectra_namespace.py        # S0.2 — nothing in namespace Spectra.*
python3 scripts/check_spectra_vendor_authorship.py # S0.3 — ratchet, target 0
python3 scripts/spectra_port_surface.py build/spectra_direct_uses.jsonl --check
```

The last one is the campaign's own progress meter: the constant count must fall
monotonically, and `--check` failing means the ledger no longer describes the
tree.

Renames additionally require `lake build Challenge` and the name-drift script,
because `comparator/*.json` stores declaration names as data — see AGENTS.md,
"Comparator challenge rule".

## Out of scope

- `DavisKahan/Experimental/**` — outside `defaultTargets`; 7 of the 35 direct
  importers live there and are not removal obligations.
- The 125 closure modules production never references.
- `external/Spectra` as a provenance reference (it is not a build input).
- Any change to Spectra's own mathematics. Compatibility-only edits go in the
  managed patch, never as an undocumented fork.

## Follow-ons (not part of the dependency removal)

- **Rename the `spectra*` bridge names.** After S1 they no longer denote anything
  Spectra-backed: `spectraOperatorAbsoluteValue` (105 occurrences, 9 files),
  `spectraCanonicalIntertwiner` (285, 8 files), `spectraPolarIsometry` (18, 4
  files). This is a naming-audit sweep and overlaps edward's active naming rows —
  coordinate before taking it. Keeping the misnomers is survivable; doing the
  rename inside a dependency-removal commit is not, because it would make the
  removal impossible to review.

## The strategy that actually works (measured 2026-07-28)

**Do not bulk-port the closure.** If the four remaining clusters are ported by
following their imports, the job is **112 vendored modules / 28,364 lines** —
Cluster A's closure alone is 17,568 lines, Cluster D's 22,492, and they overlap
heavily. That is a Mathlib-scale contribution, and almost none of it is
mathematics Davis--Kahan needs.

**Port the *endpoint*, at the right altitude.** The worked example is phase S2's
gap-resolvent bound:

| | |
|---|---|
| what DK consumes | "spectrum avoids `(c-s, c+s)` ⟹ `‖(A-c)⁻¹‖ ≤ s⁻¹`" |
| Spectra's route | Stone's theorem → unitary group → PVM → bounded Borel calculus → truncated symbol |
| closure if ported | thousands of lines |
| what it actually is | a C⋆-algebra fact about the **bounded** operator `R` |
| native replacement | ~350 lines in `ForTauCeti/…/LinearPMap/{Resolvent,ResolventBound,SelfAdjointResolvent}.lean` |
| effect | the whole sin-Θ / tan-2Θ chain came off Spectra; consumers 173 → 95 |

The pattern generalises: **Spectra is a general-purpose spectral-theory library,
so it proves DK's facts as corollaries of a much heavier apparatus.** Asking
"what is this statement really about?" repeatedly finds it is about a bounded
operator, where Mathlib is strong.

### What Mathlib does and does not have (checked, not assumed)

* **Has:** continuous functional calculus (`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/**`),
  `IsSelfAdjoint.spectralRadius_eq_nnnorm`, the `LinearPMap` adjoint API, and
  `CStarAlgebra (E →L[ℂ] E)` — the last in
  `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`, which must be imported
  explicitly or instance search **diverges** rather than failing (symptom: a
  `whnf` timeout at 10⁶ heartbeats, not an unsolved instance goal).
* **Does not have:** any Borel functional calculus, projection-valued measures,
  or spectral projections onto Borel sets, for bounded *or* unbounded operators.

That gap is real, and it is where the remaining work concentrates.

### The one place the bypass will not reach

`selfAdjointSpectralProjection A hA B hB` — the spectral projection of a
self-adjoint operator onto a **Borel set** — is consumed by 15 production
modules, and it is irreducibly a spectral-theorem statement. There is no
bounded-operator reformulation, because the object *is* the spectral measure.
For this cluster Spectra is a genuine donor and the port is a port: adapt the
dependency-closed slice into `ForTauCeti` with declaration-level provenance,
under Apache-2.0 §4(b)/(c). Everything else should be attacked with the bypass
first, and only ported when the bypass demonstrably fails.
