# Palomar readiness — campaign contract

**Status: preparation only. Nothing here claims registration, approval, acceptance,
or peer review by the Palomar Registry.**

This document is the durable execution contract for preparing Palomar Registry
submissions from this repository. It is written to survive context compaction: an
agent resuming with no memory of the conversation should be able to read this file
and continue correctly.

Written 2026-08-28. Palomar is young and its policy moves; **re-read the live
sources in §2 at the start of any resumed session and again immediately before
final verification.** Where this file and live policy disagree, live policy wins
and this file is wrong.

---

## 1. Decisions already taken (maintainer, 2026-08-28)

These were decided by the maintainer and are not open for an agent to revisit.

| # | Decision |
| --- | --- |
| D1 | **Hybrid submodule strategy.** Use the Palomar work to make `main` cleaner. Each Palomar submission gets its own branch; the branch delta must stay small and trivially forward/backward portable. |
| D2 | **Submission repos are extracted.** Branches will most likely be lifted into their own standalone GitHub repositories for the actual submission. Everything is prepared here. |
| D3 | **Add both Palomar tooling scripts, no CI.** `scripts/check_palomar_readiness.py` and `scripts/verify_palomar.sh`. This is an explicit maintainer exception to the AGENTS.md rule against new `scripts/check_*.py`. No GitHub Actions workflow. |
| D4 | **Two entries now; all DKPS results brought to Palomar-worthy state.** Prepare submission entries for **Davis–Kahan 1970** and **Yu–Wang–Samworth 2015** only — those go first, on their own. Do **not** prepare Palomar entries, Challenge modules, or entry metadata for Acharyya 2024, Acharyya 2025, Helm 2025 or Quench 2026 this run. But **do** bring all four DKPS packages to the state where such an entry could be made later, by us or by JHU (§6.3). Revised by the maintainer 2026-08-28 after the initial "classical only" answer. |
| D5 | **Authorship.** `project.authors: [Jon Crall, Edward Wang]`. `project.responsible_maintainers: [Jon Crall]`. Basis: maintainer instruction. AI models are disclosed under `automation`, never as authors. |

**The agent must not submit.** Do not call the submission API, do not open the
submission form, do not push authentication tags or gists on the maintainer's
behalf, do not create a registry entry. Preparation and local verification only.

---

## 2. Live sources — re-read these, do not trust this file for mechanics

- How to submit — <https://palomar-registry.org/how-to-submit>
- Policy / CONTRIBUTING — <https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md>
- Starter template — <https://github.com/PalomarRegistry/PalomarTemplate>
  (`formalization.yaml`, `comparator.json`, verification scripts)
- Minimum toolchain — <https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json>
- `formalization.yaml` v0.4 schema — <https://github.com/mathlib-initiative/formalization.yaml>
  (`schema/v0.4.schema.json`)
- Announcement — <https://terrytao.wordpress.com/2026/08/18/palomar-a-registry-of-lean-verified-mathematics/>

---

## 3. Requirements, as verified on 2026-08-28

### 3.1 Required files in the selected project directory

```
lean-toolchain            pinned to a supported release or RC
lakefile.toml | .lean     exactly one; .lean requires a committed manifest
lake-manifest.json        committed (strongly recommended even for .toml)
Challenge.lean            statement module, conventionally named
Solution.lean             proof module, conventionally named
comparator.json           Comparator configuration
formalization.yaml        v0.4 metadata
LICENSE                   one, at repository root, SPDX matching project.license
```

### 3.2 Challenge module — the strict part

Its **transitive import closure** may contain only Lean core, the pinned allowlisted
Mathlib, Tau Ceti, or CSLib. **No `ForTauCeti`, `DavisKahan`, `YuWangSamworth2015`,
`Acharyya*`, `Helm2025`, `DkpsQuench2026`, `RoadmapBridge`, or other local module.**
Prefer plain `import Mathlib`. Importing Tau Ceti is permitted but enlarges the
recorded trust surface — do not do it for convenience.

Hard cap 1,000 lines and 100 KiB; warnings at 300 lines / 32 KiB; aim well under the
warning band. Prefer theorem statements to new definitions. Any definition needs a
precise docstring giving its ordinary mathematical meaning. The Challenge is
*expected* to contain `sorry`.

### 3.3 Solution module

May import arbitrary pinned Git dependencies. Compared declarations must have the
**same names and types** as in the Challenge. No `sorryAx`, no `Lean.ofReduceBool`
(so no `native_decide`; ordinary `decide` is fine), no custom axioms, no unnamed
missing definitions. Permitted axioms are exactly `propext`, `Quot.sound`,
`Classical.choice`.

### 3.4 comparator.json

Accepted keys, per the current official template:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["Namespace.theorem_name"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}
```

`enable_nanoda` **is** in the official template and is accepted (an earlier reading
of the checklist's "required keys only" as forbidding it was wrong). Use `true` for
Palomar configs. Do not carry over the extra custom keys used by this repository's
internal Davis–Kahan exhibition config.

### 3.5 Repository constraints

≤500 MiB excluding `.git`; **no Git submodules**; no Git LFS pointers; no compiled
artifacts (`.olean .ilean .a .bc .dll .dylib .o .obj .so .trace`) outside `.lake`;
all Git dependencies on credential-free `https://github.com/owner/repo` URLs pinned
to full 40-character lowercase SHAs; exactly one conventionally-named root LICENSE.

### 3.6 Review

Two automated stages plus disclosure assessment. (a) Comparator + Lean kernel +
NanoDa replay. (b) An LLM judges whether the informal account matches the Challenge
and whether a **notability anchor** is met — "a credible research area and a
plausible kind of mathematician who could reasonably find it interesting" — scored,
with rejection below 4. Prohibited: trivial results presented as research;
definitions engineered to manufacture conclusions; deceptive or materially
incomplete metadata.

The informal account may live in Challenge module docs, declaration docstrings, the
selected project README, or `formalization.yaml`.

---

## 4. Verified repository baseline (2026-08-28, at `dc25a4ef`)

| Item | State | Verdict |
| --- | --- | --- |
| GitHub repo | `AIQ-Kitware/aiq-dkps-formalization`, public, Apache-2.0, default branch `main` | ok |
| Tracked content | 32.3 MB (working tree inflates to 229 MB from untracked build output and submodule checkouts) | ok |
| Compiled artifacts tracked | none | ok |
| Git LFS | none | ok |
| LICENSE | one at root, Apache-2.0, matches metadata | ok |
| `lake-manifest.json` | committed; all git deps HTTPS + full SHA | ok |
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc1` vs minimum `v4.28.0` | ok |
| **Git submodules** | **three: `external/TauCeti`, `submodules/TauCetiRoadmap`, `submodules/TauCetiReview`** | **blocker** |
| `formalization.yaml` | v0.3, does not validate as v0.4 | blocker |
| Challenge import closure | 15 of 17 internal configs are Mathlib-only; `DavisKahanSylvesterPiOverTwo` (2 local imports) and `DavisKahan1970` (24 local imports, 583 lines, deliberately unproved targets) are not | see §6 |
| `native_decide` | `DkpsQuench2026/Paper/TheoryPractice.lean:584` | landmine; not in any DK/YWS closure |

Submodule gitlinks at baseline:

```
external/TauCeti          1b39d420ac84ed9a5a7d536ce19b37818ad29c39   (TauCetiProject/TauCeti)
submodules/TauCetiReview  222eed046013fbee91239aea4a5186b12f086e65
submodules/TauCetiRoadmap 314943b32da2da9e9697fea63b264c9cbf683dff
```

Known non-Palomar gate failures at baseline, which are **not** this campaign's
business and must not be "fixed" by lowering baselines or deleting checks:
`check_expose_ratchet`, `check_tauceti_readiness`, `check_tauceti_roadmap_topics`.

---

## 5. Architecture: main, branches, and extracted entry repos

### 5.0 Superseded 2026-08-29: the entry repos carry the proof

Maintainer decision, replacing the thin-wrapper design described in the rest of this
section. Each entry repository is an **extraction**, not a wrapper: it contains the
package directories the entry needs, copied verbatim, and builds them itself.

- `AIQ-Kitware/aiq-davis-kahan-1970-rotation-eigenvectgors-perturbation-formalization`
  carries `ForTauCeti` and `DavisKahan`.
- `AIQ-Kitware/aiq-yu-wang-samworth-2015-useful-variant-davis-kahan-statisticians-formalization`
  carries `ForTauCeti`, `DavisKahan` and `YuWangSamworth2015`. `DavisKahan` is there
  for its Hilbert-Schmidt/Frobenius ideal theory, which the YWS package uses.

Both pin the same Mathlib and Tau Ceti revisions as this repository. Both were
verified with `lake build Challenge Solution` from a clean build directory (8739
and 8732 jobs).

**Metadata shape, revised 2026-08-29 against PalomarPolicy `d5a647d`.** Current
policy omits `repository` entirely when the submitted repository contains the
substantive development, and records that default as `substantive-development` in
the mechanical report; the explicit `repository.role: substantive-development`
spelling is still accepted but unnecessary. The extractions therefore carry no
`repository` key, and state the extraction lineage in prose in their READMEs
instead. `repository.substantive_formalization` is for thin wrappers only, and an
extraction that physically contains the proof source is not one.

This repository stays authoritative. The census, the distilled source specification,
the semantic-audit apparatus and the gate scripts are deliberately **not** extracted:
they are maintenance machinery, and a second copy would be a second thing to keep
honest. Because they are absent, neither entry repository makes a completion or
coverage claim about its paper. Changes go upstream here; an extraction is refreshed
from the packages, so a fix made only downstream is lost.

What this drops from the design below: the wrapper `[[require]]` on this repository
at a pinned SHA, and `repository.substantive_formalization`. What it keeps, and what
is still load-bearing: **no Git submodules anywhere**, because Lake clones a
dependency with a plain clone and does not initialise submodules.

The skeletons under `registry/<entry>/wrapper/` are kept as the metadata and
comparator-config source that the extraction copies from. They are no longer a
description of the submitted repository's shape.

**Directory renamed 2026-08-29: `palomar/` became `registry/`.** It sat beside
the Lean library directory `Palomar/`, and two paths differing only in case are
one path on a case-insensitive filesystem, so a Windows or default-macOS checkout
could conflate them or refuse operations. Both repositories now use `Palomar/`
for Lean source and `registry/` for submission configuration and metadata. The
rename was done with `git mv palomar registry`, a genuine rename rather than a
case-only one, precisely because Git handles case-only renames badly on those
filesystems. Palomar selects both paths explicitly, so nothing about the
submission depends on the directory name.

### 5.1 onward: the superseded thin-wrapper design


#### Why the submodules must go, even though we extract

Lake fetches a Git dependency with a plain clone — **it does not init submodules**.
An extracted wrapper repo whose `Solution.lean` requires this repository at a pinned
SHA therefore cannot even configure while `lakefile.toml` carries
`[[require]] name = "TauCeti" path = "external/TauCeti"` pointing into a gitlink.

So "make `main` cleaner" is load-bearing, not cosmetic: **this repository must be
fetchable and buildable as a Lake git dependency at the submitted commit.**

### 5.2 Target layout

**This repository (`main`)** is the *substantive development*:

- TauCeti becomes a canonical pinned Git dependency (`https://github.com/TauCetiProject/TauCeti.git`
  at the exact current revision) instead of a submodule path dependency.
- Scripts that need an editable upstream checkout take an explicit optional
  `--tauceti-root` / `TAUCETI_ROOT`; none defaults to a destructive export target.
- Roadmap/review checkers degrade to an honest `SKIP`/`UNAVAILABLE` when their
  external checkout is absent, rather than silently passing.
- Root `formalization.yaml` is valid v0.4 describing the whole development.
- `Palomar/<Entry>/{Challenge,Solution}.lean` and `registry/<entry>/comparator.json`
  live here so they can be verified locally with real Comparator.
- Goal: **zero gitlinks on `main`**. If a workflow genuinely still needs one, it
  stays and the branch drops it; the delta is then a `.gitmodules` deletion plus
  gitlink removals — a handful of lines, portable in both directions.

**Per-entry submission repos** (extracted from a branch, prepared here) are Palomar
**thin wrappers**:

```
Challenge.lean         copied verbatim from Palomar/<Entry>/Challenge.lean
Solution.lean          copied verbatim; imports resolve identically either way
comparator.json        challenge_module "Challenge", solution_module "Solution"
formalization.yaml     repository.role: thin-wrapper
                       repository.substantive_formalization.id: AIQ-Kitware/aiq-dkps-formalization
                       repository.substantive_formalization.revision: <40-char SHA>
lakefile.toml          requires this repo at that SHA, plus Mathlib
lean-toolchain         matches
lake-manifest.json     committed, all deps pinned
LICENSE                Apache-2.0
README.md              the informal account
```

`Solution.lean` is **byte-identical** in both contexts: `import DavisKahan.…`
resolves the same whether the library is local or arrives as a Lake dependency. Only
the lakefile differs. Keep it that way — it is what makes extraction mechanical.

Prepare the wrapper skeletons under `registry/wrappers/<entry>/` in this repo so the
extraction step is a copy, not a rewrite.

Fallback if extraction proves awkward: submitting this repository directly with a
non-default project/config/metadata path is enabled by exactly the same work.

---

## 6. The two entries

### E1 — Yu–Wang–Samworth 2015 (P0, closest to ready)

Target statement, already Mathlib-only and 40 lines at
`Challenge/YuWangSamworth/Conformance.lean`:

```
YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap
```

The Frobenius sin-Θ bound depending only on the **population** eigengap — the whole
point of the paper, and the reason it is cited across statistical spectral methods.
Build a polished Palomar version rather than reusing the internal module verbatim.

Investigate whether the aligned-frame / Procrustes conclusion of Theorem 2 can be
stated cleanly with Mathlib-only vocabulary in the same short Challenge. Include it
only if it does not hurt auditability; one strong sin-Θ entry is acceptable.

Metadata must say which part of YWS the entry represents. Do not claim the entry
stands for all 24 census rows. Preserve the disclosures that printed Equation (4) is
false as printed and that the rank-boundary convention is corrected.

### E2 — Davis–Kahan 1970 (P0)

Target statement, verified to exist and to be expressible in ordinary Mathlib
vocabulary:

```
TauCeti.norm_starProjection_comp_starProjection_le
  ForTauCeti/Analysis/InnerProductSpace/SinTheta/OperatorNorm.lean:252
```

The operator-norm sin-Θ theorem: `T, S` symmetric, `U` a `T`-invariant subspace with
quadratic form `≥ (c+g)‖·‖²`, `V` an `S`-invariant subspace with form `≤ c‖·‖²`,
`‖(S−T)x‖ ≤ ε‖x‖`, `g > 0` ⟹ `‖V.starProjection ∘L U.starProjection‖ ≤ ε/g`. Its
statement uses only `LinearMap.IsSymmetric`, `Submodule.starProjection`,
`HasOrthogonalProjection`, `RCLike.re ⟪·,·⟫`, `∘L`, `‖·‖` — all Mathlib. The proof
stays in `ForTauCeti` and is reached through the Solution.

**Do not** reuse `Challenge/DavisKahan1970/Conformance.lean`: 24 local imports, 583
lines, and deliberately unproved paper-fidelity targets. It is an internal exhibition
surface and stays that way.

Also investigate whether a source-recognizable finite `tan 2Θ` or `sin 2Θ` Part III
headline can be stated in pure Mathlib vocabulary without inflating the Challenge.
Two or three genuinely central source results may be more representative than one —
provided the Challenge stays short and ordinary.

Do **not** attempt to drag the full unbounded `LinearPMap` framework into a Challenge.
If it would require recreating a large local spectral API inside the trusted surface,
defer that entry and say so; a future accepted Tau Ceti upstream API would make it
small. The README and metadata can explain that the repository contains the full
unbounded development.

### 6.3 DKPS packages — Palomar-worthy state, no entries this run

Acharyya 2024, Acharyya 2025, Helm 2025 and Quench 2026 get **no Palomar entry, no
Challenge module and no entry metadata** in this campaign. YWS and Davis–Kahan are
submitted first and alone. The DKPS entries come later, made either here or by JHU —
and since the paper authors themselves may be the submitters, the deliverable is that
the mathematics and the statement surfaces are ready for someone else to pick up.

"Palomar-worthy" is a checkable per-paper standard, not a vibe. For each of the four
packages, the headline result must satisfy all of:

1. **Mathematically finished.** No remaining seam between the paper's stated
   hypotheses and the Lean theorem that is merely an artifact of one proof route. Every
   assumption is either the paper's, or a documented repair with a stated reason.
2. **Honestly dispositioned.** Exact source theorems say so; repairs say so and say
   *what* was repaired and why the printed statement does not stand. Counterexamples to
   false printed claims are preserved and reachable from the census row.
3. **Statement-surface legible** — the load-bearing new criterion. The headline theorem
   must be *expressible* in a Palomar Challenge: Mathlib-only vocabulary, or Mathlib
   plus definitions that carry ordinary mathematical meaning and can be restated in a
   short Challenge with precise docstrings. A statement that can only be posed by
   importing this repository's implementation is not ready, however well proved.
4. **Axiom-clean.** The headline theorem's axiom closure is exactly `propext`,
   `Quot.sound`, `Classical.choice` — no `sorryAx`, no `Lean.ofReduceBool`, no custom
   axiom. This is why the `native_decide` at
   `DkpsQuench2026/Paper/TheoryPractice.lean:584` is now a blocker rather than a
   landmine: **check whether it is in the Quench headline closure, and remove it either
   way.**
5. **Audit layer current.** Census status, semantic-review verdict, declaration lists
   and generated alignment packets all match the actual theorem types, with no stale
   freeform aggregate prose contradicting the structured rows.
6. **Notability statable.** A one-paragraph research-interest case exists that argues
   from the mathematics, never from formalization difficulty.

Deliver, per package, a short **Challenge-feasibility finding**: which declaration is
the headline, whether its statement is Mathlib-only expressible today, and if not,
precisely which definitions would have to be restated or upstreamed. That finding is
what determines whether JHU can pick this up, and it is more valuable than a
half-built Challenge.

Known remaining work by package, from the prior audits — verify each against current
code before acting, several may already be closed:

- **Acharyya 2024** — hostile re-audit of the final T2/T4/T5 surfaces, looking for
  another defect of the kind just found: a proof needing only fixed `i, i'` while the
  statement quantifies uniformly; `∀ᶠ` in the wrong binder order; a zero-stage
  artifact; a product measure where a kernel is needed; fresh-query versus sampled-pair
  law confusion; an ε-dependent subsequence; an integrated moment assumption stronger
  than dominated convergence needs. If no defect is found, leave the mathematics alone.
- **Acharyya 2025** — one clean source-facing theorem for the corrected finite
  concentration bound with the entrywise dissimilarity bound `R` explicit (A25-T1); the
  one-assembly-step spectral-norm corollary wrapper if it really is one step (A25-C1);
  and, only after those, a meaningful spread/nondegeneracy condition from which
  Assumptions 1 and 2 follow, labelled as a repair and never as the printed
  Proposition 1 (A25-P1).
- **Quench 2026** — adjudicate the normalization mismatch (Q26-D): the displayed
  dissimilarity differs by `1/m` from the normalization the imported DKPS theory
  assumes. Pick one coherent reading, justify it from the paper, and carry it
  explicitly; do not leave an undocumented scale change. Then reconsider whether the
  strengthened Acharyya 2024 continuum route removes the finite perspective net in the
  compact-infinite route (T2A/T2B/RAW-INF) — likely the highest-value new theorem work
  in this campaign. Preserve the tie-averaged nearest-neighbour repair and the
  correction of the false all-compact-subsets assumption.
- **Helm 2025** — the literal Equation (2) wrapper if the underlying theorem is
  already there (H25-EQ2); and investigate discharging the bridge's distance-convergence
  hypothesis by fibering `Acharyya2024.rawStress_mds_stability_set` over the latent
  sample (H25-BRIDGE). Preserve the uniform-integrability / dominated-loss repair and
  the evidence that convergence in probability alone does not give expected-risk
  convergence.

---

## 6.4 Verification status (2026-08-28)

Both entries pass the **real Comparator**, not a proxy for it: statements exported
with `lean4export` and compared, the independent NanoDa kernel accepting the
solution, and Lean's own kernel accepting it.

```
PASS   registry/yws-2015/comparator.json
PASS   registry/dk-1970/comparator.json
```

Also verified: challenge import closures reach nothing in this repository; both
compared declarations have axiom closures of exactly `propext`, `Quot.sound`,
`Classical.choice`; the static preflight passes; and a fresh clone with no
`git submodule update` resolves every dependency and compiles a Tau Ceti-dependent
module.

### Running Comparator locally — two things that will bite

**The exporter must match the oleans.** Comparator pins its own Lean toolchain,
which was `v4.34.0-rc2` while this repository is on `v4.34.0-rc1`. `lean4export`
built at the wrong version fails with `incompatible header` on our `.olean` files.
Set the comparator checkout's `lean-toolchain` to this repository's value and
rebuild before running anything.

**`landrun` needs Go; NanoDa needs Rust.** `landrun` is the sandbox, not a check:
without Go, `--fake-landrun` runs the same commands unsandboxed and the comparison
is unaffected. NanoDa *is* a check — the second, independent kernel — and it does
run: clone `https://github.com/ammkrn/nanoda_lib`, `cargo build --release`, and put
`target/release` on `PATH`.

```bash
git clone https://github.com/leanprover/comparator.git
cd comparator && cp ../lean-toolchain . && lake build && lake build lean4export
git clone https://github.com/ammkrn/nanoda_lib.git
cd nanoda_lib && cargo build --release
PATH=$PWD/target/release:$PATH \
AIQ_COMPARATOR_TOOL_ROOT=<tools> scripts/verify_palomar.sh --fake-landrun
```

---

## 6.5 DKPS Challenge-feasibility findings (2026-08-28)

Criterion 3 of §6.3 asks whether each package's headline theorem could be *stated*
in a Palomar Challenge, which may import Mathlib and Tau Ceti but nothing from this
repository. That is measurable rather than a matter of taste: count the constants a
statement's type actually mentions whose defining module is a local library. Those
are exactly what would have to be restated in the Challenge, with a precise
docstring each, or upstreamed first.

| package | candidate headline | local constants in its type |
| --- | --- | ---: |
| Acharyya 2024 | `Consistency.lp_consistency_of_replicates_population` | 6 |
| Acharyya 2025 | `AlignedPipeline.highProb_aligned_configFrobError_of_entrywise_close` | 9 |
| Quench 2026 | `highProb_queryEfficient_nn` | 8 |
| Helm 2025 | `DKPS.Theorem2_bayes` | 15 |

**Acharyya 2024 — feasible, and the closest.** Two of the six are the type
abbreviations `Rvec` and `Mat`, both `EuclideanSpace` and inlinable at no cost. The
four that carry content are `pointStress`, `continuousPointStress`,
`pairDiscrepancy` and `lpPairDistErr` — the one-point raw stress, its population
form, the pairwise discrepancy and the `L^p(P × P)` error. All four are ordinary
multidimensional-scaling notions with a one-line mathematical meaning, so they can
be defined in a Challenge with honest docstrings. The obstacle is not vocabulary
but hypothesis count: the theorem carries the structural assumptions of Lemma 2,
and a Challenge would be long. Splitting the statement is the design question, not
whether it can be posed.

**Quench 2026 — feasible.** Of the eight, `Model`, `ProbMeasure` and `Vec` are
abbreviations. The rest — `HighProbAtTop`, `MSE`, `yFull`, `yQ`, `yNN_paper` — are
short and concrete: an eventual-high-probability quantifier, mean squared error,
the full-benchmark score, its query-restricted version, and the nearest-neighbour
estimator. This would make a readable Challenge.

**Acharyya 2025 — feasible with more work.** Nine constants, and unlike the others
several are genuinely structural: `classicalMDSMatrix`, `EntrywiseClose`,
`ConfigFrobError`, `alignedSpectralConfigFrob`, `configFrobBound`. Restating them
means putting the classical-MDS construction itself inside the trusted statement
surface, which is a real design decision rather than transcription.

**Helm 2025 — not currently practical.** Fifteen constants, and they are the
paper's whole apparatus: learning rules, loss functions, decision functions, risk
and Bayes risk, plus four separate hypothesis predicates. A Challenge restating all
of it would be most of a small library, and a reviewer would be asked to trust
fifteen definitions to check one theorem — the opposite of what a small auditable
statement is for. The honest disposition is to defer a Helm entry, and to record
that the obstacle is the size of the statement's vocabulary, not the state of the
proof.

The measurement is reproducible: elaborate the declaration and classify
`ConstantInfo.type.getUsedConstants` by defining module.

---

## 7. Work plan and priorities

**P0 — mandatory**

1. Baseline: record `git status --short`, `git rev-parse HEAD`, `git log --oneline -20`,
   `git submodule status`, `git ls-files -s | awk '$1 == 160000'`; run `lake build`,
   `lake build Challenge`, `lake build DavisKahan.Audits.All`, `run_gates.py --fast`
   and record the exact expected failures **before** changing anything.
2. Re-read §2 live sources; note any drift in this file.
3. Convert the TauCeti dependency to a canonical pinned Git dependency; verify the
   revision exists upstream; regenerate and hand-inspect `lake-manifest.json`;
   confirm Mathlib did not move. Full build. Own commit.
4. Refactor `external/TauCeti`-hardcoding scripts to optional explicit checkout
   paths (`scripts/export_for_tauceti.py`, `certify_davis_kahan_1970.py`,
   `refresh_tauceti_pr1_consistency.py`, their tests). Own commit.
5. Make the roadmap/review-dependent checkers degrade honestly when their checkout is
   absent (`check_roadmap_delivered.py`, `check_tauceti_roadmap_topics.py`,
   `audit_scan.py`); teach `run_gates.py` about that state. Own commit.
6. Remove the gitlinks and `.gitmodules`. Verify `test ! -e .gitmodules` and that
   `git ls-files -s | awk '$1 == 160000'` is empty. Full build. Own commit.
7. Migrate root `formalization.yaml` to v0.4 (§8). Own commit.
8. `Palomar/YuWangSamworth2015/{Challenge,Solution}.lean` +
   `registry/yws-2015/comparator.json` + wrapper skeleton, verified.
9. `scripts/check_palomar_readiness.py` (static) and `scripts/verify_palomar.sh`
   (real Comparator + lean4export + NanoDa + Landrun where supported), per D3.
10. Clean-clone verification: a fresh checkout at the candidate commit builds with no
    `git submodule update`, and the wrapper repo skeleton configures against it.

**P1 — the two entries, and the DKPS Palomar-worthy standard (D4)**

11. `Palomar/DavisKahan1970/{Challenge,Solution}.lean` + config + wrapper, verified.
12. **DKPS packages to Palomar-worthy state** (§6.3), one package per lane, each
    finishing with its Challenge-feasibility finding recorded in the census:
    - Acharyya 2024 — hostile re-audit of the final T2/T4/T5 surfaces.
    - Quench 2026 — adjudicate the `1/m` normalization mismatch; remove the
      `native_decide` at `DkpsQuench2026/Paper/TheoryPractice.lean:584` and confirm the
      headline closure is axiom-clean.
    - Acharyya 2025 — corrected finite bound with `R` explicit (T1), then the
      one-step spectral-norm wrapper (C1).
    - Helm 2025 — literal Equation (2) wrapper (EQ2), then the bridge hypothesis.
13. Entry narratives (§9) and `registry/README.md`.

**P2 — if healthy time remains**

14. Davis–Kahan census residue that is mapping-stale rather than mathematically open:
    `DK-3.2-prop`, `DK-4.1-prop`, `DK-9-model`, `DK-10.4` (split established
    identities from the open functional-calculus question). Re-audit source and
    current Lean *before* proving anything new.
15. YWS single-pass current-state review: stale references, hidden hypotheses,
    quantifier order, rank-boundary corners, local definitions leaking into public
    statements. No broad YWS proof campaign — 24/24 rows are already disposed.
16. Quench compact-infinite route: whether the strengthened Acharyya 2024 continuum
    theory removes the finite perspective net (T2A/T2B/RAW-INF). Highest-value new
    theorem work if it lands; do not force it past a real compactness or measurability
    obstruction — identify the missing theorem instead.
17. Acharyya 2025 spread/nondegeneracy condition (A25-P1), labelled a repair.
18. Genuinely open Davis–Kahan source items: `S1-block-residual`,
    `DK-5-hermitian-inequalities`, `DK-6.3-thm` Example 6.1,
    `DK-9-infinite-residual-counterexample`, `DK-9.8`.

**P3 — stretch**

19. Dependency-visualization and documentation presentation work.

---

## 8. `formalization.yaml` v0.4 migration

Migrate; do not discard. Required shape (validate against the live schema):

```yaml
version: v0.4
project:
  name: ...
  description: ...            # public registry abstract, ≤10,000 chars
  authors: ["Jon Crall", "Edward Wang"]        # D5
  responsible_maintainers: ["Jon Crall"]       # D5
  license: "Apache-2.0"                        # must match root LICENSE
repository:
  role: substantive-development                # root file; wrappers use thin-wrapper
classification:
  arxiv: [...]        # 1–8, from Palomar's taxonomy snapshot
  msc2020: [...]      # 0–8, from Palomar's taxonomy snapshot
sources: [...]        # ≥1; at least one relationship formalizes/adapts/independently-proves
automation:
  methods: [{method: agent, models: [...], framework: ...}]
review:
  status: ...
status: {scope, sorry_count, sorry_in_definitions, axioms, main_results}
fidelity: {divergences: ...}
```

Fields in the current v0.3 file that are **off-schema** and must be moved, renamed, or
dropped: `project.repository`, `project.validation_note`, `sources[].author_contacted`
(→ `author_endorsement`, enum), `sources[].type: "research paper"` (→ `article`),
`sources[].prior_work` (→ `note` / `related_formalizations`), `status.repository_build`,
`status.comparator_configs`, the whole `challenge_packages` block, and
`fidelity.summary` / `fidelity.known_limitations` (v0.4 `fidelity` has only
`divergences`). Unknown fields are permitted, but do not leave v0.3-only fields
masquerading as current required ones, and update every path invalidated by the
submodule removal.

Compute `sorry_count` / `sorry_in_definitions` / `axioms` from the elaborated
environment; do not guess, and do not write zeros before establishing them. Exclude
deliberate statement-side Challenge holes per the metadata standard.

Source relationships must be honest: `formalizes` for exact source theorems, `adapts`
for repaired ones. Preserve the standing disclosures — Davis–Kahan Proposition 4.4 is
false as transcribed and carries a formal counterexample plus repair; the Section 2
tangent scope has an accepted nonlocal standing-condition reading; YWS printed
Equation (4) is false as printed and is corrected.

Automation disclosure is derivable from git: co-author trailers show Claude Opus 5
(~2,300 commits), Claude Opus 4.8 (~410), Claude Fable 5 (~250), and several GPT-5.6
variants (~350). Record what the evidence supports; do not fabricate a complete
historical list, and do not invent costs or wall time.

Review status: not `peer-reviewed`. The honest description is extensive self-review,
adversarial source audits, multiple independent agent reviews, and compiler/comparator
checks, with human coordination — distinguish kernel verification from automated
semantic audit from human coordinator review.

---

## 9. Entry narrative quality

For each entry a mathematically literate reader must be able to see: what the theorem
says; why it is of research interest; which source result it corresponds to; which
hypotheses matter; what differs from the printed source; how the Solution connects to
the wider formalization. Concise mathematics plus precise metadata beats a long essay
around a short Challenge.

Research-interest framing must be mathematical. Davis–Kahan: classical spectral
subspace perturbation, foundational in numerical linear algebra, operator theory and
statistics. YWS: the population-gap variant removes dependence on an unobservable
sample eigengap, which is why statisticians cite it. **Never** argue interest from
formalization difficulty — Palomar explicitly does not count that.

`Challenge/README.md` currently opens with "The direct Mathlib submission track is
closed" and frames the tree as regression infrastructure. That is fine for the
internal tree but must not be the text a Palomar reviewer reads; give the Palomar
entries their own README.

---

## 10. Guardrails

Do not weaken a theorem, hide a hypothesis inside a definition, or substitute an
implementation-specific surrogate for a recognizable notion in order to make a
Challenge, a comparator run, or a census go green. Do not convert a documented source
repair back into a claimed exact theorem. Do not delete a counterexample that shows a
printed statement false. Do not put `sorry` into production mathematics —
statement-side Challenge holes only. No custom axioms. No `native_decide` anywhere in
a Palomar Solution's dependency closure.

Do not start an `@[expose]` campaign. Do not start a Tau Ceti roadmap/readiness
campaign. Do not reopen the completed migrations (Frontier, MathAhead,
`Experimental/InfiniteDimensional`, `RectangularSymmetricIdealFamily`,
`ClosedOperator` → `LinearPMap`) unless a real bug traces to one. Do not repurpose or
damage the existing `Challenge/` calibration suite — the Palomar tree is separate. Do
not mass-edit the internal comparator configs to match Palomar conventions; they are
separate infrastructure.

Do not invent authors, maintainers, endorsements, affiliations, reviewer identities, or
model usage. Do not claim registration, approval, acceptance, peer review, or novelty.

Work in small coherent commits: inspect, one conceptual change, targeted build,
inspect the diff, commit, push. Never combine historical prose, current APIs, generated
audit artifacts and mathematical code in one scripted rewrite — the ClosedOperator
migration is the standing lesson. Scope every scripted edit narrowly, run
`git diff --check`, and prefer restoring a file and redoing it by hand over patching a
bad patch.

---

## 11. Stop and report rather than guessing

If live policy materially contradicts this file; if the pinned Tau Ceti revision is not
acceptable as the canonical dependency and moving it would force a proof migration; if
authorship or maintainer metadata cannot be settled honestly; if a Challenge would need
hundreds of lines of project-specific definitions with no clean trusted statement
surface; if Comparator/NanoDa do not support the current Lean RC; if a proposed
improvement would invalidate an accepted source repair; or if a source statement looks
false and no existing counterexample or repair covers it — record the blocker precisely,
checkpoint everything sound before it, and move to an independent lane. A precise
blocker is useful output.

---

## 12. Human-review checklist before any submission

The maintainer must personally decide, for each entry:

- [ ] the public abstract wording in `project.description`
- [ ] author and maintainer names as recorded
- [ ] every source relationship and every repair description
- [ ] which comparator config to submit, and whether the entry's notability case holds
- [ ] the final public commit SHA of the substantive repository
- [ ] the wrapper repository contents, if extracting
- [ ] the Palomar preview, after mechanical verification and editorial review

Registration is permanent. Withdrawal is unavailable once registered.

The correct phrasing for a finished, verified entry is:

> The following entries are locally Palomar-ready at this commit, subject to the
> maintainer's review and Palomar's own verification and editorial process.
