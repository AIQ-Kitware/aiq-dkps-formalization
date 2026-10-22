# Luna: overnight DKPS consumption of accepted TauCeti mathematics

**Execution assignment, 2026-10-21.** Continue work autonomously in the user's
**`~/code/aiq-dkps-formalization`** checkout for as much of the available run as
is productive. Implement, compile, and commit concrete dependency-closed
migrations; do not finish after writing a survey. This is **DKPS downstream
consumption**, not TauCeti upstream PR development.

**First and continuous invariant:** if the shell's checkout or any pasted build
log says `~/code/TauCeti` rather than `~/code/aiq-dkps-formalization`, **STOP**,
call out the wrong-project context, and return to the DKPS checkout. Do not
silently switch to TauCeti just because a build log or named PR mentions it.
Do not write to the independent `~/code/TauCeti` checkout, any TauCeti PR
branch, or `.lake/packages/TauCeti`.

## Goal and binding conventions

Make DKPS rely on **already accepted, present-on-`main` TauCeti declarations**,
retire its duplicate implementations and obsolete compatibility bridges, and
leave all maintained paper-facing results compiling. `ForTauCeti` is a shrinking
donor of mathematics not yet upstreamed, **not** a permanent copy of TauCeti.
This task covers the whole upstream-first consumption campaign, not only the
newest merged PR. Continue to the next unblocked slice whenever one finishes.

Read `AGENTS.md`, `ForTauCeti/README.md`,
`dev/lean-proof-engineering-lessons.md`, and
`dev/tauceti/dkps-upstream-contribution-census.md` before substantive changes.
Follow `AGENTS.md` when it imposes stronger repository constraints. In
particular:

- Preserve explicit paper-source theorem statements, theorem names needed by
  a maintained census, formally established refutations, counterexamples,
  published constants, real/complex generality, operator domains, and
  source correspondence. Keep a **short downstream theorem proof**, not an
  independent second mathematical proof, when the source-facing declaration
  is still needed. Canonical representation changes must be justified by
  actual equivalence and consumer analysis, not silently weaken a result.
- Migrate **all** consumers in a dependency-closed slice, then **delete**
  displaced definitions/proofs and temporary adapters. Never declare a slice
  complete merely because it imports an upstream theorem. Do not accumulate
  forwarding aliases, redundant reexports, or repeated coercion wrappers.
- Preserve unmerged stronger work, including genuinely unbounded/self-adjoint
  and arbitrary-ideal endpoints. A finite-dimensional theorem with the same
  nickname does not subsume an unbounded theorem. Do not invent new proof
  obligations merely to remove more source code.
- Avoid new `scripts/check_*.py`, tooling frameworks, new routine lint gates,
  axiom-print inventories, bulk `#check`, or repetitive `sorry`/`admit` checks.
  Ordinary Lean compilation and the actual theorem types are the gates.
- Do not introduce new runtime tests, validation branches, or constraints
  unrelated to the mathematical migration. Performance and proof quality
  both matter. Do not modify non-target packages or the TauCeti repository.
- The intention at
  <https://github.com/TauCetiProject/TauCetiRoadmap/issues/776> covers eight
  operator-theory roadmaps and **existing, source-backed DKPS proofs**, not
  exclusive ownership of the roadmap. Keep independently developed upstream
  mathematics separate in the provenance census, and preserve Spectra ancestry.

## What is known now; recheck against the live repositories

At instruction preparation, TauCeti `main` was
`175cd8793173c22af598fa2827648eb32f573580`; its
`lean-toolchain` is `leanprover/lean4:v4.36.0-rc1` and its Mathlib manifest
revision is `e3e75e86143b43849829fdcd44a39a6b0fe35234`. These inputs
match the last reported DKPS toolchain/Mathlib, but **the DKPS TauCeti lock
was still at** `f91b6396a35d847a87a0d37519325918356bc0fc` before the
new acceptance. The live user's checkout, not the archived snapshot used to
prepare this instruction, is authoritative. Recheck `main` before selecting a
new immutable SHA and document the actual SHA chosen. Never pin a PR head
or assume that a Bors "merge_commit_sha" is on the first-parent ancestry:
verify the declaration in the actual accepted `main` tree.

**Newly accepted:**

- [#19268 SSP-C19](https://github.com/TauCetiProject/TauCeti/pull/19268)
  has landed. Module:
  `TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Spectral`.
  Exact public theorems:
  `TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_orthogonal_pointSpectralSubspace_comp_le_map_sylvester_apply`
  and
  `TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_orthogonal_pointSpectralSubspace_Ioo_comp_le_map_sylvester_apply`.
  The former accepts a point-spectral selection with an exterior-spectrum
  hypothesis on the complementary block; the latter selects the enlarged
  interval and obtains the exterior condition automatically. Both provide
  the residual inequality for rectangular unitarily invariant seminorms.
  This PR explicitly identifies the local donor source modules
  `ForTauCeti/Analysis/InnerProductSpace/SinTheta/DirectedBounds.lean` and
  `ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean`.
- [#19252 SSP-C20](https://github.com/TauCetiProject/TauCeti/pull/19252):
  `Submodule.mul_projectionGap_le_norm_sub_of_pointIntervalExteriorGap` and
  `Module.End.mul_norm_sub_starProjection_pointSpectralSubspace_le` in
  `TauCeti.Analysis.InnerProductSpace.Projection.SpectralPerturbation`.
  Equal-rank, constant-one **finite-dimensional** spectral-projector bounds.
- [#19229 SSP-D12](https://github.com/TauCetiProject/TauCeti/pull/19229):
  `LinearMap.mul_norm_sinThetaMap_rightSingularSubspace_le` and the
  corresponding left theorem in
  `TauCeti.Analysis.InnerProductSpace.SingularSubspace.Perturbation`.
  **Already consumed in DKPS**: the user's compiled v3 YWS forwarding change
  and subsequent singular-subspace bridge retirement should be retained.
  Do not re-create the removed legacy singular-subspace definitions.
- [#19145 SA-B42](https://github.com/TauCetiProject/TauCeti/pull/19145):
  `TauCeti.ProjValMeasure.polarizedComplexMeasure_variation_univ_le` and
  `instIsFiniteMeasurePolarizedVariation` in
  `TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Variation`.
  No entire duplicate donor module is known to be removable on this basis
  alone; look for precise proof replacement and downstream simplifications.

**Other accepted, potentially consumable families:**

- Point spectra, spectral invariance/gaps and projection geometry:
  #14418, #14532, #15983, #16545, #18947, #18985, #18991.
- Hermitian dilation and perturbation: #18946 (SSP-D06),
  #19010 (SSP-D13); Gram/singular systems and polar APIs #13967, #16450.
- Closed `LinearPMap` operators, real spectral separation, PVMs and
  spectral-measure infrastructure: #13871, #13872 (**only the accepted
  CStar gap-inverse portion**), #17527, #18895, #18904, #18907, #18915,
  #18917, #18918, #18935, #18937, #18982, #19000, #19005, #19145.
- Approximation numbers/operator ideals, Ky Fan and unitarily invariant
  seminorms: #13866, #14241 (explicit DKPS adaptation), #14501, #14589,
  #16010, #16061, #16545. Some of these were **developed independently**
  despite overlapping donor results. Reuse them, but do not misattribute them.

**Not accepted at this checkpoint:** #18927, #18942, #19242, #19277,
#19299, #19329, #19338, and **#19817 SSP-C24**. Check status when
planning each slice, but do **not** consume open PR branches, vendor their
proofs as accepted, or do review/CI/branch work for them. If a PR actually
lands on `main` during this run, record the new main SHA and treat it as a
newly accepted input only after updating/rechecking DKPS's dependency pin.
No constant polling is needed; a check at a new major phase is sufficient.

## Phase 0 — inspect and protect the live DKPS checkout

Work in `~/code/aiq-dkps-formalization` on its current user branch. First
check `pwd`, `git rev-parse --show-toplevel`, `git status --short`, the current
branch/SHA, and the exact changed/untracked paths. **Do not reset, clean,
stash, discard, or overwrite unrelated changes.** In particular, inspect the
recently applied canonical point-spectral-subspace migration, including
`ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean`, and preserve
the latest v3 containment proof (using the public
`Module.End.pointSpectrumIn_iff` eliminator) and any fixes the user has
already compiled. The user moved on after the latest fix: do not downgrade
their earlier user-verified Lean claims or declare them "unverified" without
actual contradictory evidence.

Read the existing provenance census and `dev/tauceti` migration notes as
maps, not as guaranteed-current truth. Do not overwrite a newer locally
edited file with an old archive or plan. Record the baseline and accepted
repository versions in the eventual human summary, not in a new tracking
system. Prefer a single tmux session and sequential focused builds; for long
commands, tee output to a session-local log rather than using `nohup`.

## Phase 1 — pin the newly accepted TauCeti tree

1. Resolve the live upstream `main` SHA and read **that same ref's**
   `lean-toolchain` and `lake-manifest.json`. Record its exact Mathlib SHA.
2. Advance **only** the DKPS checkout's `lakefile.toml`,
   `lake-manifest.json`, and (if upstream changed it) `lean-toolchain` to
   coherent, immutable versions. The root Mathlib pin must exactly agree
   with the chosen TauCeti manifest and the actual Lake package checkout.
   Refresh with Lake if required; do not edit dependencies' source trees.
3. Run `lake exe cache get` **before every** `lake build`. Verify
   `git -C .lake/packages/TauCeti rev-parse HEAD` and
   `git -C .lake/packages/mathlib rev-parse HEAD` against the locks.
4. Build the foundation module(s) touched by the pin and the current public
   consumer(s), especially `ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace`,
   `YuWangSamworth2015.Core.SingularSubspace`, and `RoadmapBridge.Integration`.
   Fix genuine dependency API breakages before attempting broad deletions.
   Do not turn the rebuild into a new upstream development campaign.
5. Once the dependency bump and its necessary repairs compile, inspect the
   scoped diff and **commit that checkpoint**. Do not mix an unresolved
   dependency bump with a large later donor deletion.

Example initial inspection (not an instruction to discard or switch branches):

```bash
cd ~/code/aiq-dkps-formalization
pwd
git rev-parse --show-toplevel
git status --short
git branch --show-current
git rev-parse HEAD
git ls-remote https://github.com/TauCetiProject/TauCeti.git refs/heads/main
cat lean-toolchain
git -C .lake/packages/TauCeti rev-parse HEAD
git -C .lake/packages/mathlib rev-parse HEAD
lake exe cache get
```

## Phase 2 — use the accepted results in dependency-closed slices

This is the suggested **priority order**, not a demand to force a blocked
migration. For each slice compare actual Lean theorem statements (fields,
scalar type, carrier, rank, gap orientation, constants, adjoints, operator
domains), convert all maintained direct consumers, delete duplicate proof
bodies/obsolete bridges, build the changed module and public dependents, and
commit. If one slice is unexpectedly blocked, record the exact Lean error and
switch to the next **independent, accepted** opportunity. Do not end the
whole run because the first candidate has a difficult proof.

### Priority A — SSP-C19 canonical residual `sin Θ` (#19268)

Inspect the accepted module
`TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Spectral.lean`
under `.lake/packages/TauCeti`, then inspect local:

- `ForTauCeti/Analysis/InnerProductSpace/SinTheta/DirectedBounds.lean`
  (`sinTheta_residual_le`, and the ordered/spectral-distance variants);
- `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`
  (canonical subspace specialization and residual-dependent estimates);
- `ForTauCeti/Analysis/InnerProductSpace/SinTheta/UnitarilyInvariant.lean`,
  `ForTauCeti/Analysis/InnerProductSpace/Spectral/ResidualGap.lean`, and
  `ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean`;
- their `DavisKahan/**` and `YuWangSamworth2015/**` consumers.

First migrate **canonical finite-dimensional spectral selections** whose
statements are directly supported by the two accepted upstream theorems.
Where possible, replace a long residual proof by a short direct application
with only necessary `LinearMap`/`ContinuousLinearMap`, isometry, and norm
transport. Remove extra intermediate converters after the consumer move.
Preserve existing source-facing lemmas and meaningful stronger material.
The upstream C19 theorem is for a symmetric bounded `A`, symmetric `M`,
rectangular UI seminorm `N`, a **continuous linear** trial map `X`, and
canonical point-spectral subspaces. It does **not** automatically replace
local arbitrary-invariant-subspace, ordered-gap, general-disjoint-spectrum
`π/2`, or unbounded variants. A simple long-proof deletion is only valid
when the original conclusion follows with the **same assumptions**.

**Important opacity lesson from this repo:**
`TauCeti.PointSpectrumIn` and `Module.End.PointSpectrumIn` are not
interchangeable by `change` or unfolding in the Lean module system. Use the
accepted public membership and `pointSpectrumIn_iff` characterizations;
never rebuild fragile definitional-equality shims around an opaque API.

### Priority B — SSP-C20 equal-rank projector theorem (#19252)

Check the finite-dimensional comparison against
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`
(`opNorm_projection_sub_projection_le`,
`opNorm_spectralProjection_sub_spectralProjection_le`) and
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/DirectedBounds.lean`
(`opNorm_pointSpectralSubspace_sub_le` and nearby results).
Use accepted `Projection.SpectralPerturbation` theorems for *matching*
equal-rank interval/exterior spectral gaps, then delete local reproofs and
unused bridge lemmas. A theorem with two-sided gap hypotheses and **no**
equal-rank assumption, or a stronger dimension-free/coercive bound, is
**not** superseded by this PR. Keep the actual paper-facing declarations.

### Priority C — canonical point-spectrum predicates and projection geometry

The preceding work already retired the local
`TauCeti.pointSpectralSubspace` and old YWS singular-subspace definitions.
Continue with the remaining local `TauCeti.restrictedPointSpectrum`,
`TauCeti.PointSpectrumIn`, `TauCeti.IsInvariant`, linear-map-valued
`TauCeti.spectralProjection` and projection helpers **only where exact
upstream equivalents exist**. Their current definitions are in
`ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean`; consumers
include the `SinTheta`, `Spectral`, YWS, Davis--Kahan and roadmap-bridge
libraries. The canonical upstream restricted-spectrum/containment API is
in `TauCeti.Analysis.InnerProductSpace.PointSpectrum`.

Perform a dependency-closed conversion rather than leaving permanent
forwarding definitions. Determine whether a canonical `E →L[𝕜] E`
projection can replace a local `E →ₗ[𝕜] E` projector without forcing
unnecessary transport at every paper boundary; settle carrier semantics,
not just names. If a full retirement is too invasive, finish an independently
compiling subset and record precisely which declarations are still needed.

### Priority D — other recently merged, lower-risk consumption

- **#19010 / #18946:** inspect YWS rectangular/Hermitian dilation and
  operator-norm perturbation proofs; replace matching identities, retain
  stronger statements and any remaining nonduplicate Gram mathematics.
- **#19145 / #19000 / #18982 / #19005:** inspect polarized PVM measure,
  spectral integration, variation, almost-everywhere, and measurable
  reindexing consumers. Reuse the accepted sharp variation bound and
  `IsFiniteMeasure` instance *where they discharge an actual old proof*.
  Do not delete local spectral-measure construction or unbounded Borel
  calculus simply because related bounded abstract PVM support landed.
- **#18917 / #18918 / #18915 / #18935 / #18937 / #18907:** inspect
  unbounded `LinearPMap`, domain-aware Sylvester, real-spectrum and
  continuous-approximation donor slices. Preserve domain conditions,
  self-adjointness, and true higher-level unmerged results.
- **Canonical reducing restrictions (#13980 and existing Mathlib API):**
  finish the older `ReducesSubspace` / `reducingRestriction` bridge retirement
  in `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean`
  **only after** migrating every affected consumer. Do not reintroduce
  the already-retired bundled closed-operator carrier. Plan and compile
  smaller dependency-closed groups if this area is large.
- **Other #776 roadmap families:** inspect the accepted polar,
  majorization, principal-angle, operator-ideal, approximation-number,
  Sylvester and matrix-spectral-statistics APIs for further *actual*
  duplication. This is the next queue when the four priorities above
  no longer offer an unblocked slice; the eight-roadmap census is a guide.

### What to skip or defer

Do not consume mathematics found only in open PRs; do not build an unmerged
TauCeti PR locally and treat that as accepted. No mass rewrite for speculative
future interfaces. Keep the full unbounded Davis--Kahan sine theorem,
source-correction evidence, residual/domain conditions and arbitrary-ideal
results if the accepted version does not actually subsume them. Do not
spend the night optimizing lint-only gates, creating validators, researching
publication prose, or editing independent repos.

## Compilation, checkpoint, and continuation loop

For **each finished slice**, repeat until there is no further unblocked
accepted work worth changing:

1. Identify the exact local declaration, the upstream replacement, and
   mathematical scope comparison. If no genuine equivalence, choose another
   slice rather than forcing a false deduplication.
2. Rewrite consumers and remove the displaced implementation/adapters.
   Keep existing declarations intentionally cited by source censuses, with
   concise proofs; manually update any affected statement map or census.
3. Run `lake exe cache get`, then `lake build <changed-module>
   <immediate-public-dependent-modules>` serially. Read compiler errors;
   correct them. For long builds use `tmux` with `tee` and do not run multiple
   Lake jobs against one shared `.lake` simultaneously.
4. Inspect `git diff --check`, `git diff --stat`, deleted-symbol references,
   and the actual theorem statements. Compile a direct paper-facing consumer
   for every changed source/census theorem. Keep normal success output quiet.
5. Use explicit path-scoped `git add -- <files>`; inspect the staged diff;
   commit **only the compiled slice**. Every commit has one `Co-authored-by:`
   trailer naming Luna's **actual executing model/config**, as required by
   `AGENTS.md`; do not copy the assistant's GPT-6 identity into Luna's
   commit if Luna is running a different model. Do not stage unrelated user
   files, including untracked user code.
6. Update `dev/tauceti/dkps-upstream-contribution-census.md` by hand to
   record #19268 as accepted (it was previously listed as open), with its
   exact upstream declarations and genuine DKPS ancestry. Record other
   retirements, original statements and new owners. Preserve direct vs.
   independent vs. indirect provenance and pre-DKPS Spectra lineage.
   Historical accepted-PR references do not become local source files.
7. Continue to the next accepted slice. If a slice blocks after serious
   focused proof attempts, keep the last compiling checkpoint, write a
   concise blocker and leave it **uncommitted or explicitly marked as
   unfinished**, then work on another independent slice. Do not hide an
   unsuccessful migration inside a green/complete commit.

A targeted build invocation is, for example:

```bash
cd ~/code/aiq-dkps-formalization
lake exe cache get
lake build \
  ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace \
  ForTauCeti.Analysis.InnerProductSpace.SinTheta.DirectedBounds \
  ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation \
  YuWangSamworth2015.Core.SingularSubspace \
  RoadmapBridge.Integration
```

Do not run every module at every edit. Build direct dependents for the slice,
then run broader gates at meaningful checkpoints. Any baseline theorem
previously user-confirmed as compiled remains established; a newly introduced
compiler error is a regression to repair, not a reason to relabel the
original theorem as unverified.

After the final migration checkpoint, run the repository's real aggregate
build, with cache obtained first:

```bash
cd ~/code/aiq-dkps-formalization
lake exe cache get
lake build
```

If full build fails, narrow to the first new failure and fix it; only report
a remaining failure if no further safe fix is feasible in this run. Do not
mischaracterize an unrelated optional linter warning as a proof failure.
Respect the repository's `.llm_resource_tally` publish rule at handoff if it
is configured, and do not let accounting failures block mathematics.

## Final handoff to the human maintainer

Give a **short factual account of the actual migration**, not a restatement of
this contract: exact TauCeti and Mathlib pins; which accepted declarations
replaced which DKPS proof bodies; deleted modules/LOC and remaining bridges;
focused/aggregate Lean builds run and their outcomes; path-scoped commits;
and **concrete** next unblocked or blocked opportunities. Include links to
the relevant accepted PRs. Do not claim completion based on a census count,
Git diff alone, a linter, or a proposed future port. **No auto-push, merge,
new TauCeti PR, or review-thread action** is authorized by this assignment.
Produce useful verified local commits for inspection instead.

**Continue until productive accepted-upstream consumption is exhausted or
execution resources end; do not stop just because a first slice passes.**
