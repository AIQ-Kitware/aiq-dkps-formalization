# DKPS upstream-consumption review — 2026-10-22

## Scope and evidence

This reviews the uploaded `aiq-dkps-formalization` source snapshot at DKPS
`68a32d1a` (`main`, clean working tree), **not** the independent `~/code/TauCeti`
checkout. The source window reviewed is from the overnight instruction commit
`4ddfe220` through `68a32d1a`. This document supersedes the *execution queue*
in `overnight-accepted-upstream-consumption-2026-10-21.md`, but not its
historical rationale. The reducing-restriction checkpoint
`upstream_consumption_reducing_2026-10-21.md` is similarly historical.

The snapshot pins:

| Input | Exact revision |
| --- | --- |
| DKPS source | `68a32d1a` |
| TauCeti | `773bcb657352235c6348ff45be9b7f19f147c19e` |
| Mathlib | `2cabef97b63d3275776b8b060d802de6a6fa1055` |
| Lean | `leanprover/lean4:v4.36.0-rc1` |

The pinned TauCeti **manifest** was checked: its Mathlib pin matches the DKPS
root lock; the toolchains also agree. TauCeti upstream `main` had advanced past
that pin when this review was prepared. There is no requirement to re-pin merely
for unrelated main commits; re-pin when a relevant accepted API warrants it,
keeping TauCeti/Mathlib/toolchain coherent.

The overnight Git delta changed 118 Lean files, adding 5,077 and removing
5,459 Lean lines (**net −382**, before this review overlay). This is a diff
statistic, *not* a count of formalized paper results or proof quality.
The commits and provenance census report successful focused and aggregate builds
for the underlying migrations. This reviewer has not run Lean: the delivered
review overlay is for the maintainer's next compilation pass.

## Completed consumption and proof boundaries

| Accepted source | DKPS outcome in the reviewed tree | What is intentionally retained |
| --- | --- | --- |
| [SSP-C19 #19268](https://github.com/TauCetiProject/TauCeti/pull/19268) | Canonical residual theorem is exercised **directly** in `RoadmapBridge.Integration`; the intervening `sinTheta_pointSpectralSubspace_le` wrapper was removed (`655c57d8`). The accepted theorem import belongs at that direct consumer, not in the donor perturbation module. | Arbitrary invariant-space, ordered-gap, general spectral-distance and unbounded variants |
| [SSP-C20 #19252](https://github.com/TauCetiProject/TauCeti/pull/19252) | Local equal-rank projector duplicates removed (`6b4a270e`). | Stronger/differently scoped and paper-facing projector results |
| [SSP-D12 #19229](https://github.com/TauCetiProject/TauCeti/pull/19229) | YWS singular-subspace statements use canonical upstream Gram perturbation and sine-map API; local singular-subspace definitions/bridges removed in the preceding campaign. | Paper statements and genuinely nonduplicate YWS results |
| [SSP-D06 #18946](https://github.com/TauCetiProject/TauCeti/pull/18946), [D13 #19010](https://github.com/TauCetiProject/TauCeti/pull/19010) | YWS dilation uses canonical Hermitian dilation and norm transport (`692f38b5`); local Gram identity duplication was subsequently retired (`3e88342c`, `c47e787d`). | Stronger pointwise Gram, statistics and source results |
| [SA-E28 #18915](https://github.com/TauCetiProject/TauCeti/pull/18915), [reducing API #13980](https://github.com/TauCetiProject/TauCeti/pull/13980) | Local self-adjoint maximality file and four-field `ReducesSubspace` predicate removed; many consumers migrated to `LinearPMap.IsReducing`, `A.restrict`, and accepted self-adjoint restriction lemmas. | Domain-sensitive local restriction theorems and a still-used `reducingRestriction` entry point |
| Sylvester foundations, including [#14951](https://github.com/TauCetiProject/TauCeti/pull/14951) | The finite Sylvester solver and bounded operator wrapper/module were removed (`4bcd2338`, `2d763193`); consumers use `ContinuousLinearMap.sylvester`. | Gap-specific, UI-seminorm and unbounded analytic estimates that are not consequences of the basic equation API alone |
| Canonical point spectrum | Local `restrictedPointSpectrum` and `PointSpectrumIn` representations retired; consumers use opaque-safe `Module.End.*` theorem API (`1bf4bb1f`). | `restrictedPointSpectrum_restrict` and `pointSpectrumIn_restrict_iff`: actual subtype-restriction transport; linear-map projector and local invariant-subspace presentation, where still used |

The local `ForTauCeti.Analysis.InnerProductSpace.Spectral.EigenFrame` remains
because it contains independent gap-separated theorems. The two parallel
representations are retired by the follow-on overlay, as described below.

## Concrete review corrections in this overlay

1. **Stale extraction manifest:** `extraction-manifest.json` still listed the
   nonexistent `LinearPMap.SelfAdjointMaximal` and `Sylvester.Operator` files as
   active cluster members and their historical records as `staged`. Their four
   current-cluster entries are deleted, their historical records are marked
   `accepted-upstream-local-copy-removed`, and stale dependency/user metadata
   is made consistent with actual imports. Historical proof declarations remain
   in their records for lineage; they are *not* asserted to exist downstream.
2. **Incorrect C19 consumption description:** the contribution census described
   the intermediate residual wrapper as the final maintained implementation,
   contradicting its later retirement entry. The row now identifies the direct
   `RoadmapBridge` consumer and the deleting commit.
3. **Unused transitive import:** after C19 wrapper retirement, the donor
   `SinTheta.Perturbation` module contained no direct use of the accepted
   `UnitarilyInvariantSeminorm.SinTheta.Spectral` API but publicly imported it.
   The import is relocated to `RoadmapBridge.Integration`, where the theorem is
   actually used. This is an import-boundary cleanup, not a proof rewrite.
4. **Superseded handoffs:** the reducing and overnight execution documents
   still described already-completed migrations as next actions. They now
   point here while retaining their historical checkpoints.
5. **New acceptance:** [SSP-D01 #18942](https://github.com/TauCetiProject/TauCeti/pull/18942)
   was Bors-closed October 22 and its named declarations are present in the
   *existing* pinned TauCeti tree. The provenance census and local EigenFrame
   documentation now distinguish its accepted interface from unported
   gap-separated results.

## Next implementation queue, in dependency order

### 1. SSP-D01 eigenfamily/eigenframe consumption — submitted for compilation

The next overlay migrates the maintained callers of the formerly local
`TauCeti.IsEigenFamily` and `TauCeti.IsOrderedEigenframe` to the accepted
`Module.End.IsEigenfamily` and
`LinearMap.IsSymmetric.IsOrderedEigenframe` (SSP-D01 [#18942](https://github.com/TauCetiProject/TauCeti/pull/18942)).
The duplicated structure, ordered-frame predicate, constructors, dimension,
invariance, and restricted-spectrum lemmas are no longer maintained locally.
`ForTauCeti/.../Spectral/EigenFrame.lean` now supplies **only two independent
population-gap results**, specialized to `Fin d` but proved over the canonical
ordered-frame predicate:

- `LinearMap.IsSymmetric.IsOrderedEigenframe.span_eq_spanIndices`;
- `LinearMap.IsSymmetric.IsOrderedEigenframe.pointInternalGap_span`.

The latter uses the upstream eigenfamily containment and span-invariance
lemmas, and re-expresses the complementary orthonormal basis locally. It does
not assume Mathlib's eigenvector choice on the perturbed side. The YWS
paper-facing theorem names and mathematical conclusions remain unchanged.

Changed consumer cluster: `Spectral/{EigenFrame,ResidualGap}.lean`, YWS
`Core/{Residual,Statistics,Procrustes}.lean`,
`Symmetric/{Theorem1,Theorem2}.lean`, and
`Rectangular/{Theorem4,SourceTheorem3}.lean`.
This overlay has been source-checked but requires the maintainer's Lean
compilation; the earlier verified mathematical results are not being called
unverified merely because this new refactor has not yet been compiled.

Focused build (always cache first):

```bash
lake exe cache get
lake build \
  ForTauCeti.Analysis.InnerProductSpace.Spectral.EigenFrame \
  ForTauCeti.Analysis.InnerProductSpace.Spectral.ResidualGap \
  YuWangSamworth2015.Core.Residual \
  YuWangSamworth2015.Core.Statistics \
  YuWangSamworth2015.Core.Procrustes \
  YuWangSamworth2015.Symmetric.Theorem1 \
  YuWangSamworth2015.Symmetric.Theorem2 \
  YuWangSamworth2015.Rectangular.Theorem4 \
  YuWangSamworth2015.Rectangular.SourceTheorem3
```

After the focused build, run `lake build` for downstream closure. If this
refactor compiles, the next candidate is to compare the YWS
`CorrespondingEigenblock` (which fixes a chosen eigenbasis/index set) with
upstream `LinearMap.IsSymmetric.CorrespondingEigenblocks` (which quantifies over
*arbitrary* matching frames). Preserve the stronger choice-independent YWS
statements; never collapse these definitions based on matching names alone.

### 2. Finish genuinely redundant restriction presentation, selectively

The four-field `LinearPMap.ReducesSubspace` is already gone. Do **not** redo its
migration. `ForTauCeti/.../LinearPMap/Closed.lean` still contains the concrete
`reducingRestriction` entry point, its domain and application bridges, and the
stronger adjoint-domain argument. These are referenced by genuine unbounded
consumers, including `LinearPMap/UnitaryTransport.lean` and
`DoubleAngle/ReducingCutoff.lean`. Move an independently buildable consumer
cluster onto native `A.restrict` before deleting a helper; in particular do not
assume the orthogonal projection commutes with arbitrary *unbounded* actions
outside the declared domain.

The remaining finite-dimensional `TauCeti.IsInvariant` and linear-map-valued
`projection`/`complementaryProjection` in
`ForTauCeti/.../Spectral/Subspace.lean` need an **actual carrier and
hypothesis-scope comparison** to `LinearMap`/`ContinuousLinearMap` and
`Submodule.starProjection` APIs. Importing an accepted subspace theorem does
not by itself make the algebraic projector or the restriction transport
redundant. Keep the local `pointSpectrumIn_restrict_iff` and
`restrictedPointSpectrum_restrict` until equivalent subtype results are
identified in the pinned upstream tree.

### 3. Find *specific* further accepted theorem replacement candidates

Use the exact source and conclusion; do not mass-delete a donor because an
adjacent roadmap milestone merged.

- **PVM polarized measure variation [#19145](https://github.com/TauCetiProject/TauCeti/pull/19145):**
  the current maintained Lean tree has no direct use of
  `polarizedComplexMeasure_variation_univ_le` or
  `instIsFiniteMeasurePolarizedVariation`. Compare precise integral/measure
  consumers before changing an unbounded spectral-measure argument. There is
  no known duplicate variation proof to remove wholesale.
- **Other accepted OI/polar/majorization and self-adjoint APIs:** look for a
  named local theorem with the same carrier, hypotheses, and strength; prefer
  short upstream applications and delete only displaced implementations.
  Preserve arbitrary-ideal and unbounded proofs if a finite-dimensional
  upstream statement does not cover them.
- **Source-faced publication obligations:** do not replace theorem statements
  merely to make migration easy; preserve paper and census meaning.

### 4. Gate later work on PR integration

At review, #19277 (reduced extensions/form bounds), #19817 (symmetric
C24 two-orientation), #19242 (pairwise pi/2), #19299 (C27 Gram transfer),
#19338 (right singular-vector population-gap), #19329 (sine-to-tangent
transfer), and #18927 (spectral grid cells) remained **open**. They are not
accepted replacement libraries. Only resume work based on one once its
relevant declarations occur on the pinned accepted `main` tree. Do not edit
the separate `~/code/TauCeti` checkout under this DKPS task.

## Handoff checks for this review overlay

This overlay changes **no theorem proof or statement**. It changes two Lean
import lines, a Lean source comment, and documentation/JSON metadata. It is
still worth compiling both affected imports (including the new direct C19
consumer) before committing:

```bash
cd ~/code/aiq-dkps-formalization
lake exe cache get
lake build \
  ForTauCeti.Analysis.InnerProductSpace.Spectral.EigenFrame \
  ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation \
  RoadmapBridge.Integration \
  YuWangSamworth2015.Symmetric.Theorem2
```

Then run the ordinary aggregate gate when convenient:

```bash
lake exe cache get
lake build
```

The `RoadmapBridge.Integration` warning about the legacy `Mathlib` import and
module header is **nonblocking** and unrelated to this review's changes. Do
not expand this pass into a style-only rewrite. Use ordinary Lean compilation
rather than routine `#print axioms`, `#check` inventories, or new checker
scripts. Do not stage unrelated working-tree files. A successful compile of
this overlay does not by itself mean the SSP-D01 migration is complete.
