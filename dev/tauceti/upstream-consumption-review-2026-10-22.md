# DKPS upstream-consumption review — 2026-10-22

## October 25 maintenance checkpoint

`c76d49cde` publishes the module-consumer APIs in the donor layer; `6388669d7`
adds only measured-resource bookkeeping. An isolated source snapshot of that
checkpoint, using its original Tau Ceti revision
`f99e274230de08a9a8189a97dbfc910536646449` and unchanged Mathlib/toolchain,
passed `lake exe cache get` followed by `lake build` (21,035 jobs).
`lake build ForTauCeti` separately passed all 8,453 jobs with the donor's
warnings-as-errors and Mathlib linter settings. The full checkpoint still
emits the existing legacy-module and downstream proof warnings.

The project-wide module and warning migration is now committed:

- `3b6835975` consumes the accepted double-angle Gram prerequisites and retires
  ten duplicate donor declarations without aliases;
- `927ded55f` completes the donor interfaces needed across module boundaries;
- `49683f340` migrates the production libraries to explicit modules and enables
  workspace-wide warnings-as-errors.

The full default `lake build`, after `lake exe cache get`, passed **21,039 jobs**
on October 25. This verifies the production checkpoint, including all default
companion libraries. It does not assert source completeness or historical novelty.
Tau Ceti is pinned to `efded067c28ffca3483fd731674eb13b42543fbb`; Mathlib remains
`2cabef97b63d3275776b8b060d802de6a6fa1055`, with Lean
`leanprover/lean4:v4.36.0-rc1`, matching Tau Ceti's inputs.

The migration uses public application and characterization lemmas for opaque
upstream definitions. The small reusable additions include
`ContinuousLinearMap.realAlgebra_eq_of_isScalarTower`,
`TauCeti.BorelCalculus.continuous_reCoord`, and `Submodule.isOffDiagonal_iff`.
Compatible real-algebra structures are identified explicitly in functional-calculus
proofs; imported hidden bodies are not treated as available reductions. Small
computational constructors are exposed individually when their defining behavior
is needed downstream. Paper-facing mathematical conclusions are preserved.

`91b2f3332` exposes the printed dimension condition used by the existing audit;
`016e6a66c` completes the diagnostic/Challenge migration and updates comparator
fixtures to the accepted API owners. After `lake exe cache get`, a combined build
of all default targets, all maintained touched modules, `Challenge`, and
`DavisKahan.Audits.All` passed **21,170 jobs**, with warnings treated as errors.
Intentional `Challenge/**/Conformance.lean` holes remain open, following
`Challenge/README.md`; the affected fixtures disable only the intentional-placeholder
diagnostic. Their solution modules retain the comparator's trusted-dependency policy.

`f3442c71b` aligns the remaining fixture telescopes and the ambient sine expression
with the exported APIs. `lake build Challenge`, after its cache fetch, passed
**19,763 jobs**. This fixture-only follow-up leaves the production build unchanged.
A full signature preflight followed by affected-config reruns verifies matching raw
universe signatures and full types for all **42 implemented targets** across the
17 configs. The three explicitly declared missing solution targets remain `SKIP`;
this is not evidence that their source-facing proof obligations are closed.
No full external comparator run is claimed.

The explicitly historical snapshot
`DavisKahan.Explorations.Historical.SourceUnitaryInvariantNormFanDominance` is
excluded from that maintained-module check. Its existing header records that it
predates the norm-API migration, does not compile, and is retained as an archive;
this checkpoint does not claim to repair that historical mathematics.

Two auxiliary-check limitations are outside this build checkpoint:

- The import-layer check reports the pre-existing dependency from
  `DavisKahan.OperatorIdeal.SymmetricNormingScalarTransport` to
  `DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm`.
  This source/generic ownership issue remains for the canonical-consumption work.
- The syntactic declaration-name checker reports imported accepted APIs as
  absent because it indexes local source, together with stale historical migration
  mappings. For example, `LinearMap.exists_orthonormal_sum_inner_eq_kyFanSum`
  exists in the pinned `TauCeti/Analysis/InnerProductSpace/KyFan.lean`.
  These reports are not Lean build failures. Actual declaration resolution and
  comparator signatures must be checked against installed sources.

This maintenance checkpoint supersedes the earlier instructions below to ignore
legacy-module warnings. Paper and visualization updates remain a separate task.
The original untracked `ProbeModulus.lean`, `feedback.txt`, and
`luna_tauceti_upstream_first_guide.md` are preserved and are not build inputs.


## October 25 follow-up: Hilbert–Schmidt consumption

The canonical energy and real norm are now consumed from accepted Tau Ceti's
`HilbertSchmidt.Basic`; isometry invariance and block Pythagoras are consumed
from its `Isometry` and `Pythagoras` modules. The duplicate local Pythagoras
module, energy definition, real norm definition, and displaced laws are removed.
The provenance census records the exact API and scope comparisons. No paper or
visualization files are changed.

Validation: `lake exe cache get` followed by the full default `lake build` passed
**21,043 jobs**, with warnings treated as errors. The retirement removes a net
361 lines of maintained Lean source.

The committed energy checkpoint also passed explicit `Challenge` and
`DavisKahan.Audits.All` builds (20,823 jobs). A follow-up removes the local ideal
family constructor, completeness proof and unused membership/gauge aliases;
source consumers use accepted `SymmetricOperatorIdealFamily.hilbertSchmidt`
directly. The two paper triangle proofs now use the accepted energy-based law.
The full default build after its cache fetch passed **21,051 jobs**, with warnings
treated as errors. Across the two Hilbert–Schmidt retirements, maintained Lean
source shrinks by a net **508 lines**. The family checkpoint `e1b3f88d9` also
passed explicit `Challenge` and `DavisKahan.Audits.All` builds (**20,831 jobs**),
after its cache fetch.

The next remaining representation comparison is the local extended norm and
membership presentation against the accepted family's gauge and finite-gauge
submodule, together with their approximation-number energy consumers. The finite-source
Frobenius identity in local `SchattenNorm.lean` still permits an incomplete target;
the accepted theorem requires a complete target, so it is not deleted as an exact
duplicate in this pass.


## October 25 follow-up: remove the extended-norm representation

The remaining parallel Hilbert–Schmidt norm, membership predicate, chosen-basis
helpers and closure/gauge APIs are removed. The source full-displacement and
vacuity theorems state their extended norms directly through accepted
`OperatorIdealFamily.hilbertSchmidt.gauge`. The source finite-norm comparisons
and both scalar branches use native energy formulas, with no finiteness
restriction added to the extended-norm conclusions. The column model chooses
its own Mathlib basis without a donor foundation.

The residual donor module contains only pointwise-basis Fatou, real-norm
negation, and a contraction-norm consequence. The first is now stated directly
on energy without completeness assumptions; the last uses native finite energy.
Validation: `lake exe cache get` followed by the full default `lake build` passed
**21,051 jobs**, with warnings treated as errors.

No compatibility aliases replace retired APIs. The comparison identified at this
checkpoint was the approximation-number energy/truncation proofs against accepted
`ApproximationNumber.HilbertSchmidt`; the follow-up below closes that retirement.
Paper and visualization files remain unchanged.

The reconciliation follow-up deletes `ApproximationNumber.EnergyComparison`
entirely. Its two live consumers and the paper energy identity use accepted
`tsum_singularValue_sq_eq_hilbertSchmidtEnergy` directly. The accepted compactness
module `HilbertSchmidt.Columns` also compiled explicitly. Unused support for the
retired proofs is removed without asserting that every auxiliary lemma was ported.
The source ideal consumers import the accepted family, and Theorem 6.2 explicitly
imports the genuinely remaining donor contraction estimate. The next direct
migration is the Hilbert–Schmidt column model: `ofLp b` and accepted
`HilbertBasis.columnOperator b` act on the same Mathlib `ℓ²` carrier. The remaining
Schatten comparison needs a parameter-scope check: the donor defines its power-sum
functional for every real `p`, whereas the accepted normed family takes `1 ≤ p`.
The follow-up passed the full default build (**21,049 jobs**), with warnings
treated as errors, after the cache fetch. Together with `57447d82a`, it removes
a net **992 lines** of maintained Lean source.
The committed reconciliation checkpoint `1f2946e00` also passed explicit
`Challenge` and `DavisKahan.Audits.All` builds (**20,829 jobs**), after the cache fetch.
The full comparator signature preflight then matched all **42 implemented targets**;
the three explicitly declared missing solutions remain `SKIP`. A tracked-source
search confirms that the retired extended norm, predicate, basis helpers and
comparison module have no remaining Lean references. The separate syntactic
name-drift checker still reports accepted imported declarations as absent from
its local-only index; actual Lean resolution and signature comparisons passed.

## October 25 follow-up: canonical column model

The local `ofLp`/`columns` representation and `ofOperator` inverse wrapper are
removed. `HilbertSchmidt.Lp`, `.Space`, and `.Conjugation` are deleted, and all
maintained consumers use accepted `HilbertBasis.columnOperator` directly on the
same Mathlib `ℓ²` carrier. Source model, Sylvester flow, block action, spectral-gap
reassembly and the unbounded generator-domain theorem now use that canonical
operator. Norm preservation and block norm bounds consume the accepted
Hilbert–Schmidt norm laws, and the native bundled map supplies linearity and
continuity. No adapter declarations remain for the retired representation.

Validation: the focused dependency build passed 7,238 jobs; after a fresh cache
fetch, the full default build passed **21,045 jobs**, with warnings treated as
errors. The explicit `Challenge` and `DavisKahan.Audits.All` build also passed
**20,825 jobs** after its cache fetch, including the renamed diagnostic reference.

The analytic Sylvester estimates remain local. The next broad comparison is the
Schatten power-sum presentation against the accepted family, with an explicit
parameter-scope check: the donor defines all real exponents while the accepted
normed family takes `1 ≤ p`. Paper and visualization files are unchanged.


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

### 1. SSP-D01 eigenfamily/eigenframe consumption — compiled

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

The maintainer subsequently compiled the eigenframe migration and its
Acharyya2025 consumer fix. That compilation closes the basic SSP-D01
representation-retirement pass, including its corrected lint/import changes.
The module-system warnings in legacy Davis--Kahan files remain nonblocking;
do not turn individual files into `module` without migrating their imports.

### 1a. Corresponding-eigenblock comparison — completed consumption pass

The YWS `CorrespondingEigenblock` is a **strict specialization**, not a
redundant spelling of accepted TauCeti `CorrespondingEigenblocks`:

- DKPS fixes *both* subspaces to the same index `Finset` in the particular
  Mathlib-chosen eigenvector bases of the two operators.
- TauCeti permits any two ordered orthonormal eigenframes spanning the blocks,
  even when the selected indices cut a repeated *sample* eigenvalue.
- Therefore only DKPS `CorrespondingEigenblock` implies TauCeti
  `CorrespondingEigenblocks`, not conversely. Replacing the YWS predicate in
  existing theorem statements without checking the proofs would change their
  quantifier scope; the source-facing `..._frame_...` results are already
  correctly stated with arbitrary frames and must be preserved.

This follow-on overlay adds the one-way theorem
`YuWangSamworth2015.CorrespondingEigenblock.toCorrespondingEigenblocks`. It
chooses the increasing embedding of the existing finite index set, reuses
TauCeti's canonical ordered-eigenframe constructors, and explicitly transports
its spans with the existing `span_range_eigenvectorBasis_orderEmbOfFin`
identity before applying `correspondingEigenblocks_iff`.
The rectangular Gram-transfer lemmas now use the accepted
`CorrespondingEigenblocks.apply_mem_right` and `.finrank_left` / `.finrank_right`
results for invariance and equal dimension; the YWS interval-block theorem
uses the same accepted invariance result. The now-unused local
`reduces_spanIndices` induction proof is deleted. No paper-facing inequality,
eigenframe theorem, or definition changes its statement.

**Follow-on work:** the maintainer accepted the compiled corresponding-block
comparison. The next pass, recorded below, retires the definitionally redundant
ordered right/left singular-frame wrappers. `CorrespondingRightSingularBlock` /
`CorrespondingLeftSingularBlock` and their fixed-eigenbasis datum remain
intentional: do not delete `CorrespondingEigenblock` or its constructors in
`Core/TopEigenblock.lean` and the sharpness examples. An inverse to the one-way
TauCeti comparison is false without further uniqueness/separation hypotheses.

Focused build for this pass:

```bash
lake exe cache get
lake build \
  YuWangSamworth2015.Core.Statistics \
  YuWangSamworth2015.Rectangular.Theorem4 \
  YuWangSamworth2015.Core.TopEigenblock \
  YuWangSamworth2015.Rectangular.SourceTheorem3 \
  YuWangSamworth2015.Symmetric.MiddleBlockSharpness
```

The maintainer subsequently compiled this comparison pass as well. The
section below records the next rectangular source cleanup; it should be
compiled independently before running the usual aggregate `lake build`.

### 1b. Canonical rectangular ordered frames and singular-value normalization

This next overlay removes the *definitionally equivalent* local aliases
`DavisKahanTheory.IsOrderedRightSingularFrame` and
`DavisKahanTheory.IsOrderedLeftSingularFrame`, and their reflexive `_iff` lemmas.
Maintained consumers in `Rectangular/{Theorem4,SingularBlock,SourceTheorem3}.lean`
now use the **accepted** `LinearMap.IsSymmetric.IsOrderedEigenframe` directly,
at `isSymmetric_rightGram A` or `isSymmetric_leftGram A` respectively. The source
block predicates `IsRightSingularBlock` and `IsLeftSingularBlock` still model
arbitrary chosen singular vectors, including multiplicities; their
`toOrderedFrame` results keep the same Gram action and sorted indices.

In `Rectangular/Theorem4.lean`, two private compatibility theorems for
corresponding-block invariance and dimension are retired: both Gram transport
proofs now apply `CorrespondingEigenblock.toCorrespondingEigenblocks` and use
TauCeti's `CorrespondingEigenblocks.apply_mem_right`, `.finrank_left`, and
`.finrank_right` directly. The additional singular-value norm wrapper
`DavisKahanTheory.opNorm_eq_topSingularValue` is also retired; its twelve actual
maintained consumers (including `Rectangular/RankOne.lean`) use the accepted
`TauCeti.opNorm_eq_singularValues_zero` with `Module.finrank_pos`.

All mathematical hypotheses, bounds, selected source/target Gram operators,
index choices, and paper-facing theorem names are preserved. Only the
hypothesis *presentation* changes from the local frame alias to its
**definitionally identical** canonical predicate. This overlay changes no
TauCeti dependency revision, and does not attempt to replace the narrower
fixed-basis corresponding-block predicate with the broader upstream one.

Focused build for the new rectangular pass:

```bash
lake exe cache get
lake build \
  YuWangSamworth2015.Rectangular.Theorem4 \
  YuWangSamworth2015.Rectangular.SingularBlock \
  YuWangSamworth2015.Rectangular.RankOne \
  YuWangSamworth2015.Rectangular.SourceTheorem3 \
  YuWangSamworth2015.Rectangular
```

**Next unblocked migration:** compare the fixed-basis
`CorrespondingRightSingularBlock` / `CorrespondingLeftSingularBlock` consumers
in `Rectangular/RankOne.lean` against the existing arbitrary-frame rank-one
statements; eliminate a duplicate only when its source interface is subsumed.
The source-specific population-gap and rank-boundary mathematics must remain.

### 1c. Rectangular adjoint duality and rank-one Gram normalization

The rank-one comparison found **no redundant hypothesis interface** to retire.
`RankOne.lean`'s four fixed-basis variants accept a
`CorrespondingRightSingularBlock` or `CorrespondingLeftSingularBlock` with a
restricted-point-spectrum gap; the four arbitrary-frame variants instead fix a
sorted eigenvalue index and impose a gap at every other population index.
The stronger applicability of arbitrary sample frames does not make these
assumption bundles definitionally interchangeable. All eight named theorems
remain, with exactly their previous statements and paper/supporting status.

The implementation does eliminate duplicate proofs:

* `Rectangular/FrobeniusGram.lean` now proves the left-Gram **Frobenius**
  perturbation inequality from `frobenius_rightGram_sub_le` applied to the
  adjoint map, via `rightGram T.adjoint = leftGram T` and the existing
  `rectangularFrobenius_adjoint`. The independent left-Gram difference expansion,
  ideal-law estimates, and summation proof are retired. The **operator-norm**
  left-Gram proof stays as a direct application of TauCeti's accepted
  `ContinuousLinearMap.norm_self_comp_adjoint_sub_self_comp_adjoint_le`, not an
  unnecessary detour through a local duality result.
* `Rectangular/RankOne.lean` now shares one private real-number coefficient
  inequality across the right/left, fixed-basis/arbitrary-frame corollaries.
  Their four repeated arithmetic transport proofs are retired. The symmetric
  eigenvector results, Gram perturbation estimates, gap assumptions, and eight
  public theorem statements are unchanged.

This pass changes neither the TauCeti pin nor any source census declaration.
The next candidate is a declaration-by-declaration comparison of the remaining
rectangular Frobenius ideal-law helpers with accepted upstream laws, retaining
the cross-dimensional bounds where no exact match exists.

Focused build:

```bash
lake exe cache get
lake build \
  YuWangSamworth2015.Rectangular.FrobeniusGram \
  YuWangSamworth2015.Rectangular.Theorem4 \
  YuWangSamworth2015.Rectangular.RankOne \
  YuWangSamworth2015.Appendix.Lemma5 \
  YuWangSamworth2015.Rectangular.SourceTheorem3
```

### 1d. Retire duplicate rectangular Frobenius ideal laws via Schatten p=2

At the pinned Tau Ceti revision `773bcb657352235c6348ff45be9b7f19f147c19e`,
`UnitarilyInvariantSeminorm.Schatten` already supplies cross-dimensional
left-factor and two-sided ideal estimates for all `p >= 1`:
`schatten_comp_le_left`, `schatten_comp_comp_le`, and the endpoint
`schatten_two : schatten ... 2 = frobenius ...`. It also supplies
`schatten_apply_adjoint`, including the rectangular adjoint invariance
previously reproved through Hilbert--Schmidt approximation energy.

`Rectangular/FrobeniusGram.lean` consequently removes the local
`frobenius_comp_rectangular_le_opNorm_mul`,
`rectangularFrobenius_twoSided_comp_le`, `rectangularFrobenius_adjoint`,
and its private `approximationNumberEnergy_ne_top_finite`. These laws were
already subsumed by Tau Ceti's Schatten-2 results **for finite-dimensional
real/complex inner product spaces and all intermediate dimensions**. The
operator-norm factors are converted to the required pointwise bounds by
`LinearMap.toContinuousLinearMap.le_opNorm`.

The right-Gram Frobenius proof directly applies `schatten_comp_le_left 2`;
the left-Gram proof obtains adjoint invariance from `schatten_apply_adjoint 2`.
Appendix Lemma A1's contraction theorem uses `schatten_comp_comp_le 2` with
both constants set to one; its row/recovery theorem reuses the column
contraction theorem with adjointed factors instead of a second independent
ideal inequality. The row-side isometry proof also uses upstream adjoint
invariance directly. The two Davis--Kahan Hilbert--Schmidt imports are no
longer needed by the Gram module; their separate paper-specific mathematics
is not deleted.

This changes **no paper-facing theorem statement or hypothesis**, no
coefficient, no scalar field or rank assumption, and no Tau Ceti pin.
Appendix Lemma A1's source-facing interfaces and the Gram perturbation
results remain. No source census row changes: the retired items were
supporting rectangular wrappers, not paper-obligation declarations.

Focused compilation gate:

```bash
lake exe cache get
lake build \
  YuWangSamworth2015.Rectangular.FrobeniusGram \
  YuWangSamworth2015.Appendix.Lemma5 \
  YuWangSamworth2015.Rectangular.Theorem4 \
  YuWangSamworth2015.Rectangular.SourceTheorem3
```

**Follow-on:** compare the remaining source-specific linear-isometry and
Hilbert--Schmidt bridge consumers against Tau Ceti's canonical Schatten
inequalities; preserve genuinely stronger arbitrary-ideal or unbounded
statements instead of treating a finite-dimensional result as equivalent.

### 1e. Retire the duplicated Fourier kernel and operator real algebra (latest main)

The latest DKPS source (`0ab9c7cafac4`) was compared with the supplied
TauCeti `main` commit `f99e274230de08a9a8189a97dbfc910536646449`.
The latter is a descendant of the former dependency pin
`773bcb657352235c6348ff45be9b7f19f147c19e` and uses the same
Mathlib revision (`2cabef97b63d3275776b8b060d802de6a6fa1055`)
and Lean toolchain (`v4.36.0-rc1`). The manifest and `lakefile.toml` have
been updated together; no Mathlib or toolchain upgrade is required.

The maintained source consumers of the Haagerup--Zsido kernel now import
`TauCeti.Analysis.Fourier.HaagerupZsido.Fourier` and `.Mass`, and call
`HaagerupZsido.integral_exp_mul_I_mul_reciprocalKernel`,
`measurable_reciprocalKernel`, `integrable_reciprocalKernel`, and
`integral_norm_reciprocalKernel` from accepted upstream code. The two
paper-supporting Fourier results retain their existing integrand convention
(`k(t) * exp(i t x)`) by proving a pointwise order/cast equality against the
canonical upstream integral (`exp(i x t) * k(t)`). The local
`HasIntegrableReciprocalFourierKernel` predicate, gap normalization,
Fourier/Sylvester theorems, and sharp `pi/2` constant remain unchanged.

With those consumers migrated, eight local support/aggregate modules
(`Fourier/ExponentialAbs`, `Fourier/Poisson/CauchyLattice`,
`SpecialFunctions/Integral/{RationalQuadratic,SineLaplace}` and
`Fourier/HaagerupZsido/{Defs,Integrability,Fourier,Kernel}`) have no
maintained import or declaration consumer and are removed, totaling more
than two thousand lines. Their generic integration and summation lemmas
are retired because they no longer serve the paper; this does **not** assert
that every such helper was ported verbatim to TauCeti.

`TauCeti.Analysis.Normed.Operator.RealAlgebra` also provides
`ContinuousLinearMap.realAlgebra` and `.realIsScalarTower`. The corresponding
local `OperatorRealAlgebra` module is deleted, and its five direct
importers now use the upstream module. The definitions are still activated
*locally* by their consumers, preserving avoidance of global instance
changes. No public theorem names or hypotheses were intentionally changed.

The source files being removed carry Kitware copyright and DKPS provenance;
that authorship remains visible in Git history and the extraction census.
The accepted TauCeti proof implementations are used as provided, without a
claim that each upstream source was ported from these local files.

Focused compile gates: the two Fourier consumers, the five direct real-algebra
importers, and then `lake build` after `lake exe cache get`. This authoring
environment has no Lean toolchain; only the maintainer's build establishes
compilation for this new batch. The next substantial remaining candidate is
Hilbert--Schmidt energy/Pythagoras, which needs a coordinated migration of
local norm APIs rather than a wholesale deletion.

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


### Gram endpoint follow-up

The complex and real Gram nuclear-norm identities now use the accepted
Hilbert–Schmidt energy formula directly. The local `schattenENorm_one/two`
wrappers are removed, and maintained production code no longer imports the local
`Family.Schatten` donor. Its positive-exponent results, including `0 < p < 1`,
remain because the accepted normed family has the narrower `1 ≤ p` hypothesis.
The existing real approximation-number view and unmerged Gram theorem remain;
no new compatibility declarations replace the deleted wrappers.

The Gram endpoint follow-up passed the focused three-module build (7,544 jobs)
and full default build (21,045 jobs), with warnings treated as errors, after
the respective `lake exe cache get` calls.


### October 25: remove the local operator-norm family

The accepted `SymmetricOperatorIdealFamily.opNorm` has the same arbitrary-Hilbert,
scalar-generic, diagonal-universe scope as local `operatorNormFamily`. Its
`opNorm_toOperatorIdealFamily` equation identifies the underlying family with
accepted `OperatorIdealFamily.opNorm`; the accepted completeness instance then
applies explicitly at the paper constructor and specialization sites. The donor constructor,
completeness specialization, gauge wrapper, and the two paper real-gauge/membership
endpoint wrappers are deleted, with no replacement aliases or bridge definitions.
All consumers now instantiate the accepted symmetric family directly. The paper
core completeness proof uses native `OperatorGauge.Carrier` rather than importing
the retired layer for its transitional `Elem` spelling.

The two unbounded Neumann estimates use Mathlib's `opNorm_comp_le` twice, removing
the otherwise unused local two-sided norm helper. Source theorem conclusions and
ideal scope are unchanged. The legacy historical norm exploration has only its
import redirected; it remains an explicitly unmaintained archive.

Accepted scope was checked in `TauCeti.Analysis.OperatorIdeal.OperatorNorm` at
unchanged pin `efded067c28ffca3483fd731674eb13b42543fbb`; pre-retirement local
source is preserved at DKPS `226aeb096`. This records consumption of accepted
overlap, not a new audit of historical proof descent. Remaining family-carrier
adapters and the genuinely unmerged compact ideal family are separate obligations.

The operator-norm retirement passed the focused build (7,390 jobs) and full
default build (21,043 jobs), with warnings treated as errors, after their
respective cache fetches.


### October 25: retire duplicate compactness and finite-rank approximation proofs

At the unchanged accepted pin, `ApproximationNumber.Compact` provides
`tendsto_singularValue_nhds_zero_iff`,
`isCompactOperator_of_tendsto_singularValue`,
`IsCompactOperator.tendsto_singularValue`, and
`isCompactOperator_iff_tendsto_singularValue`. These cover the donor sequence
criterion, approximable-implies-compact implication, and Hilbert-target converse.
The forward Hilbert-target result still requires no target completeness, and the
accepted arbitrary-domain version permits a seminormed source. The compactness
implication only needs a locally compact field, covering the donor's proper-field
hypothesis. The native sequence formulation uses operator-norm convergence of the
approximants, equivalent to convergence of their norm differences to zero.

The donor `ApproximationNumber.Compact` and `.CompactHilbert` modules are removed.
Their unused quantitative finite-net helper is retired with its proof, without
claiming a separate accepted API for that exact helper. The compact eigenspace
and diagonal consumers apply native convergence results, using the existing real
view only where their unmerged conclusions still mention real approximation
numbers. The remaining compact-adjoint theorem and equivalence use native
singular values exclusively; their real/complex and arbitrary-universe scope
is preserved. No compatibility theorem or alias replaces a retired declaration.

Accepted `Normed.Operator.Compact.FiniteRank` also subsumes both proofs in donor
`Normed.Operator.FiniteRankCompact`. The accepted theorem
`LinearMap.HasFiniteRange.isCompactOperator` permits topological vector-space
targets over locally compact fields, so it covers the donor's normed-space scope.
Both live consumers (the second-primitive snapshots and free-beam affine part)
apply it directly. That donor module is deleted as well.

Pre-retirement source, original Jon Crall / Claude Opus 5 authorship and license
remain at DKPS `a824d8090`; accepted source was checked at Tau Ceti
`efded067c28ffca3483fd731674eb13b42543fbb`. This records accepted mathematical
overlap and direct consumption, without inferring historical proof descent.

The compactness retirement passed the focused five-module build (7,788 jobs)
and full default build (21,037 jobs), with warnings treated as errors, after
the respective cache fetches.


### October 25: consume the accepted isometric-transport adaptation

`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry` explicitly credits
adaptation of this repository's donor `ApproximationNumber/Isometry.lean` under
the Kitware Apache-2.0 license. Its private sandwich inequality and two-sided
inverse-isometry proof follow the donor construction, now using canonical
nonnegative singular values. The accepted theorem
`singularValue_comp_linearIsometryEquiv T e f n` also generalizes the four normed
spaces to seminormed spaces while preserving arbitrary nontrivially normed
fields, independent universes, and absence of completeness assumptions.
This is an explicit adapted-source relationship, beyond merely sharing a topic.

The local `approximationNumber_comp_linearIsometryEquiv` and its private
contraction helpers are removed with their entire donor module. The remaining
diagonal-realization uniqueness proof uses the native theorem directly, through
the existing real approximation-number equation; no replacement alias is added.
The historical norm exploration has its import redirected and remains unmaintained.
The unmerged uniqueness theorem itself is retained.

Pre-retirement source is DKPS `42f55fbe8`; the accepted file and its explicit
provenance were compared at Tau Ceti `efded067c28ffca3483fd731674eb13b42543fbb`.
The accepted header credits Jon Crall and GPT-6; original local Jon Crall
attribution and the Kitware license remain preserved in history and this ledger.

The isometric-transport retirement passed its focused build (6,744 jobs) and
full default build (21,037 jobs), with warnings treated as errors, after the
respective cache fetches.


The three retirement checkpoints (`a824d8090`, `42f55fbe8`, `b82f80b42`) also
passed explicit `Challenge` and `DavisKahan.Audits.All` builds (20,813 jobs),
after `lake exe cache get`. Their combined maintained Lean diff removes a net
557 lines and five donor modules. Paper and visualization files were untouched;
the three original untracked files remain outside the builds and commits.

The broader consumption goal remains open. One precise next comparison is local
`le_approximationNumber_of_lt_rank` in `ApproximationNumber.MinMax` against
accepted `le_singularValue_of_lt_rank` in Tau Ceti's module of the same name.
Both conclude the coercivity lower bound from `(n : Cardinal) < rank V`; the
local input quantifies over subtype vectors, whereas the accepted input uses
`∀ x ∈ V`. The accepted result permits a seminormed target and only a
nontrivially normed field. Migrate its consumers to the native sequence before
removing the real-valued wrapper, and compare the other min–max declarations
individually rather than treating the whole donor as redundant.

The full comparator signature preflight matched all 42 implemented targets
on raw universe signatures and full types. Three explicitly declared missing
solutions remain skipped; no external comparator run or source-completeness
claim is inferred. The auxiliary local-only name parser still has its recorded
imported-declaration limitations; it is not a substitute for these compiler checks.


### October 25: canonical min–max consumption

The duplicated coercive-subspace and independent-family lower bounds and the
projection-form infimum proof are removed in favor of accepted
`ApproximationNumber.MinMax`. Consumers apply native singular-value bounds,
using homogeneous coercivity when already available and the native unit-vector
variant for the tangent residual argument. The compact eigenvalue upper bound
now uses the restriction-form native tail estimate directly.

The duplicate identity/projection `Examples` module is deleted. Both source
block-shift cutoff consumers use the native rank cutoff. Native identity and
projection formulas cover arbitrary cardinal rank, including infinite rank and
zero spaces, with no completeness hypothesis. No compatibility aliases are added.
Three unmerged projection consequences remain in the donor `MinMax` module;
source theorem statements, sign conditions, and incomplete-target scope are
preserved. Details and provenance are in the contribution census. Papers and
visualizations remain untouched.

The adjusted trial-space and tangent leaves passed the focused build (7,152 jobs).
The full default build (21,037 jobs) then accepted all migrated consumers, with
warnings treated as errors, after the respective cache fetches.


### October 25: canonical Eckart–Young, rank and finite-diagonal APIs

The three donor modules `ApproximationNumber.FiniteDimensional`, `.Rank`, and
`.DiagonalExample` are deleted. Consumers use accepted
`singularValue_eq_linearMap_singularValues` directly; no local counterpart is
retained. The unused lower Eckart–Young wrapper in the real-valued core is also
removed, including its re-export.

The accepted rank characterization drops the donor's source finite-dimensionality
assumption while retaining scalar completeness. The accepted diagonal formulas
cover orthogonal basis images and rectangular diagonal maps, subsuming the unused
square example. Source theorem statements remain unchanged; the roadmap regression
examples now use canonical APIs. Exact scope/provenance comparisons are in the
contribution census. Existing real-valued source views and the local plural
singular-value accessor remain future representation migrations; this checkpoint
does not call those interfaces canonical or the broader goal complete.

The Eckart–Young/rank retirement passed the focused consumer build (7,644 jobs),
including explicit compilation of accepted `FiniteDiagonal`, and the full default
build (21,031 jobs), with warnings treated as errors, after the respective cache
fetches. The full build also validates removal of the unused core re-export.


The combined min–max and Eckart–Young retirements remove a net 1,083 Lean lines
and four donor modules. Explicit `Challenge` and `DavisKahan.Audits.All` builds
passed (20,807 jobs), after the cache fetch. The three original untracked files
remain untouched and no paper or visualization files were edited.

The strongest next unconsumed accepted result is
`TauCeti.HasMinMaxLowerBound.of_completeSpace` in accepted
`ApproximationNumber.MinMax`: it proves converse localization for any complete
`RCLike` inner-product source and a possibly incomplete seminormed inner-product
target. Local `MinMaxUpper` still reproves the complex threshold statement;
`MinMaxReal` reproves it through complexification. Their consumers use the
separate real-valued predicate `ContinuousLinearMap.HasMinMaxLowerBound` and
`HasMinMaxLowerBoundEverywhere` class in `FiniteRestriction`. The next migration
must consume the native predicate/result, update those consumers, and remove
the field-specific proofs and obsolete interfaces without leaving aliases.
Preserve the strict threshold `0 ≤ r < aₙ(T)` and `n + 1` witness count. This
comparison establishes an available next step, not completion of that migration.

The full signature preflight matched all 42 implemented comparator targets
on universe signatures and full types. The three explicitly declared missing
solutions remain skipped. No external comparator or source-completeness claim
is inferred; the auxiliary local-only name parser retains its documented
imported-declaration limitations.

### October 25: native converse min–max consumption

The previously identified predicate migration is implemented. Consumers use
`TauCeti.HasMinMaxLowerBound` and its accepted `of_completeSpace` theorem directly.
The duplicate complex and real threshold modules, local predicate, global
capability class, field-classification proof and fixed-field Ky Fan triangle
wrappers are removed. Native Ky Fan subadditivity is applied directly, with
numeric coercions where the remaining source interfaces are real-valued.

The native theorem preserves the strict nonnegative threshold and `n + 1`
independent-vector witness, uniformly over `RCLike`, and permits an incomplete
target. Selected downstream statements now omit unused target completeness.
Unmerged finite-restriction LUB/localization results extend the native predicate;
their conditional incomplete-source scope is preserved. Other unmerged cutoff,
scalar-transport and Schatten mathematics remains. The contribution census and
extraction manifest record exact ownership and provenance distinctions.

The focused consumer build passed (7,166 jobs), after the cache fetch. The full
default build passed (21,027 jobs), with warnings treated as errors, and was
immediately committed as `cb95b5cfa`. Explicit `Challenge` and
`DavisKahan.Audits.All` builds then passed (20,801 jobs), after their cache fetch.
The local-only name parser retains its imported-declaration false negatives;
the compiled Challenge audit resolves the native theorem it reports missing.
No paper or visualization files are changed, and the original three untracked
files remain untouched.

The full comparator signature preflight passed for all 42 implemented targets
on universe signatures and full types; the three declared absent solutions
remain skipped. No external comparator run or source-completeness claim is
inferred from that check.

The next separate representation migration is the locally constructed finite
Ky Fan symmetric ideal family in `ApproximationNumbers.ScalarGeneric`: compare
the installed `TauCeti.OperatorIdealFamily.kyFan` constructor in native
`TauCeti.Analysis.OperatorIdeal.Family.KyFan.Basic`, its gauge and completeness
API, then migrate consumers and remove duplicated construction. The native
constructor is an operator-ideal family; inspect and preserve any additional
unmerged symmetry proofs rather than assuming a native symmetric constructor.
The real-valued approximation-number views also remain an explicit
representation obligation. Neither is claimed complete by this checkpoint.

### October 25: direct Ky Fan family construction and completeness

The duplicate finite Ky Fan family, its gauge/carrier accessors, and its direct
completeness proof are removed from `ApproximationNumbers.ScalarGeneric`.
The existing source norm package stores accepted `OperatorIdealFamily.kyFan`
and consumes accepted completeness, dominance, and adjoint invariance directly.
No replacement generic symmetric adapter is introduced. The separate private
adapter in the square-ideal catalogue is also removed. Source normalization
and the beam example consume the native-backed source package; their public
mathematical statements are preserved.

The extraction manifest previously overstated this retirement: the old body
was still present at `4caeeee43`. Its entry now records the actual implementation
and the distinction between the accepted rectangular family and the symmetric
structure assembled within the paper package. Exact scope and provenance are
recorded in the contribution census. Removed namespace-map destinations are
empty, with no forwarding aliases.

The focused build passed (8,096 jobs), including all edited source consumers,
after the cache fetch. Full-build validation will be recorded when complete.
The remaining real approximation-number and norm views, transitional carrier
API, and local Fan-dominance records still require representation migrations;
this checkpoint does not claim the overall upstream-consumption goal complete.

The full default build then passed (21,029 jobs), with warnings treated as
errors, and was immediately committed as `89ee0d4ae`.

### October 25: retire carrier and Elem compatibility interfaces

`Family.Basic` is removed. Its consumers now use native
`OperatorIdealFamily.operatorGauge`, `OperatorGauge.finiteSubmodule`, and
`OperatorGauge.Carrier`, including membership, composition closure, norms,
arithmetic, and completeness. The compact-family carrier isometry, the
modulus-membership equivalence, and the paper real-valued completeness argument
retain their mathematical scope while consuming these native representations.
The source-presentation membership consumer follows the renamed finite-submodule
view; no old accessor is retained as an alias.

The unmerged `gauge_blockSum_le` is retained in the new dependency-closed
`Family.BlockSum` module, using accepted contraction estimates. The extraction
manifest distinguishes this retained theorem from the retired carrier facade,
and the module plan records its new owner. Unmerged compact-ideal and modulus
mathematics remains. Exact scope and provenance are in the contribution census.

The focused donor/consumer build passed (7,794 jobs), after the cache fetch,
including the source-presentation endpoint. Full-build validation follows.
