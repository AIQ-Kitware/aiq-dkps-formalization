# Conformance status — ForTauCeti against the submitted roadmap

Measured with `scripts/check_roadmap_delivered.py`, which reads
`submodules/TauCetiRoadmap/TauCetiRoadmap/HilbertSpaceOperatorTheory`.

**189/198 name matches (95.5%)**, from 174/198 (87.9%) at the start of the conformance pass.

Note that removing the false hypotheses from `upperHemicontinuousAt_isMinOn` did **not** move
this number, because the checker was already counting it as delivered on the strength of the
name while the statement assumed strictly more. The percentage went up when renames landed and
stayed flat when a real defect was fixed, which is the clearest available argument for reading
the classification below instead of the number.

| topic | | |
|---|---|---|
| MajorizationAndAngles | 26/26 | 100% |
| SelfAdjointSpectralTheory | 35/35 | 100% |
| SpectralSubspacePerturbation | 24/25 | 96.0% |
| OperatorIdeals | 37/39 | 94.9% |
| HilbertSpaceOperatorFoundations | 48/51 | 94.1% |
| MatrixSpectralStatistics | 19/22 | 86.4% |

**The percentage is softer than it looks, in both directions.** Name matching over-counts
(a delivered declaration can carry hypotheses the roadmap does not) and under-counts
(renames, and roadmap-local scaffolding that is not ours to deliver). Treat the
classification below as the real state, not the number.

## The "missing mathematics" list is empty

All five items originally recorded there are delivered: Berge without first countability,
Hilbert--Schmidt implies compact, the Schatten `∞` gauge with its collapse, Milestone A2's
rank-factorization uniqueness, and the CFC bridge. Each was called blocked at least once, and
in every case the blockage was a description rather than the mathematics.

## What was, at the time, treated as unverified

Of the four items originally listed there, two have since been delivered by simply attempting
them -- Berge's first-countability and Hilbert--Schmidt implies compact. In both cases the
blockage was a description I had written or read, not the mathematics. **The remaining two
deserve an attempt before anyone believes they are blocked.**

That is the same failure this conformance pass exists to catch, committed in the assessment
rather than in the code: judging by what something is called rather than by what it says.

## The outstanding items, classified

### Not a gap — do not "fix" these

1. **`frobeniusNorm`** — declared in the roadmap's `Local derived objects` section of
   `SpectralSubspacePerturbation/Suggested.lean`: scaffolding so that file elaborates, not a
   delivery target. Our `frobenius` in the seminorm API is the real object. Renaming it to
   match would bend correct API toward a throwaway.

### The roadmap should change, not us

2. **`singularValues_toLinearMap`** — delivered as
   `ContinuousLinearMap.toLinearMap_singularValues`, same equation, `rfl` both ways.
   `RoadmapBridge/MatrixSpectralStatistics.lean` argues the roadmap should adopt the
   delivered name: the word order is a deliberate `simp`-normal-form choice ("so that `simp`
   removes the coercion from statements rather than introducing it") and the roadmap's
   spelling reverses it.
3. **`yosidaApproximant` index type** — *delivered*, but the roadmap takes `n : ℕ` and we take
   `n : ℕ+`. At `n = 0` the approximant `n²R(in) − in` degenerates and `R(0)` is unavailable
   for a self-adjoint operator with `0` in its spectrum. `ℕ+` is the honest index type.
4. **`exists_linearIsometryEquiv_comp_eq_comp`** — the roadmap states Davis's intertwining
   unitary with *seven loose hypotheses* (symmetry, idempotence, completeness of each family,
   non-degeneracy). We bundle them as `OrthoProjFamily` with `NonDegenerate`. The roadmap
   argues for exactly this bundling in its own Moore--Penrose section — "four anonymous
   hypotheses" is the anti-pattern it names — so it is inconsistent with itself here.
   Delivering the loose form would mean building a bridge from loose hypotheses to the
   bundle, which is the translation layer this work is meant to avoid.

### Genuinely missing mathematics — not renames

5. ~~**`selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc`**~~ — **delivered.**
   Part A's milestone: the `RCLike` finite calculus, transported to bounded operators, is
   Mathlib's continuous functional calculus.

   The route, in the order it was built: the algebra laws (`_add`, `_smul`, `_comp`,
   `_isSymmetric`, `_one`, `_pow`), the Parseval norm bound, the `Module.End`↔`ContinuousLinearMap`
   algebra equivalence, the eigenvalue containment in the real spectrum, `extendSymbol` with
   `_indicator` to make extension off the spectrum invisible, then `calculusStarAlgHom` and
   its two hypotheses, and finally `cfcHom_eq_of_continuous_of_map_id`.

   This entry was described as blocked, or as needing four obligations, then one, then three,
   then two, then one again, across six revisions. Every number came from estimating; every
   correction came from opening a file. The final assembly took four reverts.

### Over-strong hypotheses

**`upperHemicontinuousAt_isMinOn` — resolved.** It carried `[FirstCountableTopology X]`,
`[T2Space X]` and `[(𝓝 p₀).IsCountablyGenerated]`; the roadmap assumed none and called the
first a proof artifact of the sequential route. Correct: Mathlib's
`IsCompact.eventually_forall_of_forall_eventually` is a tube lemma with no countability, and
gives uniform closeness of `g p` to `g p₀` on compact `K` directly. The delivered signature
now carries none of the three, and the sequential proof was replaced rather than kept beside
the new one.

**`continuous_iInf_of_hemicontinuous` and `upperHemicontinuousAt_isMinOn_of_hemicontinuous`
— a different case, and a question for the roadmap.** These are the *varying*-constraint
theorems, delivered as `..._of_hemicontinuousAt` (the better name — the hypotheses really are
pointwise) with `[FirstCountableTopology P] [RegularSpace X] [T2Space X]
[FirstCountableTopology X] [WeaklyLocallyCompactSpace X]`.

The first-countability binders are probably artifacts of the same sequential route and worth
attacking the same way. **Local compactness is not.** `Berge.lean` documents why, at
`exists_subseq_tendsto_mem_of_upperHemicontinuousAt`:

> The local-boundedness hypothesis is what makes this possible and **cannot be weakened to
> "each `K p` is compact"**: a family of individually compact sets can march off to infinity
> as `p → p₀`, leaving no compact set to extract from.

The roadmap's own README agrees the varying case is not the fixed case plus a hypothesis:
"the argument that proves the fixed case does not generalize by adding a hypothesis, because
with `K` varying the approximate-minimizer sequence need not stay in one compact set."

So the roadmap states these with only `[TopologicalSpace P] [TopologicalSpace X]` while the
mathematics appears to need a local-boundedness assumption. That is the same shape as the
Milestone D1 defect — a hypothesis the statement needs and does not carry — but unlike D1 it
is **not confirmed**, because no counterexample has been constructed here. It should be
reviewed before anyone tries to deliver the signature as written.

## Roadmap defects found and fixed

- **Milestone D1 was false.** `approximationNumber_le_of_spectral_band` omitted `0 ≤ δ`; at
  `P = 1` the band hypothesis reads `0 ≤ 0` and holds for every `δ`, and `r ≥ finrank E` makes
  the conclusion `0 ≤ δ`, false at `δ = -1`. Fixed and pushed as `970b0a4`.

## Roadmap defects found and not fixed

- The `Local derived objects` section of `SpectralSubspacePerturbation/Suggested.lean` is
  captioned *"Only perturbation-specific constructions are declared here"*, but `sinThetaMap`
  and `frobeniusNorm` are not perturbation-specific — that file's own README says they are
  *"Consumed from `MajorizationAndAngles`"*, which never declares them. A reviewer reading the
  signature file would assign ownership contrary to the prose.

## The namespace migration is a decision, not cleanup — attempted and reverted

`ForTauCeti/README.md` carries a TODO to move ~39 files off root Mathlib namespaces, on the
grounds that "Tau Ceti never extends a root Mathlib namespace". Measured with namespace
nesting tracked properly, that is **39 files and 318 declarations** — the README's estimate
was right. (A grep for `^namespace ContinuousLinearMap` reports 66, because Lean does not
indent a nested namespace, so root-level and nested-inside-`TauCeti` look identical.)

**Do not start this as a mechanical lane.** Three things say so:

1. **`check_namespace_policy.py` passes today.** It allowlists 12 root Mathlib namespaces
   with a stated reason for each ("facts about a `LinearMap`, including its `IsPositive` /
   `IsSymmetric` predicates"). By this repository's own gate the current state is correct.
2. **`MinMax.lean` documents the opposite decision, deliberately**, under a `Namespace note`:
   declarations extend `ContinuousLinearMap` "so that dot notation resolves and the names
   match the eventual Mathlib upstreaming target … Lean field projection binds `T.foo` only
   to the literal `ContinuousLinearMap.foo` and does not consult the enclosing `TauCeti`
   namespace. This is a deliberate API choice, **flagged for Tau Ceti maintainer review**."
3. **The cost is `open` churn, which is the thing this work is meant to avoid.** A trial
   migration of the three smallest files (`SetTheory/Cardinal/Lift`, `Topology/ENNRealLiminf`,
   `LinearAlgebra/Dimension/RankComp`) cascaded immediately: `RankComp` needed `open LinearMap`
   for bare names that had resolved through the enclosing root namespace, and four
   `ApproximationNumber` modules then needed `open TauCeti`, with more behind them. Reverted;
   the tree is green.

So the question is not "when do we do the migration" but "does Tau Ceti want dot notation on
`ContinuousLinearMap`, or names under `TauCeti`?" That is a maintainer decision, the repo has
already flagged it as one, and doing it unilaterally would either break `T.foo` everywhere or
require an `open TauCeti.ContinuousLinearMap` in every consumer.

## Open, and the largest remaining polish item: one gauge concept, two structures

`SymmetricGauge` (`Analysis/Normed/SymmetricGauge.lean`) and `TruncationGauge`
(`Analysis/OperatorIdeal/SymmetricGauge.lean`) are **the same structure declared twice** —
same carrier `(ℕ →₀ ℝ≥0) → ℝ≥0`, same five conditions, same docstrings, differing only by a
prime on every field name:

| `SymmetricGauge` | `TruncationGauge` |
|---|---|
| `add_le` `smul` `symm` `mono` `normalized` | `add_le'` `smul'` `symm'` `mono'` `normalized'` |

The roadmap specifies exactly one, named `SymmetricGauge`, and `ForTauCeti/README.md` states
the goal as "one canonical spelling per concept". Thirteen declarations are duplicated across
the two namespaces, including three the roadmap names by hand — `extend`,
`extend_le_extend_of_forall_sum_le`, `iSup_le_extend_le_tsum`. **This is an over-count in the
conformance number**: the checker matches those names, but cannot tell that the delivered ones
hang off a structure the roadmap does not have.

**Correction to an earlier version of this section, and to commit `753f23f6`'s message.**
That version said the thirteen same-named declarations across the two namespaces are
duplicates to be deleted. They are not. Only the lemmas that speak about `Φ` alone are
genuine duplicates (`le_sum`, and the five accessors that merely unprime a field). The
`extend` family is **two different constructions wearing the same names**:

```lean
-- Analysis/Normed/SymmetricGauge.lean          -- domination
SymmetricGauge.extend Φ a = ⨆ b : Dominated a, (Φ b.1 : ℝ≥0∞)

-- Analysis/OperatorIdeal/SymmetricGauge.lean   -- capped truncation
TruncationGauge.extend Φ a = ⨆ k, ⨆ m, (Φ (truncate a k m) : ℝ≥0∞)
```

and their `truncate`s differ too — one takes a length and a `≠ ⊤` proof, the other a length
and a cap. So the merge is not deletion; it is reconciling two constructions, which means
either proving them equal or choosing one and reproving its dependents. That is mathematics,
not packaging, and it is why this is recorded rather than done.

**Which one the roadmap wants.** Its `SymmetricGauge.extend` body is `sorry`, so the
signature does not pin the construction, but the prose does: *"`extend` is a supremum of
truncations and nothing cleverer"*, and B1 specifies `Φ∞ a = ⨆ N, Φ (truncate a N)` over
truncations of the decreasing rearrangement. **`TruncationGauge` is the one that matches the
spec**; the module actually named `SymmetricGauge` takes the domination route. So the merge
direction is the opposite of what the naming suggests.

Still true and still worth doing: the *structures* are duplicated, one concept has two
spellings, and `TruncationGauge` is confined to its own file (32 references). What is not
true is that it can be done by deleting collisions.

## What the gates cannot see

`check_duplicate_qualified_names` reports 0 and is correct — it compares *names*. It cannot
see one theorem wearing two names, which is how Part D's copy of the Part A
singular-value-determination lemma survived (identical proof, different name, different file;
the roadmap had explicitly warned against restating it). Found by hashing normalised proof
bodies; that scan also flagged `hasDerivAt_expTime_apply'` in `StoneUniqueness.lean` as a
restatement of a `private` lemma in `SkewAdjointExponential.lean`, differing only in
`expTime B s (B ψ)` versus `(expTime B s * B) ψ`, with both carrying `@[simp]`. Not yet fixed.

## The largest mechanical-submission gap: the module system

Upstream Tau Ceti is **1212/1212 files** on Lean's module system (`module`, `public import`,
`public section`). `ForTauCeti` is **68/192**, plus 13 files carrying a `public section` that
does nothing because the file is not a `module`. Every unconverted file is hand-work at
submission time, so this — not the remaining name matches — is what stands between here and a
mechanical port.

Conversion was attempted and reverted. The measured result, which is the useful part:

* `dev/hilbert-space-operator-roadmap/module-system-conversion.py` converts a file
  mechanically (insert `module` after the copyright block, `import` → `public import`, add
  `public section` after the module docstring). It handled all 124 files.
* Conversion is **all-or-nothing**: a `module` may not import a non-`module`, so no
  downward-closed subset short of the whole package builds.
* **114 of 124** then compiled with no further work.
* The rest needed two things. Missing imports, because the module system drops transitive
  name visibility — `Finset.sum_le_sum`, `Finite.bddAbove_range` and friends must be imported
  directly, and Lean names them precisely (`Unknown constant`). And exposed definition bodies,
  which Lean also names precisely, under `definitions were not unfolded because their
  definition is not exposed`.
* That left **20 errors in 8 files**: `Polar/Decomposition`, `Normed/SymmetricGauge`,
  `GramBandPolar`, `Spectral/Subspace`, `BoundedOperator/SinTheta`, `EnergyComparison`,
  `Rosenblum`, `SpectralProjectionGroup`.

The reason to stop rather than push through is a decision already recorded in the tree.
`spectralPVM` in `LinearPMap/SpectralMeasure/Construction.lean` documents that its `@[expose]`
was **removed** once `spectralPVM_def`, `specProjection_def`, `toProjValMeasure_proj`/`_diag`
and `specProj_def`/`specDiag_def` retired every consumer, at a cost of zero sites — and draws
the general rule: a consumer that rewrites by lemma rather than reducing through a body does
not care whether the body is exposed. Blanket `@[expose]` is the style that note moved away
from. Finishing in house style means writing the `_def` lemmas and rewiring the call sites in
those 8 files, which is real work, not a mechanical pass.

The converter script skipped `spectralPVM` by luck — its "already annotated" guard matched the
word *exposed* in that very docstring. Anyone rerunning it should not rely on that.

## `PosDef` collides with an unrelated upstream file

`export_for_tauceti.py --check` failed on every module we would *add*, because a module absent
upstream is by definition absent, and the check treated that as drift. It now reports those as
`NEW` and fails only on genuine divergence. One survives:

`ForTauCeti.LinearAlgebra.Matrix.PosDef` maps onto
`external/TauCeti/TauCeti/LinearAlgebra/Matrix/PosDef.lean`, which already exists upstream as a
different 112-line file with different content and its own copyright. `--write` would refuse it
(it is not in `protected`), and should. The module needs either a different target name or a
merge into the existing upstream file; it is the one place where submission is not a copy.
