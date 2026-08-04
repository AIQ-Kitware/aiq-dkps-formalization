# Conformance status — ForTauCeti against the submitted roadmap

Measured with `scripts/check_roadmap_delivered.py`, which reads
`submodules/TauCetiRoadmap/TauCetiRoadmap/HilbertSpaceOperatorTheory`.

**189/198 name matches (95.5%)**, from 174/198 (87.9%) at the start of the conformance pass.

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

## The nine outstanding, classified

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

5. **`selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc`** — the `RCLike` calculus
   agrees with Mathlib's CFC over `ℂ`. Part A milestone; nothing in the tree proves it.
6. **`isCompactOperator_of_hilbertSchmidtEnergy_ne_top`** — Hilbert--Schmidt implies compact.
   Both ends exist (`tendsto_enorm_comp_one_sub_basisTruncation` from finite energy;
   `isCompactOperator_of_tendsto_approximationNumber`) but the join is real work: the first is
   a net over `Finset ι`, the second a sequence over `ℕ`, and reconciling them is the content.
   The Peter--Weyl roadmap depends on this one.
7. **`schattenFamilyInf`** — the roadmap wants the `∞` endpoint defined from the `Φ_∞` gauge
   and then *proved* equal to the operator-norm family, "an equality of *families* and not
   merely of gauges". Defining it as an alias for `operatorNormFamily` would make that
   theorem vacuous, which the roadmap explicitly rules out.
8. **`exists_units_eq_mul_of_rank_factorization`** — Milestone A2 uniqueness. The roadmap's own
   Acknowledgements already say A2 is specified and not implemented.

### Over-strong hypotheses — the theorem exists, the signature does not match

9. **`continuous_iInf_of_hemicontinuous`** and **`upperHemicontinuousAt_isMinOn_of_hemicontinuous`**
   — delivered as `..._of_hemicontinuousAt` (the better name; the hypotheses really are
   pointwise), but carrying `[FirstCountableTopology P] [RegularSpace X] [T2Space X]
   [FirstCountableTopology X] [WeaklyLocallyCompactSpace X]`, none of which the roadmap
   assumes. Same defect as `upperHemicontinuousAt_isMinOn`, which carries an extra
   `[FirstCountableTopology X]` and which the *name* checker scores as delivered — the
   over-counting direction, and the reason `RoadmapBridge` exists.

   Removing them is real proof work: Mathlib's `UpperHemicontinuousAt.of_sequences` is the
   sequential route that forces first-countability, so the general proof cannot go through it.
   The roadmap is explicit that the hypothesis is a proof artifact rather than incidental.

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

## What the gates cannot see

`check_duplicate_qualified_names` reports 0 and is correct — it compares *names*. It cannot
see one theorem wearing two names, which is how Part D's copy of the Part A
singular-value-determination lemma survived (identical proof, different name, different file;
the roadmap had explicitly warned against restating it). Found by hashing normalised proof
bodies; that scan also flagged `hasDerivAt_expTime_apply'` in `StoneUniqueness.lean` as a
restatement of a `private` lemma in `SkewAdjointExponential.lean`, differing only in
`expTime B s (B ψ)` versus `(expTime B s * B) ψ`, with both carrying `@[simp]`. Not yet fixed.
