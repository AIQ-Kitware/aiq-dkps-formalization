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

## Treat the "missing mathematics" list as unverified

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

5. **`selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc`** — the `RCLike` calculus
   agrees with Mathlib's CFC over `ℂ`. Part A milestone. **Checked, not guessed**, and this
   one really is a development rather than a lookup.

   The `sqrt` special case is delivered (`operatorAbs_toContinuousLinearMap_eq_cfcAbs`) but it
   goes through `CFC.sqrt_unique`, a characterisation peculiar to square roots. A general `f`
   has to go through uniqueness of the continuous functional calculus, which means exhibiting
   `f ↦ selfAdjointFunctionalCalculus hT f` as a *continuous star-algebra homomorphism*
   sending `id` to `T` and invoking `cfc_unique`.

   **Re-verified against the actual uniqueness lemma.** `cfcHom_eq_of_continuous_of_map_id`
   takes `φ : C(spectrum R a, R) →⋆ₐ[R] A` together with `Continuous φ` and `φ (id) = a` —
   precisely the bundle named below, so this is not a case of having searched for the wrong
   thing. Of the eight "blocked" calls made during this pass, this is the only one that
   survived checking, and it is the only one that was made by enumerating what the file has
   and lacks rather than by inferring difficulty.

   `SelfAdjointFunctionalCalculus.lean` has `..._id`, `..._comp`, `..._isSymmetric`,
   `..._congr` and the eigenvector action. It does **not** have additivity, multiplicativity
   as an algebra map, star-preservation, or continuity in `f` — the four obligations a
   `StarAlgHom` bundle needs. That is the work, and it is real.
6. ~~**`isCompactOperator_of_hilbertSchmidtEnergy_ne_top`**~~ — **delivered.** Hilbert--Schmidt
   implies compact. I classified this as missing mathematics twice and was wrong both times:
   first claiming the obstacle was reconciling a `Finset ι` net with an `ℕ` sequence (it is
   not -- one `s` from the net gives a rank bound at a single index and antitonicity finishes),
   then claiming it needed a long proof (the four remaining blockers were lemma-name lookups:
   `finrank_euclideanSpace_fin`, `Module.finrank_eq_rank`, `ofReal_norm`, and
   `ContinuousLinearMap.one_def`). Proved via a new `rank_comp_basisTruncation_le`, which
   simply exposes the factorisation already inside
   `tsum_approximationNumber_comp_basisTruncation_sq_le` as a rank bound.

7. **`schattenFamilyInf`** — **the gauge is now built**; what remains is one computation and
   one decision.

   `supGauge : TruncationGauge` carries `Φ_∞ a = ⨆ n, a n` with all five axioms proved. I had
   recorded this as needing `Finset.sup` machinery; it needed `NNReal.mul_finset_sup` for
   homogeneity, and for permutation-invariance it needed only the two characterising bounds
   (`le_supGaugeFinsupp`, `supGaugeFinsupp_le`) rather than reasoning about `Finset.sup` at all.

   *The computation is done*: `supGauge_extend_of_antitone` proves
   `supGauge.extend a = a 0` for any antitone `a : ℕ → ℝ≥0∞`. Since approximation numbers are
   antitone, `Φ_∞ (a T) = a₀ T = ‖T‖` — the whole mathematical content of "the `∞` endpoint is
   the operator-norm gauge". Every capped truncation is bounded by `a 0`, and the existing
   `le_extend` supplies the reverse.

   *Remaining decision*, which is not mine: our `symmetricGaugeFamily` carries
   `[ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜]` while the roadmap's
   `schattenFamilyInf : OperatorIdealFamily.{0, v, w} ℂ` carries no hypothesis, so routing the
   endpoint through `symmetricGaugeFamily` yields a different object from the one specified.

8. ~~**`exists_units_eq_mul_of_rank_factorization`**~~ — **delivered.** Milestone A2. I called
   this blocked three times, the last after a search I reported as coming back empty; it did
   not, I searched badly. `Module.projective_lifting_property` is the engine, and the proof is
   four helpers: `injective_mulVecLin_of_rank_eq` (rank-nullity on `Fin r → 𝕜`),
   `rank_left_factor_eq`, `range_left_factor_eq`, and a left-cancellation lemma. Lifting both
   ways gives `G` and `G'`; injectivity turns `G G' = 1` and `G' G = 1` into the `Units`.

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
