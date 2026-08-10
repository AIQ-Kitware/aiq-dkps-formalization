# Davis--Kahan 1970: completion handoff

State as of 2026-08-09, HEAD `b73c7ecd`, build green at 9573 jobs.

This is the work list for finishing the Davis--Kahan 1970 formalization, written so that a
coordinator who has never seen this campaign can dispatch it, and so that a subagent handed one
mission can start without reading the rest.

**Read first:** [`coordinator-subagent-workflow.md`](coordinator-subagent-workflow.md) --- how the
loop is run, what a brief must contain, and the verification protocol. Everything in this file
assumes it.

**Ground truth is the census**, `davis-kahan-1970-full-source-census.json`. This file is a plan;
the census is the record. Where they disagree, the census wins, and this file is stale.

---

## 1. Where things stand

| | |
|---|---|
| census rows | 49 |
| proved in the default build | 46 (3 `not_applicable` --- the paper's own Section 10 open questions) |
| `compiled_exact` | 26 |
| `compiled_specialization` | 18 |
| `refuted_as_transcribed` | 1 (`DK-4.4-prop`) |
| blockers | 1: `real-scalar-infinite-dimensional-scope`, 8 rows |
| rows with a recorded `scope_gap` | 22 |
| build | 9573 jobs, exit 0 |
| baselines | `check_dependency_layers` 7, `check_docstring_coverage` 98, `check_library_structure` checks 1--2 `ok` (check 3 pre-existing at 16) |

**Two rows are terminal and need nothing.** `DK-4.4-prop` is `refuted_as_transcribed`:
Proposition 4.4 is false as printed, with a compiled counterexample and a write-up in
`papers/davis_kahan_prop_4_4_counterexample.tex`. Recording a false proposition as refuted *is*
the faithful outcome. The three `not_applicable` rows are questions the paper itself poses and
leaves open.

**The remaining blocker's name no longer describes its rows.** `real-scalar-infinite-dimensional-scope`
reads as one mechanical transport across 8 rows. Measured row by row, only two are really about
scalars; the rest carry distinct printed obligations that would remain if every scalar question
were settled tomorrow. Splitting it is worth doing --- keeping heterogeneous obligations under one
name is exactly what let four stale entries hide in the blocker that was retired in M37.

---

## 2. Before you prove anything: look for it first

This repository is large and much of what a mission needs already exists, usually under a name
the mission did not think of. **Three of the four false-premise findings in recent missions were
"this does not exist" claims that a repository-wide search refutes.** Search before you build.

### Where to look

| place | what is there |
|---|---|
| `ForTauCeti/` | the general, reusable analysis: operator ideals, approximation numbers, Ky Fan gauges, polar decomposition, functional calculus, complexification, `LinearPMap` unbounded theory, Borel calculus |
| `external/TauCeti/` | the Tau Ceti library, checked out for **reading**. Search it before writing general mathematics --- for the statement if it exists, and for the proof strategy if it does not. **We do not modify it from this repository.** What you need goes in `ForTauCeti/` |
| `DavisKahan/` | paper-specific development; `Sources/DavisKahan1970/` is the source-numbered facade layer |
| `dev/tauceti/` | migration ledgers, extraction manifests, the promotable inventory |
| `dev/hilbert-space-operator-roadmap/` | the submitted operator-theory roadmap and its conformance status |

Useful commands:

```bash
# does this declaration exist anywhere, under any namespace?
grep -rn "theorem someName\|def someName" --include=*.lean .

# does a name resolve from the default build target?
python3 scripts/probe_census_declarations.py --keep     # then read dev/.census-probe.lean

# what does this file's section actually assume?  read the `variable` block, not the docstring.
```

### The operator-theory roadmap: a source of general shapes, not a goal

**Read this framing before the table.** The goal of this campaign is 100% Davis--Kahan, not
roadmap delivery. The operator-theory roadmap is **still an unaccepted pull request**; it is not
a specification anyone here is obliged to meet, and its contents may change. Two hard rules:

* **We do not modify the roadmap or the Tau Ceti library from this repository.** Both are read-only
  here. If a roadmap signature looks wrong, record that in the census or a `dev/` note --- do not
  edit it.
* **Do not frame anything you write as "to be upstreamed."** Tau Ceti policy (`TauCetiRoadmap`
  PRs #165 and #169, both merged) is *never push work*: whether other projects absorb this
  material is their decision, not a property of the code. Write `ForTauCeti/` results as
  self-standing general mathematics and say what they are independent of, not where they are
  going.

What the roadmap is genuinely useful for here: it is a curated list of the **general shapes** that
operator-theoretic results tend to take. When a Davis--Kahan mission needs a lemma, checking
whether the roadmap names a general form of it is a cheap way to pick the right generality --- and
a generic `RCLike` statement in `ForTauCeti/` is worth more to the campaign after this one than
the paper-specific special case would be. That is the whole of the connection: better generality
now, cheaper next goal. It is never a reason to enlarge a mission's scope.

`submodules/TauCetiRoadmap/**/Suggested.lean` records signatures whose bodies are deliberately
`sorry`. `scripts/check_roadmap_delivered.py` reports which names the donor libraries already
carry. **A name match is a planning aid, not semantic verification** --- a delivered declaration
can carry hypotheses the roadmap does not, and the script says so itself. Do not copy its output
into public roadmap prose.

Current OperatorTheory topics:

| topic | delivered |
|---|---|
| `OrthogonalGeometry` | 6/6 |
| `SpectralSubspacePerturbation` | 24/24 |
| `Majorization` | 18/19 |
| `PrincipalAngles` | 27/31 |
| `SelfAdjointSpectralTheory` | 34/41 |
| `PolarDecomposition` | 38/47 |
| `MatrixSpectralStatistics` | 15/20 |
| `OperatorIdeals` | 34/49 |

```bash
python3 scripts/check_roadmap_delivered.py --topic OperatorIdeals --missing
```

**How to use this list.** Several outstanding signatures are the general form of something a
mission here would otherwise prove in a paper-specific shape --- the `singularValue` family and
`singularValue_eq_linearMap_singularValues` in `OperatorIdeals`, the modulus/`operatorAbs` cluster
in `PolarDecomposition`, `restrictedPointSpectrum` in `PrincipalAngles`, the spectral-projection
measurability group in `MatrixSpectralStatistics`. If your mission needs one of these, **state it
in the general `RCLike` form under `ForTauCeti/` and use it from the paper facade**, rather than
proving the special case inline --- the cost is usually the same, and the campaign after this one
inherits a tool instead of a specialization.

Two limits on that. Do not generalize a statement you cannot prove in the general form: a
paper-specific lemma that works beats a generic one that stalls the mission, and the Davis--Kahan
row is what you are accountable for. And do not add scope --- if the roadmap names a neighbouring
result your mission does not need, leave it.

The conformance write-up's own conclusion is worth carrying, and it applies to this repository's
notes as much as to the roadmap: of the items ever recorded there as blocked, *every one* turned
out to be blocked by a description rather than by the mathematics. Attempt before believing.

---

## 3. Standing traps

These have each cost a mission at least once. They are repo-wide, not mission-specific.

1. **Complexification is the fallback, not the default.** Check first whether the argument is
   already scalar-generic and merely uninstantiated at `ℝ`. Section 6's tangent and leakage
   material was; Section 3's polar factors were not. Measure link by link. A claim that a whole
   tree is "complex by convention" is worth nothing until the finite-projector selection steps in
   it have been checked.
2. **The bounded projection-valued measure in `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/`
   is ℂ-only.** Any proof that reaches `exists_finiteDimensional_le_almostInvariant` cannot be
   generalized to `RCLike` by editing binders. This has blocked two separate generalization
   attempts (Section 3 and the Appendix passage).
3. **`spectrum ℝ` does not survive the complexification transport.** `Algebra.complexToReal` and
   `RealComplexification.instModuleReal` create a real-algebra diamond: the two `Module ℝ`
   structures are propositionally but not definitionally equal, so a `spectrum ℝ` rewrite across
   the transport fails. Use `TauCeti.DavisKahan.Experimental.Foundation.realSpectrum`, which is
   `spectrum` over the native scalar field and therefore diamond-free.
4. **`KyFanDominantIdealFamily` is scalar-fixed and has no `gauge_complexify`** --- a complex
   family's gauge cannot be transported onto real operators. But the structure is *`RCLike`-generic*,
   as is the `RestrictedDisplacementApproximationDominance` / `restrictedDisplacement_idealGauge_le`
   pair, so you can state the real endpoint over a **real** family with nothing transported but the
   approximation numbers. Corollary 4.1 over `ℝ` is proved exactly that way. Do not read
   obstruction (4) as wider than it is.
5. **`PaperUnitaryInvariantNorm` is scalar-agnostic**; `KyFanDominantIdealFamily` is instantiated
   per field. If an endpoint is stated over the latter and you need it over `ℝ`, re-derive at
   `PaperUnitaryInvariantNorm` scope from a Ky Fan core rather than transporting.
6. **A module nothing imports is invisible to every gate.** The census probe, the frontier check
   and the axiom audit all resolve against `DavisKahan.All`, and the `DavisKahan` lean_lib has no
   globs. Wire every new module into the appropriate `All.lean`.
7. **The two JSON files under `dev/` are serialized differently.** The census is
   `indent=2, ensure_ascii=False` with a trailing newline; the frontier manifest is `indent=1`
   with **no** trailing newline. Verify a byte-identical round-trip before and after editing
   either.
8. **A census status change can break the frontier gate.** `compiled_specialization` is not in
   `census_terminal_statuses`, so downgrading a row makes a frontier manifest mapping mandatory.
   Run the *full* gate set after any status edit, not just the census gate.

### Routes already refuted --- do not re-propose

* `J² = -1` is **false**. The correct identity is `J² = -(sinΘ)(sinΘ)⁺`, because `J` vanishes on
  `Null Θ`.
* On `DK-3.1-cor`, do **not** "simplify" the hypothesis back to `P Q P`. That was the bug. The
  statement is on `genericCosineBlock`, not the symmetrized `genericHalmosCosineSq`.
* On `DK-3.5-prop`, do **not** "restore" the source form of the maximal-subspace predicate; it is
  refuted for `c < 1` by an exterior vector.
* On `DK-8.2-thm`, the counterexample recorded in the row's notes does **not** satisfy standing
  assumption (3.5) and must not be re-used as evidence against the (3.5)-hypothesised statement.
* The unrestricted sharp infinite-dimensional `tan 2Θ` ideal statement is **refuted**: the genuine
  unbounded Sylvester equation has a nonzero commutator defect, carried explicitly by
  `doubleAngleTangent_sylvesterEquation`.
* An attained-maximum form of (1.12)/(1.13) --- `∃ Ω, ‖KΩ‖_ν = ‖K‖_ν` --- is **false** in infinite
  dimensions. `K = diag(1 - 1/n)` has every approximation number `1`, so `‖K‖_ν = ν`, while every
  rank-ν compression falls strictly short. The statements are `IsLUB`.

---

## 4. The work

Each item is sized for one subagent. "Scalars?" says whether the mission is really about the
real-scalar axis or whether that label is inherited from the blocker.

### Track A --- the last narrowing outside the blocker

**A1. Remove the codomain-room hypothesis from `equation1_12`.** Row `S1-ui-norms`. *Scalars? No.*

`equation1_12` carries `hF : ∃ y : Fin ν → F, Orthonormal ℂ y`, which printed (1.12) does not:
(1.12) quantifies over projectors on the **domain** alone. It enters only through the proof --- the
rectangular Ky Fan principle needs room on both sides --- and it excludes operators whose codomain
has finite dimension below `ν`, a class the paper permits. The domain hypothesis `hE` is *not* a
narrowing and must stay: without it the printed supremum ranges over an empty set.

Route, worked out by M38 and recorded on the row's `next_action`: run the attaining argument at
`ν'' = min ν (finrank W')`, use `rectangularKyFanSum_eq_minFinrank_of_minFinrank_le` to see the
prefix has saturated there, then extend the orthonormal `ν''`-tuple to a `ν`-tuple inside the
finite-dimensional `W`. Estimated ~130 lines.

On landing: row → `compiled_exact`, and frontier node `s1-ui-norms-kyfan-suprema` stops being an
open obligation. This is the smallest remaining mission and it retires the last non-terminal row
outside the blocker.

### Track B --- genuinely about real scalars

**B1. `DK-8.1-thm`, Theorem 8.1 over `ℝ`.** *Scalars? Yes, and not mechanical.*

Every declaration on the row is `InnerProductSpace ℂ`. The transport is not binder editing:
8.1(a) is an `iff` about spectral subspaces of a real self-adjoint operator and 8.1(b)
*constructs* one, so after complexifying you must show the complex branch is the complexification
of a real reducing subspace. Note the row's own qualification: `[FiniteDimensional]` on the
8.1(iii) symmetric-gauge statements is **the paper's own restriction** and is not part of this
gap.

**B2. `DK-3.2-prop`, the nonacute existence criterion.** *Scalars? Partly.* Three printed pieces,
of which two are not about scalars:

1. State the actual nonuniqueness: exhibit two **distinct** direct rotations in the nonacute case,
   e.g. two distinct isometries of the crossed defect spaces whenever that space is nonzero, fed
   to the injective `build` of `proposition3_2_parameterized_nonuniqueness`.
2. Compile the Remark's bilateral-shift example on `ℓ²(ℤ)`: (1.5) holds, the shift satisfies
   (1.4), and (3.5) fails. Short, and it is the source's own separation of (1.5) from (3.5).
3. The real-scalar form.

Note the connection to B3: the same standing assumption is what the Theorem 8.2 counterexample
turns out to violate.

### Track C --- printed content, not scalars

**C1. `DK-8.2-thm`: restate `Θ < π/4` under standing assumption (3.5).** *Scalars? No.*

Replace `[FiniteDimensional ℂ H]` with the Section 3 standing assumption
`dim(PH ∩ Q^⊥H) = dim(P^⊥H ∩ QH)`, and prove `subspaceGap P Q = directedGap P Q` from (3.5)
rather than from `subspaceGap_eq_directedGap_of_finrank_eq`. Route: the transcription's
L832--834 argument --- (3.5) says `dim Null(C₀) = dim Null(C₀⋆)`, which is exactly when `S₀` and
`S₁` carry the same singular data. If it turns out false in infinite dimensions, **the
counterexample must satisfy (3.5)**; the one already in the notes does not, and its refutation is
written up there so it is not re-used.

**C2. `DK-3.1-cor`: the compact realization sentence.** *Scalars? No.*

Given a decreasing sequence `π/2 ≥ θ₁ ≥ θ₂ ≥ ...` tending to 0, plus a prescribed multiplicity of
the eigenvalue 0 on each side, construct a pair of subspaces with `P Q^⊥ P` compact realizing it.
The general instrument is `theorem3_1_realization` (on `DK-3.1-thm`, proved 2026-08-09); this is
its compact specialization at the eigenvalue-list level. See the refuted-routes list above for the
two things not to do.

**C3. `DK-3.5-prop`: the eigenvector clause.** *Scalars? No.*

One of the six printed assertions is outstanding: `angle(x, Ux) = θ`. `InnerProductGeometry` is
used nowhere in `DavisKahan/` or `ForTauCeti/`, so the angle itself has to be brought in --- that
is the bulk of the mission. Separately, the commutations proved in M19 and M24 are
finite-dimensional over any `RCLike` field; lifting them to the bounded complex tree where
`paperAngleOperatorC` lives is the remaining scope work, and the `J` clause additionally needs a
`J` to exist there.

**C4. `S2-unbounded-scope`: unbounded `tan 2Θ` beyond the operator norm.** *Scalars? No.*

`tanTwoTheta_unbounded_residual_opNorm` is the `ν = 1` residual case. Open: the Ky Fan `ν ≥ 2`
case, the arbitrary-unitarily-invariant-norm endpoint, and the perturbation form
`δ N(tan 2Θ) ≤ 2 N(H)`. The obstruction and its proposed repair are recorded on `DK-6-appendix`,
not on this row --- read both. Everything else on this row is closed: the sine, double-angle sine
and tangent families are complete at complex scalars, at the printed hypothesis, and at arbitrary
trial dimension.

**C5. `DK-9-model`: the fourth-derivative Rayleigh--Ritz model.** *Scalars? No, and the
complexification route is unavailable* --- `Lp ℂ 2 μ` is not presented as
`RealComplexification (Lp ℝ 2 μ)` and no such isometry exists locally. Three items, increasing in
difficulty:

1. **Existence of `α₃`**: prove the positive real spectrum of `beamOperator` is nonempty (in fact
   an unbounded increasing sequence). Compactness of the form embedding is already proved, so the
   resolvent is compact and the spectrum is a sequence of eigenvalues; what is needed is that the
   kernel is not everything, which the affine-plane kernel computation already gives. This is what
   lets `beamFiniteDataCertificate` drop its `α ∈ realSpectrum` hypothesis.
2. Identify `beamOperator` with the closure of the classical `(d/dt)⁴` on the four free-end
   boundary-condition domain. At present the boundary conditions are derived rather than assumed.
3. (See the row.)

**C6. `DK-3.1-thm` follow-ups.** *Scalars? No. The row itself calls these non-blocking.* Theorem
3.1's statement, uniqueness and realization half are all proved. Outstanding: bridge the
realization datum from `(cos Θ, sin Θ)` to a single self-adjoint `Θ` with spectrum in `[0, π/2]`
via the continuous functional calculus. The missing lemma is about an intertwiner of two
self-adjoint operators.

### Track D --- hygiene, not source coverage

**D1. Finish the `LinearPMap` migration** (was M21). GPT moved the spectral reduction and its
real companion onto the canonical `LinearPMap` carrier (`b73c7ecd`), which is the foundation.
The temporary `ClosedOperator (𝕜 := ℝ)` adapter is still consumed by at least eight source
facades: `FullSineTheta`, `RemainingSourceSurface`, `SinTwoTheta`, `DirectedUnboundedReal`, and
the four `SineTheta/` modules. Migrate those and delete the duplicate.

**D2. Frontier `--check` coverage** (was M23). `--check` no longer covers source nodes that have
no census mapping.

**D3. Removable-conjugation simplification back to the complex side** (was M28).

---

## 5. Sequencing

* **A1 first.** Smallest, route fully worked, and it retires the last non-terminal row outside the
  blocker.
* **Then split the blocker** before dispatching Track C. B1 and B2(3) are the real-scalar rows;
  C1--C6 are printed obligations that happen to sit under a scalar-shaped name. One blocker with
  eight heterogeneous rows is how four stale entries hid in the blocker M37 retired.
* **C1 and B2 share (3.5)** --- the standing assumption C1 introduces is the one B2's bilateral-shift
  example separates. Doing C1 first gives B2 a compiled hypothesis to point at.
* **C4 depends on reading `DK-6-appendix`**, where its obstruction is actually recorded.
* Track D is independent of all of it and can fill any gap.

## 6. What "done" means

The census carries no row that is a completion obligation: every row is `compiled_exact`,
`not_applicable`, `refuted_as_transcribed`, or `resolved_by_modern_development`, with every
recorded `scope_gap` either discharged or reclassified as a disclosed global convention rather
than paper debt. The blockers table is empty. Six gates exit 0, build exit 0, every source
endpoint axiom-clean.

That endpoint is a claim about the paper, so it is settled by a fresh section-by-section audit
against `non-distributable/davis-kahan-1970-modernized-transcription.tex`, not by the gates. The
gates cannot see scope, cannot see `status`, and cannot see a row that omits a declaration for a
conclusion the paper asserts.
