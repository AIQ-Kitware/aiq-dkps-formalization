# Davis--Kahan 1970 — what is actually left, handoff 2026-08-05 (late evening)

Written at `9113fc5a`+ on `main`, pushed.  `lake build` green; the extra targets
`DavisKahan.Experimental Challenge FinishTanTwoTheta` green; census checker
**CLEAN, all 48 rows agree with the build**.

**Supersedes the evening handoff of the same name**, which is replaced rather
than amended: two of its three headline claims moved.

---

## 0. Working constraints (do not relearn these)

* One agent on `main`.  The lane system is retired; do not claim lanes.
* **Do not add new `scripts/check_*.py`.  Do not write tests for scripts.
  Prefer deleting a script to repairing it.**  Censuses are edited **by hand in
  the same commit as the work**.
* Report status in terms of the mathematics, not whether a file agrees with
  itself.  Never call a declaration complete until Lean accepts it.
* `lake build` covers only `defaultTargets`.  Also build
  `DavisKahan.Experimental Challenge FinishTanTwoTheta`.
* **Never pipe `lake build` into `tail`/`head`** — you get the pipe's exit code.
  Redirect to a log and echo `$?`.
* Never run two `lake build`s at once; they share one `.lake`.
* `ForTauCeti` is `warningAsError`, and >100 columns is a hard error there.
  Root-namespace declarations must sit outside `namespace TauCeti`.
* Commit and push finished work without being asked.
* `TauCetiRoadmap` `Suggested.lean` files are API sketches — never report
  `sorry` there.
* Before any mass refactor, grep for a docstring that already recorded the
  decision.
* **A `local instance` does not cross a module boundary.**  Splitting a file
  cost two build cycles over exactly this
  (`ContinuousLinearMap.instStarOrderedRingRCLike`, and the three
  functional-calculus `variable`s beside it).

---

## 1. What landed today (second session)

| Commit | Content |
|---|---|
| `590075db` | The Appendix finite-projector limiting passage: Theorem 6.3's Ky Fan core at **arbitrary trial dimension** |
| `036581df` | The directed tangent representative **exists** at every trial dimension |
| `d4505507` | `s2-tan-theta` grounded; manifest + census updated |
| `721a26fd` | `Theorem63TrialData` — the trial-block data the chain actually consumes |
| `9113fc5a` | Both promotion-blocking `sorry`s routed out of the Section 4/8 closures |

**Frontier moved 62 → 63 of 80 grounded; paper results 23 → 24 of 32.**

### 1a. Section 2's tangent theorem is finished

`s2-tan-theta` is no longer an open obligation.  The equal-dimensional
infinite/noncompact case is proved, axiom-clean, in the default build:

* `ExactTanTheta.theorem6_3_all_kyFan_core_infiniteTrial` — the prefix Ky Fan
  inequalities with **no dimension hypothesis** on the trial subspace;
* `…_infiniteTrial_spectral_exists` / `…_of_formBounds_exists` — the ideal-gauge
  endpoints, with the representative **exhibited, not assumed**;
* `MathAhead.Section2.theorem6_3_perturbation_infiniteTrial` — the perturbation
  companion, by the same one-line residual bridge as the finite case.

Three findings worth carrying:

* **The limit needs no operator net.**  Min–max localization
  (`lt_approximationNumber_iff_exists_finiteDimensional_lowerBound`) beats every
  strict lower bound of each sine value on some *finite* subspace of the trial
  space; the almost-invariant enlargement supplies one finite `F` that nearly
  attains all `k` sine values at once while the compression leaks at most `ε`;
  the finite core plus `kyFan_k(residual F) ≤ kyFan_k(residual Z) + k·ε`
  squeezes.  Lemma 5.1 is *not* used — it is the engine for Theorem 5.2, not for
  this passage.
* **The pole at `sin = 1` never occurs, and that is a theorem, not a
  hypothesis.**  A sine value at one would push the tangent bound past every
  threshold, because `tan (arcsin ·)` is unbounded near one and the finite Ky
  Fan bound is uniform.  `approximationSingularValue_sineBlock_lt_one_infiniteTrial`.
  Beware: in Lean `tan (arcsin 1) = 0`, junk — always carry the `< 1` fact
  explicitly rather than letting a `simp` decide.
* **`ForTauCeti/.../BorelCalculus/AlmostInvariant.lean` needs no compactness.**
  Spectral-band slicing of a spanning set through `boundedPVM` enlarges any
  finite-dimensional subspace to a finite-dimensional almost-invariant one, for
  *any* bounded self-adjoint operator.  That is what makes the passage work for
  trial compressions with continuous spectrum.

### 1b. Both promotion-blocking `sorry`s are out of the closures

Neither was discharged by proof, because neither was load-bearing:

* **`directRotation_minimal` is orphaned.**  Nothing outside its own file
  mentions it; the complex statement is already proved in production as
  `spectraDirectRotation_minimal`, which the source-facing alias already points
  at.  `SpectraBridge/DirectRotationAPI.lean` imported the module only for
  `IsAcute`, which lives in `BoundedOperator/Compat`.  Its inline comment
  claimed the Halmos two-projection framework was needed; **its own docstring
  retracts that**, and the previous handoff propagated the stale version.  The
  comment is now corrected in place.
* **`projectionDifference_ideal_intervalExterior`** and its only consumer
  `ideal_sinTheta`, plus `ideal_sinTwoTheta`, moved into
  `Experimental/InfiniteDimensional/SinTheta/IdealIntervalExterior.lean`.
  `SinTheta/General.lean` and `InfiniteDimensional/DoubleAngle.lean` are now
  sorry-free.

**Measured after the move** (`closure.py`-style walk of the import graph):

| Target | Modules | `Experimental` | tactic `sorry`s |
|---|---:|---:|---:|
| `Experimental/MathAhead/Section4/InfiniteProposition43` | 175 | 24 | **0** |
| `Experimental/Sources/DavisKahan1970/Section8/SourceSurface` | 188 | 41 | **0** |
| `Experimental/Frontier/Section8` | 199 | 50 | **0** |

---

## 2. READ THE INVENTORY, NOT THE PROSE

**`dev/davis-kahan-1970-frontier-status.md` is the live inventory.**  Regenerate
with `python3 scripts/check_davis_kahan_frontier.py --write-report`.  As of this
commit: 80 manifest nodes, **63 recursively grounded, 17 not**.

The census `next_action` fields are prose and go stale silently — five were
wrong in one earlier session, every one claiming work outstanding that was
already done.  The row's own `verification` field is machine-checked and has
been right every time.  **Re-run the report and trust it over any sentence in
this file.**

The same caution applies to effort estimates, and it bit again today in both
directions: the previous handoff called `directRotation_minimal` a hard Halmos
obstruction when it was an orphan deletable in one line, and called the
equal-dimensional tangent theorem the whole of Section 2 when the unbounded
scope claim is a separate and larger piece.  **Grep for every lemma a plan
treats as existing, and grep for every consumer a plan treats as waiting.**

---

## 3. The 17 ungrounded nodes

### 3A. Section 2 — one node left, and it is the harder half

**`s2-unbounded-scope`** (priority `hard`, census `S2-unbounded-scope`).  The
paper claims arbitrary-UI-norm scope for **unbounded** self-adjoint operators;
what is grounded is the bounded theorem plus an operator-norm graph-angle
companion.  Its three dependencies are all grounded.

**Trap, on the census and repeated here: do not credit the operator-norm
unbounded graph-angle companion as the full scope claim.**

*The scaffolding for this is now built and is the recommended route.*
`DavisKahan/TanTheta/Theorem63TrialData.lean` isolates exactly what the tangent
chain consumes — `action`, `compression`, `residual`, the block identity, and
residual orthogonality — with `ofBounded` recovering the bounded case and
`restrict` transporting both form bounds to any subspace.  And
`theorem63ResidualWitness_scalar_of_data` (in `Theorem63FiniteSource.lean`) is
the equation-(6.6) estimate over that data, taking the **crossed action** `X`
as a separate argument.

Why the crossed action is the right abstraction, and the one thing to get
right: for unbounded `A` the quadratic form `⟪A y, y⟫` on `Vᗮ` is only defined
on the domain, but the argument only ever evaluates it at left singular vectors
of the sine block, i.e. at vectors `P_Vᗮ z` with `z` in the trial space.  Those
*are* in the domain when `Z ⊆ dom(A)` and `V` is a spectral subspace, because
spectral projections preserve the domain
(`selfAdjointSpectralProjection_mem_domain`).  So the faithful hypothesis is

```text
(α + δ) ‖P_Vᗮ z‖² ≤ re ⟪P_Vᗮ z, X z⟫   for all z : Z,   X z = A (P_Vᗮ z)
```

and the Sylvester link is `X z − S (M z) = P_Vᗮ (R z)`.

**Remaining for this node**, in order:
1. Generic transversality and `sine < 1` over the data (the bounded proofs
   use `T` only through the two form bounds; the generic statements need a
   field or hypothesis `z ∈ Vᗮ → X z = action z`).
2. Generic Ky Fan core over the data (mirrors
   `theorem6_3_all_kyFan_core`; `orthonormal_theorem63ResidualWitness` is
   already generic — it now takes the `sine < 1` hypothesis directly).
3. `Theorem63TrialData` from an `UnboundedTrialBlock`
   (`DavisKahan/TanTheta/UnboundedSpectrum.lean:39`), with the crossed form
   bound from `ForTauCeti/.../LinearPMap/SpectralFormBounds.lean`.
4. Fan-dominance endpoint + source wrapper; repoint the manifest node off
   `unbounded_angle_theorems_source_scope_partial_marker`.

### 3B. Section 3 — 4 nodes; one is reachable, three are not

`s3-cor3-1` (Corollary 3.1, compact case) is **not blocked by
Hahn–Hellinger**.  Its manifest dependencies are `s3-operator-classification`
and `s3-compact-angle-list`, both grounded; it is ungrounded only because of its
own `sorry` at `Frontier/Section3.lean:1088`.  What it needs:

* `twoProjection_operator_classification` (same file, proved) reduces it to:
  two compact positive **injective** operators are unitarily equivalent iff
  their approximation-number lists agree.
* The unitary half already exists:
  `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`
  in `ForTauCeti/Analysis/InnerProductSpace/CompactSelfAdjointClassification.lean`,
  stated as `dim ker(A−μ) = dim ker(B−μ)` for all `μ`, with trivial kernel.
* **The missing bridge** is `approximationNumber` list ⟺ eigenspace-dimension
  function, for compact positive operators.  It does not exist in the repo.
  Note the trivial-kernel hypothesis is not optional and is exactly what
  genericity supplies: on the generic part the cosine-square block has no
  eigenvalue `0` or `1`, so the list determines the dimension.  Without it the
  statement is false (pad either side with kernel).

`s3-theorem3-1`, `s3-spectral-multiplicity-definition`,
`s3-spectral-multiplicity-complete` **are** Hahn–Hellinger and are not a
session's work.  `Frontier/Core.lean:71` is a `sorry`-ed *definition*, so
everything resting on it is vacuous rather than unproved, and its own docstring
already records the decision: the mathematical content of Theorem 3.1 is proved
admission-free as
`MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`
(both directions, arbitrary complex Hilbert spaces, no compactness or
separability), and supplying the definition buys only the paper's *literal*
multiplicity phrasing.  Mathlib has no multiplicity theory in any form.
**Do not "define" `SameSpectralMultiplicity` as unitary equivalence of the
PVMs** — that makes the companion theorem near-trivial and abandons the measure
class plus cardinal-valued multiplicity function the docstring demands.

Also parked here: `DK-3.5-prop` — the commutation identities are present, the
maximal constant-angle eigenspace characterisation is not represented.

### 3C. Section 9 — 12 nodes, and it is a months-long project

`s9-semantic-model` is done.  The other 12 are open, and 9 of the 21 `sorry`s in
`Frontier/Section9Analytic.lean` are not modelled by any frontier node at all
(the eight `actual*` definitions and `canonicalFreeBeamAnalyticModel_representsSource`).

Corrections to the previous handoff's ordering, which was inverted:

* **The operator comes first; completeness of the mode family is a by-product
  you may not need.**  `SobolevTraceFoundation`'s spectral obligations are
  `spectrum_nonnegative`, `positive_spectrum_characterization` and
  `affineKernelEquiv` — none of them is "the modes span `L²`".
* **`DavisKahan/SpectralTheory/FormMethod/` (11 files, all sorry-free) already
  contains the self-adjointness machinery**, including
  `ShiftedBeamRealization.lean:169` `beamOperator_isSelfAdjoint`.  Free-end
  conditions are the *natural* boundary conditions of the bending-energy form on
  `H²`, so **no trace theorem is needed** — which is why the repo chose the form
  method.  H⁴ and traces enter only if you insist on the full
  `SobolevTraceFoundation` interface; recommend not.
* **What genuinely does not exist**: a concrete `L²(0,1)`.  `grep` for
  `MeasureTheory.Lp` across `DavisKahan/` and `ForTauCeti/` returns nothing; the
  whole development is abstract `H`.  The hardest single lemma is completeness
  of the form space `V` with `⟪u,v⟫_V = ∫u''v̄'' + ∫uv̄`.
* **Three structural traps**, beyond the certificate one already known:
  `freeBeamClosedFourthDerivative` is stated for an *arbitrary* `H`, where no
  free-beam operator exists; `freeBeam_exact_finite_data` as written is a
  tautology closed by `⟨_, _, rfl, rfl⟩`; and `RepresentsFreeBeamProblem` /
  `ThirdEigenvalueIsCorrect` are `def … : Prop := by sorry`, hence opaque —
  every hypothesis mentioning them is both unusable and unfalsifiable.
* **The largest hidden gap**: `TheoremOutputCertificate` has 14 scalar fields;
  the two angle-bound nodes supply 8.  The six Weinberger/direct/ω outputs have
  no `actual*` definition, no theorem, and no frontier node.
* Highest-value cheap item: `freeBeam_thirdEigenvalue_gt_fiveHundred` is a
  ~3-line re-export of `FreeBeamAnalyticFoundation.lean:173`, which is proved —
  but only after the predicate is defined through the existing records.

---

## 4. Not in the frontier manifest, but still open

* **The promotion itself.**  The two admissions are out of the closures, but
  `check_library_structure` rule 2 forbids a production module importing
  `Experimental`, so promoting means **relocating** those closures out of
  `Experimental/`.  That is a design decision, not a mechanical step, and it
  should be taken deliberately.  Precedent exists for the namespace being
  independent of the directory (`Geometry/Polar/DirectRotationSquare.lean`
  declares into `DavisKahan.Experimental` while living in production).
  The three rows this guards are `DK-3.2-prop`, `DK-8.1-thm`, `DK-8.2-thm`,
  still reported as *"proved but unguarded by `lake build`"*.
* **`check_library_structure` rule 3 is now 49 violations, up from 6** — 34 real
  modules and 15 aggregates.  **This is a consequence of today's work, not a
  regression to repair blindly.**  Rule 3 asks that every `Experimental` module
  support admission-bearing work; removing the two admissions made 34 modules
  admission-free, so the checker is now enumerating precisely the modules that
  ought to move.  Rules 1, 2, 4 and 5 pass.
* **`S2-sharpness` part (ii): the audit.**  Checking each compiled equality
  model against the printed *simultaneous*-equality claim.  Exactly the kind of
  scope question that produced three refuted transcriptions in Section 4.
* **`exact-source-wrappers` still open on**: `S1-block-residual`,
  `S2-tan-two-theta`, `DK-3.1-def`, `DK-3.2-def`, `DK-3.4-prop`, `DK-3.5-prop`,
  `DK-7-sin2-proof`, `DK-7-tan2-proof`, `S2-unbounded-scope`.  Mechanical.
  **Check each one first**: two of five stale rows in an earlier session were
  "missing wrapper" rows whose wrapper already existed.
* **`Experimental/InfiniteDimensional/Core/Unbounded.lean` does not compile**
  (30 errors, `ClosedOperator` field mismatches).  It is in no built target, so
  nothing catches it; `Core/Forms.lean` and `Ideals/CompactAndSingular.lean` sit
  downstream and are equally unbuildable.  Pre-existing, unrelated to today.
* **Consolidate the duplicated Halmos outer assembly.**

---

## 5. Traps, consolidated

1. **`DK-4.4-prop` is `refuted_as_transcribed`.**  A compiled ℝ⁴ counterexample
   beats the direct rotation in trace norm of the full displacement `1 − W`.
   Anything phrased on the **full** displacement must be checked against it.
2. **Proposition 4.2's right-hand side.**  Not `∑ᵢ cost D bᵢ`; that form is
   false.  The correct one is `∑ᵢ (1 − ‖C bᵢ‖²) = dim U − tr((C|_U)²)`.
3. **Proposition 4.3 is Ky Fan level only.**  Pointwise domination of the
   individual approximation numbers of the squared displacement is false.
4. **Frontier declarations must never go in a census row's
   `lean_declarations`** — judge by the module path, not the namespace.
5. **A `sorry`-ed definition makes its consumers vacuous, not unproved**
   (`SameSpectralMultiplicity`, and the Section 9 `Prop := by sorry` pair).
6. **Underscore binders mark fake scope gaps.**  Read the binders before
   working a "hypothesis too strong" obligation.
7. **`tan (arcsin 1) = 0` in Lean.**  Junk value; carry `sine < 1` explicitly.
8. **The union-of-two-rectangles Sylvester estimate has a second obstruction**
   the old note missed: the constant-one machinery is stated for
   `SymmetricOperatorIdealFamily`, the open theorem quantifies over
   `SymmetricNormIdeal`, and `ofRectangular` bridges the wrong way.  And the
   constant-one claim is sharp at `B − A = d (P_U − P_V)`, so there is no cheap
   route.  The triangle inequality on the two corners gives constant two and is
   already proved as `sinTheta_spectrum_gauge_symmetric`.

---

## 6. Verification recipe

```bash
lake build                       > /tmp/b.log 2>&1; echo "DEFAULT=$?"
lake build DavisKahan.Experimental Challenge FinishTanTwoTheta > /tmp/e.log 2>&1; echo "EXTRA=$?"
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_davis_kahan_frontier.py --write-report
python3 scripts/render_davis_kahan_1970_source_census.py
for g in check_docstring_coverage check_dependency_layers check_namespace_policy \
         check_duplicate_qualified_names check_declaration_name_drift \
         check_library_structure; do
  python3 scripts/$g.py > /dev/null 2>&1; echo "$g=$?"
done
```

Axiom-check every new declaration before claiming it:

```bash
cat > /tmp/ax.lean <<'EOF'
import DavisKahan.All
#print axioms <fully.qualified.name>
EOF
lake env lean /tmp/ax.lean
```

Expect exactly `[propext, Classical.choice, Quot.sound]`.
`check_library_structure` is expected to report **49** rule-3 violations (see
§4); everything else must be 0.

Importing `DavisKahan.All` alone is also the cheapest test of *"is this really
in the default build?"*.
