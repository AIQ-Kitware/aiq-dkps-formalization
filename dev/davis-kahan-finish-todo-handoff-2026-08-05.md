# Finishing Davis--Kahan 1970 — handoff, 2026-08-05

Written at `bc302ccb`, on `main`, pushed.  `lake build` green; the extra targets
`DavisKahan.Experimental Challenge FinishTanTwoTheta` green; census checker
**CLEAN**; every gate passes except `check_library_structure` rule 3, which was
already failing before this session (6 pre-existing violations, unchanged).

This document is the to-do list for **finishing Sections 4 and 2**, which is
where the work was directed.  Everything else that was on the task list is
parked at the bottom so it is not lost.

Read this next to `dev/davis-kahan-1970-full-source-census.json` — the census
rows carry the detailed evidence and the traps; this file carries the *order of
work* and the bricks that have been located but not yet laid.

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
* Commit and push finished work without being asked.
* `TauCetiRoadmap` `Suggested.lean` files are API sketches — never report
  `sorry` there.
* Before any mass refactor, grep for a docstring that already recorded the
  decision.

---

## 1. What landed today, and the two patterns worth carrying forward

Nine commits, ending at `bc302ccb`.  Census status counts now:
13 `compiled_exact`, 18 `compiled_general_infrastructure`,
4 `compiled_specialization`, 8 `partial_or_wrapper_missing`,
1 `refuted_as_transcribed`, 1 `resolved_by_modern_development`,
3 `not_a_completion_obligation`.

| Row | Was | Now |
|---|---|---|
| `DK-3.1-prop` | `partial_or_wrapper_missing` | `compiled_exact` |
| `DK-4.2-prop` | `compiled_specialization` | `compiled_exact` |
| `S2-tan-theta` | `compiled_specialization` | `compiled_exact` |
| `DK-6.3-thm` | conditional on a hypothesis with no producer | unconditional |
| `S2-tan-two-theta` | two recorded gaps | both closed |
| `DK-4.3-prop` | frontier statement `sorry` **and false** | restated correctly, still open |

**Pattern one — a hypothesis with no producer.**
`HasTheorem63DirectedTangentApproximationNumbers` appeared in *every* compiled
form of Theorem 6.3 and nothing in the repository ever constructed one.  The row
read `proved_in_build`: true of the declarations, misleading about the
mathematics.  Building the witness took ~150 lines and needed **no new
hypothesis** — the `sᵢ < 1` it wanted was already derivable from the source gap
by a lemma in the same file.  This is the second instance in this tree (the
first was `CorrespondingEigenblock`).  **Grep for producers, not consumers.**

**Pattern two — an underscore binder marks a fake scope gap.**
The census recorded "the equal-dimension Section 2 tangent theorem" as blocked
because Theorem 6.3 assumes `rank Z < rank V`.  The compiled theorem bound that
hypothesis as `_hStrictDimension` and never used it.  Restating without it was
four lines.  The printed inequality exists only to force finite-dimensionality
of the trial space under the paper's separability convention, and that was
already an explicit instance argument.  **Before working a "cannot specialise,
hypothesis too strong" obligation, read the binders.**

A third of the closures this session were bookkeeping rather than mathematics.
Check before building.

---

## 2. TRAPS — read before touching Section 4

Section 4 has produced **three** refuted transcriptions.  In every case the
*paper* is fine and the *transcription* was not.

1. **`DK-4.4-prop` is `refuted_as_transcribed`.**  A compiled ℝ⁴ counterexample
   beats the direct rotation in trace norm of the full displacement `1 − W`.
   Anything phrased on the **full** displacement must be checked against it.

2. **Proposition 4.2, twice.**  First form quantified over an arbitrary `Finset`
   of an orthonormal family with no completeness requirement — false, refuted by
   any non-principal unit vector.  Second form added the basis hypothesis but
   compared against `∑ᵢ cost D bᵢ`, which is *not* the paper's basis-free
   right-hand side — also false (ℝ⁴, principal angles `0` and `arccos(1/10)`,
   basis rotated `0.2` rad: competitor `1.028237` vs direct rotation
   `1.051417`).  **Do not restate the right-hand side as `∑ᵢ cost D bᵢ`.**  The
   correct right-hand side is `∑ᵢ (1 − ‖C bᵢ‖²) = dim U − tr((C|_U)²)`.

3. **Proposition 4.3's frontier form, found today.**  It asserted pointwise
   domination of the individual approximation numbers of the squared
   displacement.  That implies Ky Fan majorisation and hence Proposition 4.4,
   which this repository refutes — so it cannot hold.  Refuting configuration:
   ℝ⁴, `U = span(e₁,e₂)`, `V` at principal angles `π/4, π/4`, competitor
   carrying `U` onto `V` by a quarter turn in the `V`-frame and `Uᗮ` onto `Vᗮ`
   by the identity; then `a₂(1−D) = 0.765367 > 0.261052 = a₂(1−W)`.
   **Do not attempt pointwise approximation-number domination.**  Proposition
   4.3 itself survives because its Ky Fan sums are sums of *squares*, and those
   are dominated at every `k`.

Also: **frontier declarations must never go in a census row's
`lean_declarations`** — `DavisKahan.Experimental.Frontier` is built by no default
target, so listing one drops the row to `partially_in_build`.  The census
checker catches it.

---

## 3. DK 4 — remaining work

Sections 4's rows: `DK-4.2-prop` is done (`compiled_exact`), `DK-4.4-prop` is
refuted with no outstanding action.  What is left is Proposition 4.3's infinite
form, plus guarding and wrappers for 4.1, Cor 4.1 and 4.3.

### DK4-A — the infinite-dimensional Proposition 4.3 (Ky Fan)

Target: `proposition4_3_squaredDisplacement_kyFan`, the **last `sorry` in
`DavisKahan/Experimental/Frontier/Section4.lean`**.

The proof chain, all four steps now identified:

```
kyFan_k(2 − 2C)                            -- D's squared displacement, already pinch-diagonal
  = kyFan_k(blockSum of D's two blocks)    -- A2
  ≤ kyFan_k(blockSum of W's two blocks)    -- A3 + kyFanApproximationGauge_blockSum_le (EXISTS)
  = kyFan_k(pinch((1−W)*(1−W)))            -- A2
  ≤ kyFan_k((1−W)*(1−W))                   -- A1, DONE
```

**A1 — pinching contraction. DONE, `bc302ccb`.**
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Pinching.lean`:
`kyFanApproximationGauge_diagonalPart_le` and
`kyFanApproximationGauge_reflectionConjugate_le`.  Default build, axiom-clean,
~90 lines, first try.  It is three lines of mathematics because the pinch is an
average of two unitary conjugations —
`Submodule.two_smul_diagonalPart_eq_add_reflectionConjugate` already said so —
and the Ky Fan gauge is subadditive over ℂ
(`kyFanApproximationGauge_add_le_complex`, unconditional for ℂ) and
conjugation-invariant.

**A2 — chart the pinch as a block sum.  Three pieces, all bricks located.**

* *(a)* Ky Fan gauge transport across a linear isometry equivalence:
  `kyFan k (e ∘L A ∘L e.symm) = kyFan k A`.  Both directions from
  `kyFanApproximationGauge_comp_le` with `‖e‖ ≤ 1`
  (`LinearIsometry.norm_toContinuousLinearMap_le`).  Prove the `≤` direction
  once as a private lemma and apply it twice (once with `e`, once with `e.symm`)
  — do *not* `rw` a self-referential equation.  Put it in the ForTauCeti
  `Pinching.lean` written today.
* *(b)* The chart identity
  `e ∘L (U.diagonalPart A) ∘L e.symm = continuousOrthogonalBlockSum (P_U A ι_U) (P_Uᗮ A ι_Uᗮ)`
  where `e = U.orthogonalDecomposition : H ≃ₗᵢ[ℂ] WithLp 2 (U × Uᗮ)`
  (**Mathlib**, `Analysis/InnerProductSpace/ProdL2.lean`;
  `orthogonalDecomposition_apply` and `_symm_apply` are both `simp`).  Pointwise
  on `toLp (u, u')` it is immediate: `diagonalPart A (u + u') = P_U A u + P_Uᗮ A u'`.
* *(c)* The blocks themselves: the `U`-compression of `(1−W)*(1−W)` is
  `((1−W) ∘L ι_U)* ∘L ((1−W) ∘L ι_U)`, same on `Uᗮ`; and `2 − 2C` is already
  pinch-diagonal because `C` commutes with `P_U`
  (`spectraCanonicalAbsoluteValue_commute_projection`).

**A3 — Proposition 4.1 for the complementary pair `(Uᗮ, Vᗮ)`.**
`InfiniteProposition41` proves `aₙ((1−D) ∘L P_U) ≤ aₙ((1−W) ∘L P_U)` for `(U,V)`
(`MathAhead.Section4.proposition4_1_restrictedDisplacement_approximationNumbers_scratch`).
The complement needs:

* `IsAcute Uᗮ Vᗮ` from `IsAcute U V` — literally the same number, since
  `‖P_Uᗮ − P_Vᗮ‖ = ‖(1−P_U) − (1−P_V)‖ = ‖P_V − P_U‖`.
* **The direct rotation of `(Uᗮ, Vᗮ)` is the same operator `D`.**  `D` maps `Uᗮ`
  onto `Vᗮ` (`spectraDirectRotation_maps_orthogonalComplement`), squares to
  `J_Vᗮ J_Uᗮ = J_V J_U`, and has nonnegative numerical range — so
  `spectraDirectRotation_unique_of_sq` identifies it.  This is a clean reuse of
  today's DK-3.1 work.
* Admissibility of `W` for the complementary pair: subtract
  `W * projection U = projection V * W` from `W`.
* Two glue lemmas: `aₙ((1−W) ∘L projection U) = aₙ((1−W) ∘L U.subtypeL)` (the
  pre-composition analogue of `approximationSingularValue_subtypeL_comp`, proved
  today in `Theorem63FiniteSource.lean`), and `aₙ(T*T) = aₙ(T)²`.

**A4 — assemble.**  Consumes A1–A3 plus the block-sum Ky Fan machinery that
**already exists** in `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean`:
`kyFanApproximationGauge_continuousOrthogonalBlockSum`,
`kyFanApproximationGauge_blockSum_le`, `splitKyFanGauge_mono`,
`hasSameApproximationNumbers_continuousOrthogonalBlockSum`.

Estimated: A2 + A3 + A4 is roughly 300–400 lines and one solid session.  No
missing mathematics remains — every brick is either built or located.

### DK4-B — guard Section 4's infinite chain

`DK-4.1-prop`, `DK-4.1-cor` and `DK-4.3-prop` all rest on declarations that
compile only under `DavisKahan/Experimental`, so `lake build` does not guard
them.  Promote `Experimental/MathAhead/Section4/InfiniteProposition41.lean`
(infinite Prop 4.1 plus the Cor 4.1 ideal-gauge bridge), and
`directRotation_minimizes_restrictedDisplacement_uiNorm` /
`directRotation_minimizes_displacementSquare_uiNorm`.

**Measure the import closure first.**  The Section 8 chain turned out to be 42
modules with a `sorry` in it; do not assume this one is small.  The cost is
namespace renames, not mathematics.

### DK4-C — source wrappers

Clears `exact-source-wrappers` on `DK-4.1-prop` and the wrapper half of
`DK-4.1-cor` and `DK-4.3-prop`.  Add `DavisKahan1970`-namespaced aliases for
`singularValues_restrictedDisplacement_le` / `_directRotation` (4.1),
`uiNorm_restrictedDisplacement_le` and
`directRotation_minimizes_restrictedDisplacement_uiNorm` (Cor 4.1),
`directRotation_displacementSquare_kyFan` / `_uiNorm` (4.3).  Blocked by DK4-B
for the ones currently in Experimental.

**Section 4 is finished when A4 and C land.**

---

## 4. DK 2 — remaining work

`S2-sin-theta`, `S2-tan-theta` and `S2-sharpness` are `compiled_exact`;
`S2-tan-two-theta`'s bounded content is done.  What is left:

### DK2-A — sin 2Θ source-general residual and perturbation forms

`S2-sin-two-theta` is `compiled_general_infrastructure`, blocked on
`exact-source-wrappers`, next action "Certify source-general residual and
perturbation forms."  The tan-Θ analogues were proved today
(`theorem6_3_generalizedTanTheta_equalRank_spectral`,
`theorem6_3_perturbation_equalRank`) and the sin-Θ side is already
`compiled_exact` (Theorem 6.1), so this is the double-angle sine statement at
the same scope.

**Check first whether the existing sin-2Θ declarations already cover it and only
a wrapper is missing.**  Two of three Section 2 gaps closed today were exactly
that.

### DK2-B — exact Theorem 5.2 wrapper

`DK-5.2-thm`, blocked on `exact-source-wrappers`: "Expose an exact Theorem 5.2
wrapper and include it in the full-paper audit."  `S2-unbounded-scope` names
Theorem 5.2 as one of its two halves, so this is a hard prerequisite for the
unbounded scope claim.  Small.  Do the sibling `DK-5.1-lem` wrapper
(strong-cutoff convergence of singular values) while in the file.

### DK2-C1 — `DK-6.3-lem`, the finite-rank near-maximizer leakage estimate

`partial_or_wrapper_missing`: "State and prove the source lemma; it may be
useful independently for cutoff passages."  It is the quantitative brick the
Appendix's cutoff/Fan passage runs on — a near-maximizing finite-rank subspace
leaks only a controlled amount past a spectral cutoff.  **Do this before C2**:
it is the reusable half, and the Appendix chain is the assembly.

### DK2-C2 — the unbounded arbitrary-ideal tan-Θ cutoff/Fan passage

**The largest remaining piece of Section 2.**  `S2-unbounded-scope`: "the paper
claims arbitrary-UI-norm unbounded scope and the cutoff/Ky-Fan passage is not
yet formalized."  `DK-6-appendix`: "Audit every displayed appendix identity and
complete the arbitrary-ideal tangent cutoff/Fan passage; **do not infer it from
the compiled common-domain wrappers alone**."

*Exists*: common-domain and graph-core forms of Theorem 6.1 (`compiled_exact`),
the operator-norm unbounded graph-angle companion, `DK-5.1-lem`'s strong-cutoff
convergence of singular values.
*Missing*: the passage from bounded spectral cutoffs to the unbounded tangent at
arbitrary ideal-gauge scope.
Depends on DK2-B and DK2-C1.

**Trap, already on the census: do not credit the operator-norm companion as the
full scope claim.**

### DK2-D — guard the branch-selection rows `DK-8.1-thm` / `DK-8.2-thm`

Section 2's tan-2Θ chain now runs spectral separation → branch selection →
arbitrary-UI-norm bound entirely inside the default build
(`sharp_paperUnitaryInvariantNorm_selectedBranch`).  But the paper's *own*
branch-selection theorems are proved only outside the build, so CI does not
guard them.

**Measured 2026-08-05:** the import closure of
`Experimental/Sources/DavisKahan1970/Section8/SourceSurface.lean` is **42
Experimental modules**, and one of them —
`Experimental/InfiniteDimensional/SinTheta/General.lean:1109` — **still carries a
`sorry`**, so a straight promotion would drag a `sorry` into the default build.
Either finish that `sorry` first, or split the Section 8 chain off from the
SinTheta continuation stack.  `DK-3.2-prop` is unguarded for the same structural
reason and rides along.

### DK2-E — promote the sharpness witnesses and audit the equality models

`S2-sharpness` is `compiled_exact` but its next action is unfinished: the
constant-optimality and ratio-limit witnesses compile only under
`DavisKahan/Experimental/FiniteDimensional/Sharpness.lean`.  Two parts:
(i) promotion, so CI guards them; (ii) **the audit** — check each compiled
equality model against the printed simultaneous-equality claim.  That is exactly
the kind of scope question that produced three refuted transcriptions in
Section 4.

**Section 2 is finished when A, B, C1, C2, D and E land.**  C2 dominates the
effort.

---

## 5. Parked — not Section 2 or 4, do not lose

These were on the task list before it was narrowed to DK 4 and DK 2.

* **Section 9 free-beam operator.**  Five bricks laid and pushed: Green's
  identity for `d⁴/dx⁴` (`ForTauCeti/Analysis/Calculus/FourthOrderGreensIdentity.lean`),
  `L²`-orthogonality of modes at distinct frequencies, the Rayleigh identity,
  nonnegativity, and normalisation positivity
  (`Sources/DavisKahan1970/Section9/FreeBeamOrthogonality.lean`).
  Remaining: **completeness of the mode family in `L²(0,1)`** (the last step
  needing no Sobolev theory), then **the densely defined self-adjoint operator**,
  which is where `H⁴(0,1)` and traces actually enter — and *only* there; they
  are not needed for Green's identity, orthogonality, the quadratic form or
  positivity.
  **Trap:** do NOT "close" Section 9 by instantiating `TheoremOutputCertificate`
  or `FreeBeamFiniteDataCertificate` — both are trivially instantiable and
  certify nothing.  `Frontier/Section9Analytic.lean`'s eight `actual*`
  quantities are `sorry`-ed **definitions**.
* **Hahn--Hellinger** — needed only for Theorem 3.1's literal
  spectral-multiplicity phrasing.  Explicitly **off** the critical path: the
  classification content of Theorem 3.1 is proved in the paper's own invariant,
  both directions, admission-free.  `SameSpectralMultiplicity` is
  `def _ : Prop := by sorry`, so the frontier statement resting on it is
  vacuous, not merely unproved.
* **`DK-3.5-prop`** — commutation identities are present; the maximal
  constant-angle eigenspace characterisation is not represented.
* **Consolidate the duplicated Halmos outer assembly.**
* **`check_library_structure` rule 3** — 6 pre-existing violations
  (5 real modules, 1 aggregate).  Exactly 14 modules must move, closed under
  imports; the real cost is namespace renames.

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

Expect exactly `[propext, Classical.choice, Quot.sound]`.  `check_library_structure`
is expected to report 6 rule-3 violations; everything else must be 0.
