# Palomar candidate: the four Davis–Kahan Section 2 theorems

A **development spike**, not a submission. Nothing here has been submitted to or
registered with Palomar. The standalone submission repository under
`submodules/` owns the real Challenge/Solution surfaces and the packaging
policy; this directory answers two questions ahead of that work.

**Question 1 — can a four-theorem Section 2 Challenge be written inside the
Palomar envelope?** Answered: yes.

**Question 2 — are the statements source-faithful enough to prove?** Answered
for the first draft: no, in four separate ways. This directory now holds the
repaired statements and the audit that will keep them honest.

## Measurements

| | Challenge.lean | limit |
| --- | --- | --- |
| lines | **684** | hard 1000, preferred 300 |
| bytes | **32,765** | hard 102,400, preferred 32,768 |
| imports | **`Mathlib` only** | Lean core + allowlisted Mathlib/Tau Ceti/CSLib |
| definitions and structures | 39 | supplied to the Comparator as `definition_names` |
| headline theorems | 4 | `sorry`-bodied, per the Comparator convention |
| supporting theorems | 1 (`Reduces.orthogonal`) | proved; needed for the `sin 2Θ` statement to typecheck |
| functional calculus | **absent** | — |

`Solution.lean` is 471 lines and contains no `sorry`, no `admit` and no `axiom`.

The line count is over Palomar's *preferred* 300 and under its hard 1000, so
`check_palomar_readiness.py` would warn, not fail. Four full theorems with their
own vocabulary do not fit in 300 lines.

## Reproducing

```bash
lake env sh -c 'LEAN_PATH="$PWD/dev/palomar-candidate:$LEAN_PATH" \
  lean -o dev/palomar-candidate/Challenge.olean dev/palomar-candidate/Challenge.lean'
lake env sh -c 'LEAN_PATH="$PWD/dev/palomar-candidate:$LEAN_PATH" \
  lean dev/palomar-candidate/Solution.lean'
rm -f dev/palomar-candidate/*.olean dev/palomar-candidate/*.ilean
```

The Challenge reports exactly four `declaration uses 'sorry'` warnings and the
Solution reports none. Build products are removed: Palomar rejects committed
build artifacts.

## The idea that made it fit: name the angle, do not construct it

A unitarily invariant norm is a symmetric norming function of a singular-value
sequence. It cannot see anything else. So no angle operator has to be *built* by
a continuous functional calculus — which is where the first "blocked" verdict
went wrong, because Mathlib's complex functional calculus is not what a Challenge
may import and the real one lives in the development.

* `sin Θ₀` is the paper's own `(I − F₀F₀⋆)E₀`.
* `sin Θ` is the projector difference `P_V − P_U`.
* `sin 2Θ` is the projector difference between `U` and its mirror image in `V` —
  reflecting doubles every principal angle.
* `sin 2Θ₀` is `U`'s overlap with the mirror of its own complement.
* The **tangents are sequences**: `UINorm.evalSeq` measures a unitarily invariant
  norm on `tan θ₁, tan θ₂, …` directly. No representative operator is quantified
  over, so no tangent conclusion can be made vacuous.

## What the repair pass changed

The first draft stated four theorems that were not the paper's. All four defects
came from writing a compact restatement without checking it clause by clause,
and all four are now fixed:

1. **`tan Θ₀` was defined from the residual.** The draft said
   `∀ T, IsTangentOf R T → …`, i.e. `tan(arcsin sₙ(R))` — a different quantity
   from the tangent of the principal angle, and the residual belongs on the
   right-hand side of the inequality, not the left. `tanSeq` now takes a *sine*,
   and its docstring names the mistake so it is hard to make again.
2. **The Ritz compression was forced to be bounded.** `M : U →L[𝕜] U` loses the
   Appendix scope the source explicitly allows. `TrialBlock.compression` is now a
   partial map `U →ₗ.[𝕜] U`, with only the residual bounded — which is exactly
   what the source's scope paragraph requires.
3. **The directed clauses inherited the ambient clause's ideal membership.**
   `N.Finite H` sat outside the conjunction, so `δ‖tan Θ₀‖ ≤ ‖R‖` could only be
   invoked when the whole perturbation lay in the ideal. The three two-clause
   theorems now conclude in a record — `TanThetaResult`, `SinTwoThetaResult`,
   `TanTwoThetaResult` — whose fields carry their own data and their own
   membership premise. The directed `tan 2Θ` premise is membership of the
   residual *corner*.
4. **The tangents could be vacuous, and a pole read as zero.** `Real.tan (π/2)`
   is `0` in Lean. Each tangent theorem now *concludes* `TangentDefined` /
   `DoubleTangentDefined` — there is no pole — which is what Section 7 of the
   source derives rather than assumes, and what the development's own `tan 2Θ`
   endpoints conclude with `IsUnit …`.

## The reducing-versus-spectral question, resolved

Section 1 of the source says in as many words that neither `P` nor `Q` is assumed
to be a spectral projector. The theorems add a *separation* hypothesis on the two
blocks; a separated reducing decomposition then *is* spectral, but that is a
theorem and not a hypothesis. So the reducing formulation is the printed one, and
the Challenge keeps it.

For `sin 2Θ` this is not just an argument: `Solution.sinTwoTheta_ambient_of_capabilities`
**proves** the ambient clause at an arbitrary reducing subspace, from
`sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm`, which the
development already states at that scope. The remaining spectral-only endpoints
(`sin 2Θ` directed, both `tan 2Θ` clauses) are recorded as *production*
narrowings rather than Challenge defects.

## What is proved, and what is open

Proved in `Solution.lean`:

* the norm correspondence, by `rfl` — `UINorm.toPaper`, `eval_eq`, `finite_iff`,
  `norm_eq`;
* the separation, constructor by constructor, both half-infinite branches;
* reduction, blocks, and the bounded perturbation of a partial map;
* the trial data, field for field, with the compression still a partial map
  (`RitzData.toUnboundedRitzPair`);
* the off-diagonal condition as the development's `IsOddFor`;
* **`sin Θ`**, and **the ambient clause of `sin 2Θ`** — both modulo the two
  development capability classes, which are instances at `ℝ` and at `ℂ`.

Open, and named per clause in
[`../palomar-section-two-challenge-statement-audit.md`](../palomar-section-two-challenge-statement-audit.md):

* the scalar-field transport that discharges
  `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜` and
  `HasUnboundedSylvesterKyFan 𝕜` at an arbitrary `RCLike` field;
* the `sin 2Θ` directed clause at a reducing subspace and an unbounded
  compression;
* tangent representatives and the derived no-pole facts for `tan Θ` and
  `tan 2Θ`.
