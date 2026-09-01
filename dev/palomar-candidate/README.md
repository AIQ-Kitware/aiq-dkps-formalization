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
| lines | **600** | hard 1000, preferred 300 |
| bytes | **29,683** | hard 102,400, preferred 32,768 |
| imports | **`Mathlib` only** | Lean core + allowlisted Mathlib/Tau Ceti/CSLib |
| definitions and structures | 37 | ordinary concrete definitions; **not** `definition_names` |
| headline theorems | 4 | `sorry`-bodied, per the Comparator convention |
| supporting theorems | 1 (`Reduces.orthogonal`) | proved; needed for the `sin 2Θ` statement to typecheck |
| functional calculus | **absent** | — |

`Solution.lean` is 1,983 lines and contains no `sorry`, no `admit` and no `axiom`.

The line count is over Palomar's *preferred* 300 and under its hard 1000, so
`check_palomar_readiness.py` would warn, not fail. Four full theorems with their
own vocabulary do not fit in 300 lines. The byte count is now **2,784 bytes below
the preferred 32 KiB**, where it used to sit three bytes under it; the margin came
entirely out of prose that belongs in this file and in the statement audit, not
out of any definition or statement.

## Comparator configuration

```json
"theorem_names": [
  "RotationOfEigenvectors.sinTheta",
  "RotationOfEigenvectors.tanTheta",
  "RotationOfEigenvectors.sinTwoTheta",
  "RotationOfEigenvectors.tanTwoTheta"
],
"definition_names": []
```

`definition_names` is Palomar's mechanism for definitions whose *value* the
Challenge leaves unspecified and the Solution supplies. Every definition here is
concrete, so none of them belongs in that list; an earlier draft of this file
said all 39 would be listed, which was a misreading of the policy. A definition
hole would have to be justified on its own terms, and none is.

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
   Appendix scope the source explicitly allows *for the tangent theorem*.
   `TrialBlock.compression` is now a partial map `U →ₗ.[𝕜] U`, with only the
   residual bounded. See the next section for where that relaxation stops.
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

## Where the unbounded compression stops: `sin 2Θ` is bounded

A second pass found the mirror image of defect 2: having learned that the
compression may be unbounded, the draft made it unbounded everywhere. The
Appendix to Section 6 is specific about which theorems get which relaxation:

> For the sine theorem, one of `A₀, Λ₁` may be unbounded. … Proposition 6.1 and
> Theorem 6.1 admit the analogous relaxation.
>
> For the tangent theorem the Appendix explicitly returns to the ordered
> hypotheses `A₀ ≤ α` and `Λ₁ ≥ α+δ` in the general case and allows *both* `A₀`
> and `Λ₁` to be unbounded.

So the sine family — the `sin Θ` theorem, Proposition 6.1, Theorem 6.1 — gets
"one of the two", and only the tangent theorem gets "both". **No double-angle
result is named in the Appendix at all.** In the directed `sin 2Θ` configuration
the unwanted exact block is the unbounded one, which is exactly the allowed
shape, so the trial compression there stays bounded.

The Challenge therefore has two trial-data structures, and the difference between
them is the source's:

* `TrialBlock` / `RitzData` — partial compression, for `tan Θ`, where the
  Appendix asks for it;
* `BoundedTrialBlock` — bounded compression, for `sin 2Θ`.

This also removes the inconsistency the repository was carrying: the production
semantic audit had already concluded that directed `sin 2Θ` is not extended to an
unbounded compression, while this Challenge went on demanding it.

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

## What is proved

Everything, at the Challenge's own scalar scope.  `Solution.lean` proves all seven
printed clauses and assembles them into the Challenge's four theorems:

| Challenge theorem | `Solution.lean` |
| --- | --- |
| `sinTheta` | `sinTheta_solution` |
| `tanTheta` | `tanTheta_solution` |
| `sinTwoTheta` | `sinTwoTheta_solution` |
| `tanTwoTheta` | `tanTwoTheta_solution` |

| printed clause | proof |
| --- | --- |
| `sin Θ` | `sinTheta_proof` |
| `tan Θ` directed | `tanTheta_directed_proof` |
| `tan Θ` ambient | `tanTheta_ambient_proof` |
| `sin 2Θ` directed | `sinTwoTheta_directed_proof` |
| `sin 2Θ` ambient | `sinTwoTheta_ambient_proof` |
| `tan 2Θ` directed | `tanTwoTheta_directed_proof` |
| `tan 2Θ` ambient | `tanTwoTheta_ambient_proof` |

Each is stated at an arbitrary `[RCLike 𝕜]` with **no capability binder, no
field-dispatch hypothesis, no finite-dimensionality hypothesis and no spectral
selection of the trial subspace**, and each depends on exactly `propext`,
`Classical.choice`, `Quot.sound`.

Also proved here, as the bridge the four theorems rest on: the norm
correspondence by `rfl` (`UINorm.toPaper`, `eval_eq`, `finite_iff`, `norm_eq`);
the separation constructor by constructor, both half-infinite branches;
reduction, blocks and the bounded perturbation of a partial map; the trial data
field for field with the compression still a partial map
(`RitzData.toUnboundedRitzPair`); and the off-diagonal condition as the
development's `IsOddFor`.

## Two corrections this pass made to the mathematics

**The doubled tangent must be read off the doubled sine.**  An earlier draft
applied `|tan (2 arcsin ·)|` index by index to the approximation numbers of the
*single*-angle sine.  That is wrong at arbitrary dimension: `θ ↦ sin 2θ` is not
monotone on `[0, π/2]`, so the transformed sequence need not be ordered.
Principal angles `75°` and `30°` already invert it — `sin 75° > sin 30°` while
`sin 150° < sin 60°`.  Both `tan 2Θ` clauses now read the doubled tangent off
`directedDoubleSine` / `ambientDoubleSine` through the *monotone*
`u ↦ tan (arcsin u)`, and `absTanTwoSeq`, `DoubleTangentDefined` and
`directedSineCorner` are gone.

**The pole certificate had to move with it.**  `DoubleTangentDefined` looked only
at the single-angle sine's approximation numbers, which a noncompact operator's
interior spectral value can evade.  The certificate is now `TangentDefined` of
the double-angle sine, whose `a₀` is `‖sin 2Θ‖`: the uniform quarter-turn
exclusion that production derives from the ordered gap.

## How the scalar field was closed

Not by making the machinery generic — `gramOperator`, `cfc` and the double-angle
functional calculus are complex — but by **transport**.  Every quantity a
Challenge clause mentions is a function of one operator's singular-value
sequence, and `TauCeti.ScalarTransport` renames the field without touching the
vectors, the additive group, the topology, the norm, the operators, or that
sequence.  `RCLike.I_eq_zero_or_im_I_eq_one` supplies the case split; the real
branch of each `tan` clause is itself proved by complexification, so the analysis
happens once, over `ℂ`.

| module | carries |
| --- | --- |
| `ForTauCeti/Analysis/RCLike/ScalarTransport.lean` | the field isomorphism `RCLikeIso`, and `ScalarTransport e E` — `E` with the induced `𝕂`-structure — with subspaces, `ᗮ`, orthogonal projections, bounded operators (function, norm, adjoint, self-adjointness), `Module.rank`, and partial maps |
| `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/ScalarTransport.lean` | approximation numbers, linear independence, spans — hence the min–max instance |
| `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/ScalarTransport.lean` | reducing subspaces, and adding a bounded operator to a partial map |
| `ForTauCeti/Analysis/InnerProductSpace/Projection/ScalarTransport.lean` | reflections, and the mirror image of one subspace in another |
| `ForTauCeti/Analysis/RCLike/ScalarTransportIsometry.lean` | linear isometric equivalences, and intersections — hence the crossed-defect condition (3.5) |
| `DavisKahan/Sylvester/ScalarTransport.lean` | finite Ky Fan gauges, operator-form semibounds, the real resolvent set and spectrum, the three-constructor separation, the domain-aware Sylvester equation — hence the Sylvester instance |

Restriction of scalars (`InnerProductSpace.rclikeToReal`) is the wrong tool here:
over a complex-like `𝕜` it halves the scalars, doubling `Module.rank` and
changing the singular-value sequence.  The transport changes no ranks because it
changes no scalars — it renames the field.

One diagnostic worth keeping: a helper that only reads a singular-value sequence
had been stated over `ℂ`, and the whole `Solution.lean` then stalled at `whnf`
inside the real branch.  A fixed-field helper inside a scalar-generic proof is
not merely inelegant here; it is a hang.

## The Comparator layout this is not yet in

`Solution.lean` here imports `Challenge` for its vocabulary.  That is right for a
bridge file inside the development and wrong for a submission: the Comparator
compares two independently exported environments, so the submitted `Solution.lean`
must **not** import `Challenge`, and must redeclare the Challenge's definitions
verbatim and then the four advertised names, at the same types, with these proofs.
The conversion is mechanical — the definitions are copied and the four theorem
bodies are the `*_solution` terms above — and it belongs in the standalone
submission repository under `submodules/`, together with a refreshed mechanical
extraction of the development, a `registry/` entry, and the real Comparator run.

Nothing has been submitted or registered.
