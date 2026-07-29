# Davis–Kahan 1970 frontier — session handoff (2026-07-24)

Continuation brief for a fresh session picking up the recursive DK-1970
formalization. You are **jon, window A** (identity is by human, not model).

## Environment & conventions
- Repo `/home/joncrall/code/aiq-dkps-formalization`, Lean 4 + pinned Mathlib
  v4.32.0, vendored `vendor/Spectra`. Default build `DavisKahan.All` (~9097 jobs)
  **excludes** `Experimental/**` and `Scratch/**`; it must stay green.
- Commit with `--no-gpg-sign` and trailer
  `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
- **Never `git add -A`** — the working tree is shared with other agents; stage
  explicit paths only. Read `AGENTS.md` and `dev/LANES.md` first; claim a lane
  before editing.
- Frontier status is tracked by `scripts/check_davis_kahan_frontier.py` against
  the manifest `dev/davis-kahan-1970-frontier.json` (nodes: id/title/kind/module/
  declaration/dependencies). `--no-lean` is fast (textual + manifest validation);
  `--write-report` runs Lean-mode `#print axioms` on all 72 nodes (~20–40 min,
  builds the frontier) and regenerates `dev/davis-kahan-1970-frontier-status.md`.
  A node is 100% only when its whole dependency closure is `sorryAx`-free.

## Where the frontier stands (HEAD `d569af2`)
**34/72 manifest nodes recursively grounded; 15/32 paper results at 100%.**

Grounded paper results: DK 3.1 def+prop, **3.2** prop+cor, **3.3**, **3.4**,
**3.5** (Section 3 OneSpace is COMPLETE), Cor 3.2, **4.1** prop+cor, **5.1**,
Lemma 6.3, sin-2Θ (s7), tan-2Θ (s7).

Open (ungrounded), by owner:
- **jon (window A) — Section 4:** `s4-prop4-2`, `s4-prop4-3` (both directly
  `sorry`, ~50%). These are the only very-close open items in this lane.
- **user:** `s6-theorem6-3` (generalized tan-θ, 87%) and Section 8
  spectral-continuation (`s8-continuation-*`, `s8-circle-continuation-data`,
  `s8-projection-lipschitz`).
- **window B — Section 3 Classification:** `s3-operator-classification`,
  `s3-theorem3-1`, `s3-cor3-1`, `s3-compact-angle-list`,
  `s3-spectral-multiplicity-definition/-complete`.
- **edward — Section 8:** `s8-theorem8-1`, `s8-theorem8-2-*`,
  `s8-*-half-gap`, `s8-direct-rotation-{upper,lower}-data`, `base-section8-core`.
- **hard / unowned:** `base-theorem5-2` (unbounded Sylvester, 0%),
  `base-sharpness` (0%), Section 9 free-beam numerical model (`s9-*`, ~84%;
  the model `def`s are sorry-defined — needs assembly), `base-section9-*`.

## What this session closed (all axiom-clean unless noted)
Props 3.1, 3.3 (jon); Props 3.4, 3.5 (Section-3 agent, done); section7 sin/tan-2Θ,
Theorem 5.1, Prop 4.1 + Cor 4.1 (jon); `trialResidual`, DoubleAngle
`sinTwoTheta_residual` (jon/agent); manifest sync + status reports.

## Correctness findings raised (documented in-source)
1. `IsPaperDirectRotation` diagonal-compression fields are *numerical*
   (`0 ≤ re⟪x,(PTP)x⟫`), strictly weaker than operator-positivity — does NOT force
   Prop 3.1 uniqueness (counterexample: `exp(Iθ)` on `U=V`). Prop 3.1 carries two
   extra `IsSelfAdjoint` diagonal hypotheses. **Open improvement:** strengthen the
   `Core.lean` definition to operator-positive diagonals and drop the extra
   hypotheses (touches Core.lean = window B's file + re-proving Prop 3.2 existence
   + `spectraDirectRotation_isPaperDirectRotation`).
2. Prop 3.4's half-angle bound belongs on the cosine **square**
   (`re⟪x, halmosCosineSq x⟫ ≥ ‖x‖²/2`), not on `|S|`; and reflected-pair
   acuteness `IsAcute U (reflectedSubspace V U)` is an **independent** hypothesis.
3. `section7_tanTwoTheta`'s RHS needs the intrinsic double-cosine denominator
   `(2·N.gauge E)/(1 − 2·directedGap²)`; bare `2·N.gauge E` is too strong.
4. Theorem 5.1 (Banach) bounded-below hypothesis is insufficient (no bounded left
   inverse on general Banach) → corrected to explicit `BoundedLeftInverseData`.
5. Cor 4.1 needs `KyFanDominantIdealFamily`, not `RectangularSymmetricIdealFamily`.
6. `IsFixedCosineReducingSubspace` maximality was false as written (exterior
   vector counterexample) — corrected with the two complement conditions.

## namek-work workflow (recurring)
The user pushes compiled hard-theory to `origin/namek-work` (in `Scratch/**`);
you `git fetch origin namek-work && git merge --no-edit --no-gpg-sign
origin/namek-work`, then **elevate**: `git mv` the proof out of `Scratch/**` into
a source-facing `MathAhead/**` home (the build cannot depend on Scratch),
rename `namespace Scratch → MathAhead`, fix the internal import + the scratch
importers, then close the Frontier `sorry` with a thin `:=`. This produced the
acyclic Frontier→MathAhead edges (`MathAhead/Section4/InfiniteProposition41.lean`
for Prop 4.1; `Section3Nonacute` for Prop 3.2). **Trap hit:** after `git mv` +
`sed`, you must re-`git add` the moved files or the commit records only the
rename and drops the namespace fix (fixed in `bd5d071`).
Latest merged: the Section-7 tan-2Θ paired-singular-family core
(`Scratch/Section7/InfiniteTanTwoThetaCore.lean`, compiles, 0 real sorries) — it
is **foundational** (dimension-free Ky-Fan tan-2Θ under an explicit
`HasExactApproximationSingularFamilies` attainment hypothesis, deferred to the
future compact spectral bridge) and is **not** wired to any frontier node yet.
Its line-29 docstring contains the word "sorry" (trips the grep check) — fix on
the namek side, not by editing the active branch.

## Prop 4.3 route (cracked, with the real obstacle)
`(1 − star D)*(1 − D) = 2•(1 − |C|)` since `D + star D = 2|C|`
(`spectraDirectRotation_add_star_eq_two_smul_absoluteValue`, D unitary), and
`(1 − star W)*(1 − W) = 2•(1 − Re W)`. So 4.3 ⟺ `aₙ(1−|C|) ≤ aₙ(1−Re W)`.
Plan: build a **full-displacement** `CosineDisplacementData` (reuse the structure
in `MathAhead/Section4/InfiniteProposition41.lean`) to get `aₙ(1−D) ≤ aₙ(1−W)`,
then `aₙ((1−D)⋆(1−D)) = aₙ(1−D)²`.
**Obstacles (genuine):** (a) the competitor bound `re⟪Wx,x⟫ ≤ ‖|C|x‖·‖x‖` holds
on `U` and on `Uᗮ` separately, but the `U`/`Uᗮ` cross terms don't vanish for
general `x`, so the full-`x` quadratic lower bound is not immediate; (b)
`aₙ(T⋆T) = aₙ(T)²` (via `aₙ(|A|²)=aₙ(|A|)²` + `aₙ(A)=aₙ(|A|)`) is **not** in
`ForMathlib/Analysis/Normed/Operator/ApproximationNumber*.lean` and must be
proved. Prop 4.2 (squared-cosine Ky-Fan majorization) is similarly hard — scratch
has only the finite-dimensional form; the per-vector competitor bound does not
give the squared sum.

## Also still queued (user asked, deferred as risky during active namek churn)
Relocate compiled Scratch out of the staging area into permanent homes: FreeBeam
(~20 files, Section 9 analytic), RectangularHilbertSchmidt, SharedFoundations/
{Residual,Ideal,Spectral}. Redundant already-superseded scratch: `NonacuteExistence`
(= Prop 3.2), `Section7Wrappers` (= section7 sin/tan). Relocation conflicts with
the actively-churning namek-work branch, so coordinate timing.

## Traps / lessons
- `cfc_nonneg` needs `open scoped ComplexOrder`; prove `0 ≤ z+star z` via
  `Complex.le_def`. CLM kernel/range via dot notation (`X.ker`, `A.range`,
  `A.orthogonal_range`, `X.isClosed_ker`); membership via `LinearMap.mem_ker`;
  `A.ker.HasOrthogonalProjection` via `haveI : CompleteSpace A.ker :=
  A.isClosed_ker.completeSpace_coe`.
- `projection`/`complementaryProjection`/`reflectionOperator` are reducible
  abbrevs for `U.starProjection`/`Uᗮ.starProjection`/`U.reflectionOperator`.
- The `T + star T = 2|S|` identity (any RHP unitary square root of the reflection
  product) is the workhorse behind Prop 3.1/3.3 and the accretive branch.
