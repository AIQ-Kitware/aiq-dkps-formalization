# Review — `ForTauCeti` T02, T03, T06, T11, T21, T22

**FILE PASS COMPLETE for six groups — 20 files, ~5,300 lines.** 2026-07-29,
`edward (aiq-gpu)`, lane `AUDIT`. Grouped into one document because the headline
finding spans T01–T03 and would be invisible reviewing any one of them.

| group | files | verdict |
|---|---|---|
| **T02** Polar decomposition and partial isometries | 5 | **duplicate modulus API, T02-1**; three polar factors, T02-2 |
| **T03** Singular values and the singular system | 4 | good; one namespace defect (extends `T01-NS`) |
| **T06** Principal angles, aligned bases, finite frames | 3 | good, coherent |
| **T11** Hilbert–Schmidt operators | 4 | good, coherent |
| **T21** Matrix rank factorization / PSD | 2 | **asserts a Mathlib target, T21-1** |
| **T22** Berge / approximate minimizers | 2 | **asserts a Mathlib target, T21-1** |

## Finding T02-1 — the operator modulus exists twice, under two names `{lane:MODULUS-DEDUP}`

`ForTauCeti` defines the absolute value of an operator **twice**:

| | `PolarDecomposition.lean:50` | `OperatorModulus.lean:82` |
|---|---|---|
| name | `TauCeti.abs` | `ContinuousLinearMap.modulus` |
| carrier | `E →ₗ[𝕜] E` (`LinearMap`) | `E →L[ℂ] F` (`ContinuousLinearMap`) |
| scalars | `RCLike`, finite-dimensional | `ℂ`, general Hilbert |
| built from | `(isPositive_adjoint_comp_self A).sqrt` | `CFC.sqrt (T⋆ ∘L T)` |
| API | `abs_mul_self`, `norm_abs_apply`, `ker_abs`, `range_abs` | `modulus_mul_self`, `norm_modulus_apply`, `modulus_apply_eq_zero_iff`, … |

The two APIs are **the same theorems under two names**, and the give-away is in
the source: `PolarDecomposition.lean:53`, documenting a lemma about `abs`, calls
it *"**The modulus** is a positive operator"*. The file names the object one way
and describes it the other.

**This makes an already-completed deduplication look finished when it is not.**
`OperatorModulus.lean`'s provenance states that it replaced two parallel APIs —
`rectangularOperatorModulus` and `operatorAbs` — with a single rectangular
definition, per `dev/tauceti-signature-polish-todo.md` §7. That work was real and
the resulting file is the best in T01. But **`TauCeti.abs` survived it**, so the
library still carries a second modulus, in the adjacent topic, imported by six
`ForTauCeti` modules.

**Why this is not simply "delete `abs`".** The two live at genuinely different
generalities: `modulus` needs ℂ because Mathlib registers the CFC only there,
while `abs` is `RCLike`-generic and finite-dimensional, and the polar
decomposition in T02 is stated over `RCLike`. So the resolution is the same
design question T01-SQRT raises: which carrier is canonical, and does the other
become a specialization or disappear? **That is one decision covering both
lanes**, and it should be made once.

## Finding T02-2 — three polar factors in one topic `{lane:MODULUS-DEDUP}`

T02 contains `polarFactor` (`PolarDecomposition.lean`), `polarPartial`
(`PolarPartialIsometry.lean`, 687 lines) and `polarIsometryOfIsUnitModulus`
(`PolarIsometry.lean`). Each is "the isometric factor of the polar
decomposition" under a different hypothesis — general, partial-isometry, and
invertible-modulus respectively.

That is defensible mathematics: the three cases really do need different
constructions. It is **not** defensible as three unrelated names with no stated
relationship. None of the three docstrings mentions the other two. A reviewer
opening T02 cannot tell whether these are a designed hierarchy or three
independent attempts, and the file sizes (415 / 687 / 282) mean finding out
costs an hour.

**The fix is documentation, not code**: one paragraph in each naming the other
two and the hypothesis that separates them. Folded into the same lane because
the naming should be settled at the same time.

## Finding T03/T01 — `namespace FiniteDimensional` is used twice, not once `{lane:T01-NS}`

`MoorePenroseInverse.lean:58` also opens `namespace FiniteDimensional`, so the
public name is `FiniteDimensional.moorePenroseInverse`. This is the second
offender after `SelfAdjointFunctionalCalculus.lean:38`. **Lane `T01-NS` is
updated to cover both**; the argument is unchanged — `FiniteDimensional` is a
core Mathlib namespace and neither of `ForTauCeti/README.md` §2's two
justifications applies.

## Finding T21-1 — four modules assert a Mathlib upstream target `{lane:HDR-DEST}`

All four ex-`ForMathlib` modules — `LinearAlgebra/Matrix/{PosDef,
RankFactorization}.lean` and `Topology/{Berge,ApproxMinimizer}.lean` — carry:

> *Extraction class: **authored in place**. Upstream target is **Mathlib**; the module …*

This is the strongest form of the `HDR-DEST` problem and the only one that is
**not merely a stale header**: it is the module's declared *extraction class*,
the field `ForTauCeti/README.md` §5 requires, asserting a destination that the
retirement of `ForMathlib` was supposed to settle.

It is also the precise text the `CANDIDATE-TOPIC-DESIGN.md` addendum predicted
would be here, and it needs the decision recorded there: T21 and T22 are the two
topics most plausibly Mathlib-bound rather than Tau Ceti-bound. Either they are
re-aimed at Tau Ceti like everything else, or `ForTauCeti` is knowingly hosting
Mathlib-bound material and `AGENTS.md` should say so. **Jon's call.**

## What is good

- **T06 and T11 are coherent and need nothing.** T06's three files build one
  chain — `familyMap` → `familyIsometry` → `overlapOp` → principal angles — with
  each file consuming the previous one's API rather than rebuilding it. T11's
  four Hilbert–Schmidt files are similarly linear (`columns` → `ofLp` →
  conjugation → Pythagoras) and nothing in them is duplicated elsewhere.
- **`SingularValues.lean` (124 lines, 8 declarations) is the right size and
  shape**: one definition and the seven facts a consumer needs, no more.
- **`RankFactorization.lean` and `PosDef.lean` are genuinely Mathlib-shaped** —
  which is exactly why their extraction class is a live question rather than a
  typo. The mathematics (rank factorization, PSD Gram realization) is standard,
  self-contained, and would be accepted in `Mathlib/LinearAlgebra/Matrix/`.
- **`Berge.lean` proves a real theorem** (upper hemicontinuity of the argmin
  correspondence) and its companion `ApproxMinimizer.lean` is properly factored
  out rather than inlined.

## Group verdicts

- **T02 is the least submittable group reviewed so far** — not because the
  mathematics is weak, but because a reviewer meets three polar factors and a
  second modulus with no map between them. Fix the naming and the relationships
  and it is fine.
- **T03, T06, T11 are close to submittable**, modulo the shared namespace defect.
- **T21, T22 are blocked on a decision, not on work.**
