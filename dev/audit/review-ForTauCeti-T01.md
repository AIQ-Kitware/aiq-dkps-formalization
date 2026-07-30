# Review — `ForTauCeti :: T01` Positive square root, operator modulus, functional calculus

**FILE PASS COMPLETE — 9 of 9 files read.** 2026-07-29, `edward (aiq-gpu)`,
lane `AUDIT`. Group review below. 70 declarations, 1,643 lines, 0 proof escapes,
provenance present in all 9.

| file | lines | decls | verdict |
|---|---|---|---|
| `CourantFischer.lean` | 556 | 17 | good; 6 statements shared with its Challenge conformance (by design) |
| `SelfAdjointFunctionalCalculus.lean` | 238 | 13 | **namespace defect, T01-3** |
| `OperatorModulus.lean` | 208 | 16 | **best file in the group** |
| `PositiveSqrt.lean` | 180 | 11 | **duplicate construction, T01-2**; ticket metadata, T01-4 |
| `BasisSpan.lean` | 157 | 8 | good; a model extraction |
| `SpecialFunctions/Sqrt.lean` | 112 | 2 | good |
| `Spectrum.lean` | 72 | 1 | good |
| `Basic.lean` | 70 | 1 | good |
| `Normed/Operator/LinearIsometry.lean` | 50 | 1 | good |

## What is good — and it is most of the group

- **`OperatorModulus.lean` is the standard the rest should meet.** It defines
  `|T| = (T⋆T)^(1/2)` *rectangularly*, notes that the endomorphism case is a
  specialization rather than a second definition, justifies the ℂ-only scalars
  by Mathlib's CFC registration, and its provenance records that it **replaced
  two parallel APIs** (`rectangularOperatorModulus` and `operatorAbs`) with one.
  It also names the computational heart (`norm_modulus_apply`) and derives the
  four norm laws from it rather than reproving each. Nothing here needs work.
- **`BasisSpan.lean` is a model extraction.** Its header explains that the old
  `specSubspace` was "a predicate-selected span of an arbitrary orthonormal
  basis — not intrinsically spectral", so it was renamed, generalized from
  `Fin n` to an arbitrary index type, moved into `OrthonormalBasis`, and given
  the *complete* API rather than only the fragments its one caller needed. That
  is exactly the reasoning a Tau Ceti reviewer wants to see.
- **`Sqrt.lean` states why its two lemmas differ.** One needs no smallness
  hypothesis and is sharp; the other genuinely does, "as `μ ↓ 0` the left-hand
  side blows up". Explaining the *asymmetry* pre-empts the obvious review
  question.
- `CourantFischer.lean`'s 6 statement collisions are all against
  `Challenge/MathlibCandidate/CourantFischerWeyl/Conformance.lean`, which is a
  conformance restating the library theorem **by design**. Not a defect.

## Finding T01-2 — two square roots, one of them definitionally the other `{lane:T01-SQRT}`

`PositiveSqrt.lean` defines `LinearMap.IsPositive.sqrt` as a spectral sum.
`SelfAdjointFunctionalCalculus.lean` defines `selfAdjointFunctionalCalculus` as
the *same* spectral sum with a general `f : ℝ → ℝ`. Then, at line 224:

```lean
theorem selfAdjointFunctionalCalculus_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    selfAdjointFunctionalCalculus hT.isSymmetric Real.sqrt = hT.sqrt := rfl
```

**`rfl`.** The two constructions are not merely equal, they are *definitionally
identical* — `sqrt` is `selfAdjointFunctionalCalculus … Real.sqrt` with the
function inlined. So the library defines one object twice and then observes that
the definitions coincide.

A reviewer asks the obvious question: why is `sqrt` a separate `noncomputable
def` rather than an `abbrev` for the calculus at `Real.sqrt`? The current shape
means every fact about `sqrt` must be proved again or transported, and
`sqrt_comm` (line 230) is exactly that transport — it rewrites through
`selfAdjointFunctionalCalculus_sqrt` to reuse `selfAdjointFunctionalCalculus_comm`.

**Not a trivial fix, which is why it is a lane.** `PositiveSqrt.lean` carries
the *uniqueness* theory (`sqrt_unique`, `apply_eq_smul_of_apply_apply_eq_smul`)
that the general calculus does not, and its `ker_sqrt` / `range_sqrt` are stated
against `IsPositive`. Collapsing the definition without losing that API is a
design decision.

**There is a third square root in this group**: `OperatorModulus.lean` uses
Mathlib's `CFC.sqrt`. That one is *justified* — `PositiveSqrt`'s own docstring
explains it is the `𝕜`-generic `LinearMap` counterpart of the ℂ-only `CFC.sqrt`,
needed because the C⋆ instances exist only over ℂ. Keep both; the reviewable
question is only the first pair.

## Finding T01-3 — a module declares into Mathlib's `FiniteDimensional` namespace `{lane:T01-NS}`

`SelfAdjointFunctionalCalculus.lean:38` opens `namespace FiniteDimensional` and
puts `selfAdjointFunctionalCalculus` and its twelve lemmas inside it. So the
public name is `FiniteDimensional.selfAdjointFunctionalCalculus`.

`FiniteDimensional` is a **core Mathlib namespace**. Declaring an
operator-theoretic construction into it is namespace pollution of the kind Tau
Ceti and Mathlib both reject, and it is inconsistent with every other file in
this group, which use `TauCeti`, `TauCeti.Real`, `OrthonormalBasis`,
`LinearMap.IsPositive` or `ContinuousLinearMap` — all either the project
namespace or the canonical namespace of the object being extended, exactly as
`ForTauCeti/README.md` §2 requires.

Neither justification in that README applies: this is not an extension of
`FiniteDimensional` (the class), and it is not `TauCeti`. It should be
`LinearMap.IsSymmetric.functionalCalculus` or live under `TauCeti`.

## Finding T01-4 — project-management metadata in a source header `{lane:HDR-DEST}`

`PositiveSqrt.lean:9-11`:

> Sub-dev I of the operator polar decomposition project — COMPLETE
> (proof-complete; reduction uses only: `propext, Classical.choice, Quot.sound`).
> Tickets PD-01..PD-04.

"Sub-dev I", "COMPLETE", and ticket IDs `PD-01..PD-04` are internal
project-tracking state. They mean nothing to a Tau Ceti reviewer and will be
wrong the moment the tickets are closed. The axiom list is worth keeping — as a
fact about the file, not as a status claim. Folded into lane `HDR-DEST`.

## Finding T01-5 — three header conventions in nine files `{lane:HDR-DEST}`

Refines the earlier finding with what the group actually shows:

| header form | files |
|---|---|
| `Staged for Mathlib: … Mathlib/…` | `LinearIsometry`, `Basic`, `Spectrum`, `PositiveSqrt` |
| `Staged for **Tau Ceti**: … **`Mathlib/`**…` | `BasisSpan`, `CourantFischer` |
| no staging line at all | `OperatorModulus`, `SelfAdjointFunctionalCalculus`, `Sqrt` |

The middle row is the interesting one: those two files say **Tau Ceti** in the
prose and then name a `Mathlib/` destination path in the same sentence. So the
correction has already been started and left half-done — which is worse than
either consistent state, because a reader cannot tell whether the path or the
project name is the stale half.

## Group verdict

**This group is close to submittable and its problems are structural, not
mathematical.** Nothing here is wrong; two things are shaped wrong (T01-2's
duplicate definition, T01-3's namespace) and the headers disagree with each other
(T01-4, T01-5). The mathematics — Courant–Fischer with the sup-inf equality as
the headline, Weyl at `ContinuousLinearMap` level, the rectangular modulus with
its norm laws derived from one pointwise identity — is the quality the rest of
the library should be measured against.

**One boundary question for the group, which the file pass answers: T01 is
correctly one topic.** The square root, the modulus and the functional calculus
are the same construction at three generalities, and `BasisSpan` /
`CourantFischer` / `Spectrum` are the spectral machinery they all use. Do not
split it.
