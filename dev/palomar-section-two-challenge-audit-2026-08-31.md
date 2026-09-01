# Can the four Section 2 theorems be a Palomar Challenge?

Audited 2026-08-31, against the policy snapshot the submission repository
carries (`submodules/aiq-davis-kahan-1970-rotation-eigenvectgors-perturbation-formalization`,
`scripts/check_palomar_readiness.py`, read from `PalomarSubmission` on
2026-08-28), the pinned Tau Ceti at
`1b39d420ac84ed9a5a7d536ce19b37818ad29c39`, and the Mathlib this workspace pins.

**Answer: no, not without loss of generality, and the blocker is in the
*statement*, not the proof.**  The four theorems can be *stated* over `ℂ` inside
a Challenge; they cannot be stated over `ℝ`, because Mathlib's real continuous
functional calculus for bounded operators does not exist, and the paper states
its results for a real *or* complex space.  A complex-only Challenge would be
exactly the "loss of generality introduced for packaging convenience" the entry
is supposed to avoid.

This document is the audit.  It is **not** a submission surface: the Challenge,
the Solution, the comparator configuration and the submission metadata belong to
the standalone repository, and `AGENTS.md` forbids recreating them here.

## What the policy allows

| rule | value |
| --- | --- |
| Challenge hard cap | 1000 lines / 100 KiB |
| Challenge preferred cap | 300 lines / 32 KiB |
| Challenge import closure | Lean core, allowlisted Mathlib, Tau Ceti, CSLib — **and no module of the submitted repository except the Challenge itself** |
| Challenge-local definitions | permitted; compared through `definition_names` |
| `sorry` in the Challenge | the Comparator convention: the statement side carries the hole, the Solution proves it |
| permitted axioms | `propext`, `Quot.sound`, `Classical.choice` |

So the question is precisely: **can the four printed statements be written from
Lean core + Mathlib + upstream Tau Ceti + compact Challenge-local definitions?**

## The vocabulary each statement needs, and where it is

| concept | production symbol | in Mathlib? | in pinned Tau Ceti? | Challenge-local replacement? |
| --- | --- | --- | --- | --- |
| unbounded operator | `LinearPMap` | **yes** | yes (resolvent/shift additions) | not needed |
| self-adjointness of one | `LinearPMap.IsSelfAdjoint` | **yes** | — | not needed |
| reducing decomposition of the paper's `E₀, F₀, F₁` | `IsTrialResidual`, `IsExactSpectralDecomposition` | no | no | **yes**, ~20 lines: they are equations between bounded maps |
| operator-form semibounds | `LinearPMap.SemiboundedBelow/Above` | no | no | **yes**, 4 lines |
| real spectrum of a `LinearPMap` | `LinearPMap.realSpectrum` | no | no | **yes**, ~8 lines (complement of "has a bounded two-sided inverse") |
| the source separation | `FormBoundedSylvesterGap` | no | no | **yes**, ~12 lines, all three constructors |
| singular / approximation numbers, infinite-dimensional | `ContinuousLinearMap.approximationNumber` | **no** — `LinearMap.singularValues` exists but is defined through `finrank` and is finite-dimensional only | no | **yes**, ~6 lines as `⨅ {‖T − F‖ : rank F < n}` |
| unitarily invariant norm | `PaperUnitaryInvariantNorm` | **no** | **no** | **yes**, ~40 lines as an ideal gauge with the two-sided bound and normalization |
| `sin Θ` over `ℂ` | `paperSinAngleOperatorC` | statable: `cfc` on `E →L[ℂ] E` is available | — | yes, ~15 lines |
| `tan Θ`, `sin 2Θ`, `|tan 2Θ|` over `ℂ` | `paperTanAngleOperatorC`, … | statable, same way | — | yes, ~45 lines |
| the same four angles over `ℝ` | `paperTanAngleOperatorR`, … | **no** | **no** | **no — see below** |
| Ritz pair, reducing complement, condition (3.5) | `UnboundedRitzPair`, `ReducingComplement`, `CrossedDefectsEquivalent` | no | no | yes, ~40 lines |
| reflection intertwiner, odd-for, diagonal part | `ReflectionIntertwines`, `IsOddFor`, `Submodule.diagonalPart` | no | no | yes, ~35 lines |

Adding the four statements themselves (~120 lines), a complex-only Challenge
lands around 350–450 lines: **inside** the 1000-line hard cap, over the 300-line
preferred one.  Size is therefore not the blocker.

## The blocker: the real angle operators cannot be named

Every one of the four angle objects is built from
`ContinuousLinearMap.modulus (P_V − P_U)` and a real continuous functional
calculus on top of it.  In Mathlib that calculus reaches `E →L[𝕜] E` through

```
IsSelfAdjoint.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ A IsSelfAdjoint
```

whose hypothesis is `[ContinuousFunctionalCalculus ℂ A IsStarNormal]`
(`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean`).
`A` therefore has to be a **complex** C⋆-algebra.  For a real Hilbert space `E`,
`E →L[ℝ] E` is a real Banach ⋆-algebra and Mathlib provides no such instance —
Mathlib's own library note records generalization to real C⋆-algebras as a design
goal, not a fact.

This repository reaches the real angles by *complexifying*: `paperSinTwoAngleOperatorR U V`
is `realPartOperator (paperSinTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))`.
That complexification layer — the real-to-complex transport of Hilbert spaces,
bounded and partial operators, subspaces, spectral projections and approximation
numbers — is thousands of lines of `ForTauCeti` and `DavisKahan`.  It cannot be
imported (the import rule forbids it) and cannot be inlined (the cap forbids it,
and inlining it would put the whole transport inside the trusted statement
surface, which is what a Challenge exists to prevent).

**Consequence.**  A policy-valid Challenge for the four Section 2 theorems is
complex-only.  The paper states its results for a real *or* complex space, so
that is a loss of generality, and this audit does not recommend it.

## The second, softer objection: what a Challenge-local norm class would mean

Even over `ℂ`, the Challenge would have to *define* the unitarily invariant norm
and the four angle operators, because neither Mathlib nor upstream Tau Ceti has
them.  A Challenge's definitions are its trusted surface.  A compact re-definition
of "unitarily invariant norm" is easy to get subtly wrong in the weakening
direction, and a reviewer would then be checking the repository's fidelity claim
against a definition written for the occasion rather than against Mathlib.

That is the same objection the standalone entry already records for its current
scope, and it is the reason its Challenge compares the operator-norm `sin Θ`
theorem — a statement writable in ordinary Mathlib vocabulary — rather than the
general ones.

## What would unblock it

In descending order of leverage:

1. **A real continuous functional calculus for `E →L[ℝ] E`**, or Mathlib's
   generalization of the C⋆ calculus to real C⋆-algebras.  This alone turns the
   four statements from complex-only into real-and-complex.
2. **Infinite-dimensional approximation numbers in Mathlib**, generalizing
   `LinearMap.singularValues` off `finrank`.
3. **A unitarily invariant norm / symmetric gauge class upstream** — the natural
   Tau Ceti contribution, and the one this repository is already positioned to
   make: `ForTauCeti` carries the class, the Fan dominance theorem, and the
   approximation-number theory it rests on.

(3) is the item this repository can act on, and it is already the Tau Ceti track.
Until at least (1) and (3) exist upstream, the four Section 2 theorems are not a
Challenge; the operator-norm `sin Θ` theorem the standalone entry compares is.

## Standing constraint

Nothing here is a submission.  Nothing has been submitted to or registered with
Palomar.
