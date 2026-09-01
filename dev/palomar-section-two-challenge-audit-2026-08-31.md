# Can the four Section 2 theorems be a Palomar Challenge?

Audited 2026-08-31, against the policy snapshot the submission repository
carries (`submodules/aiq-davis-kahan-1970-rotation-eigenvectgors-perturbation-formalization`,
`scripts/check_palomar_readiness.py`, read from `PalomarSubmission` on
2026-08-28), the pinned Tau Ceti at
`1b39d420ac84ed9a5a7d536ce19b37818ad29c39`, and the Mathlib this workspace pins.

**Answer: RETRACTED.  The candidate has now been built, and it works.**

This audit originally concluded that a four-theorem Challenge was blocked -- first
because the real angle operators could not be named, then, after that was
corrected, because the needed vocabulary lives in `ForTauCeti` rather than
upstream.  **Both conclusions were wrong, and the second did not follow from
Palomar's policy at all**: Palomar permits Challenge-local definitions, and
provides `definition_names` precisely so a Challenge may name a definition whose
value the Solution supplies.  Inferring a blockage from where the *development's*
definitions live was a category error.

The candidate is `dev/palomar-candidate/`.  It compiles, against `import Mathlib`
alone, at **684 lines / 32,765 bytes** -- inside the 1000-line / 100 KiB hard cap
and, after a statement-repair pass, inside the preferred 32 KiB as well -- with
four `[RCLike 𝕜]` headline theorems and **no functional calculus anywhere**.
`Solution.lean` proves the `sin Θ` statement and the ambient clause of `sin 2Θ`
from the development, and proves that the Challenge's unitarily invariant norm is
the development's `PaperUnitaryInvariantNorm` **by `rfl`**.

**The first draft's statements were not the paper's, in four ways**, and a proof
of an inaccurate Challenge would have been worse than an unfinished accurate one.
`dev/palomar-section-two-challenge-statement-audit.md` is the clause-by-clause
audit that found and fixed them, and is now the maintained record of what each
Challenge clause claims and what its correspondence still owes.

What remains is named there and in `dev/palomar-candidate/README.md`; the
headline item is a scalar-field transport that would discharge two development
capability classes at once.  None of it is a Palomar policy obstruction.

The rest of this file is retained as the record of what the vocabulary needs and
where each object currently lives, which is still accurate and still useful.  Its
earlier verdict is not.

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

## Where each needed object currently lives

The table below is a map of the *development's* dependencies, not an argument
about feasibility -- the candidate shows the Challenge does not need to import
any of it.  The last four rows are the ones the earlier verdict leaned on, and
the candidate defines all four from Mathlib primitives instead.

| concept | Mathlib | upstream Tau Ceti (pinned) | Tau Ceti operator roadmap | `ForTauCeti` |
| --- | --- | --- | --- | --- |
| infinite-dimensional approximation numbers | no (`LinearMap.singularValues` is `finrank`-based) | no | **yes** — `OI-A01`, `OI-A06` | yes |
| Ky Fan gauge and Fan dominance | no | no | **yes** — `OI-B74`, `OI-B75` | yes |
| operator ideal families | no | no | **yes** — `OperatorIdeals` | yes |
| symmetric gauge, i.e. the paper's UI norm class | no | no | **yes** — `OI-B56`, `OI-B59`, `OI-B64`–`OI-B71` | yes |
| `modulus`, positive square root, polar factors | `ℂ` only | no | **yes** — `PD-A36`, `RCLike`-generic | yes |
| ambient `sin Θ` / `cos Θ` angle operators | no | no | **yes** — `PA-B10`, `PA-B11` | yes |
| directed `sin 2Θ` block | no | no | **yes** — `PA-B09` | yes |
| `LinearPMap` resolvent set and resolvent | no | partial | **yes** — `SelfAdjointSpectralTheory` | yes |
| spectral PVM of an unbounded self-adjoint operator | no | no | **yes, over `ℂ`** — `SA-E01` | yes |
| Sylvester equation, `MapsDomainTo`, `perturb` | no | no | **yes** | yes |
| real continuous functional calculus for `E →L[ℝ] E` | **no** | no | **no — proposed, not yet on it** | **yes** |
| spectral *subspace* and reducing restriction of an unbounded operator | no | no | **no** | yes |
| `FormBoundedSylvesterGap` (three-constructor, over `LinearPMap` semibounds) | no | no | **no** | yes |
| ambient `tan Θ` and `tan 2Θ` **operators** | no | no | **no** (roadmap has tangents as finite-dimensional singular-value sequences, `PA-B15`) | yes |

So the Challenge is blocked on the last four rows, and on the first eleven only
until the roadmap topics land.

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

## What would unblock the *upstreaming* route

Separately from the Challenge, which does not need it, these are the items this
repository could propose upstream, in dependency order.  They matter for the Tau
Ceti track, not for Palomar:

1. **Land the `OperatorIdeals` and `PolarDecomposition` roadmap topics.**  They
   carry the approximation numbers, the symmetric gauge, Fan dominance and the
   modulus.
2. **Propose the real continuous functional calculus.**  It is written, it is
   self-contained, and its own module docstring already says it is proposed for
   the roadmap.
3. **Propose the unbounded spectral subspace and reducing restriction**, and the
   form-bounded gap predicate.

## Standing constraint

Nothing here is a submission.  Nothing has been submitted to or registered with
Palomar.
