# Repo-wide duplicate scan — what is left, and what should not be touched

`scripts/check_inline_duplicates.py` now covers **eight production libraries**
instead of two.  This note records what the first repo-wide scan found, so that
the next person starts from the list rather than from the tool.

Run it as:

    python3 scripts/check_inline_duplicates.py --only repeated --min-body 4 --why

## The headline correction

**The library list was hardcoded to `ForTauCeti` and `DavisKahan`.**  Seven other
declared libraries — 136 files — were never scanned and nothing in the output
said so.  That is the same defect `run_gates.py` exists to prevent, in a script
written the same day by the same author.  It is now derived from
`lakefile.toml`, with `ForTauCetiRoadmap` (all `sorry`) and `Challenge`
(calibration comparators) excluded for stated reasons, and a test that fails if
the two-library list returns.

**A second, subtler restriction was mine, not the tool's.**  While sweeping
`DavisKahan` I filtered to the proofs over 150 body lines, because that was the
long-proof campaign's list.  Duplicates do not live only in long proofs.  The
repo-wide scan at `--min-body 4` reports **65 non-thin repeated groups**, and the
largest are in files I had already "finished".

## Four categories, and only one is work

Every `repeated` group falls into one of these.  Classifying costs a minute and
saves an hour.

**(1) A real duplicate.**  Same statement, same proof, factors out.  This is the
actionable case and roughly twenty of this session's extractions were it.

**(2) Shared local naming over different objects.**  Two proofs each write
`let P := …` for *different* operators, so the statement text matches and the
statement does not.  `hSP`/`hCosP` in `DirectRotationSquare.lean` — one `P` is
`projection U`, the other `complementaryProjection U`.  **Read the `let`/`set`
bindings at both sites before extracting.**

**(3) A statement with no content.**  `Function.Injective f` matched two
completely unrelated proofs in `GramSpectralRank` and `FinitePVMSelection`.  The
report marks these `(thin: content 1)`.  The mark means the tool has no opinion —
`CauchySeq (fun n => (a n).val)` is equally thin and *was* a genuine four-way
duplicate.

**(4) Deliberately parallel accounts.**  Same statement, *different proofs*, kept
on purpose.  **This is the category that must not be collapsed**, and the two
instances found are both documented as intentional by their own authors.

## The two parallel accounts — do not collapse without a decision

**`tan_theta_le` / `tan_theta_le'`.**  `DavisKahan/FiniteDimensional/TanTheta/Vector.lean`
and `DavisKahan/TanTheta/Vector.lean` state the *same theorem with
character-identical signatures*, and their `hkey` steps are 101 lines each with a
201-line diff — they share nothing.  The finite proof evaluates the key
inequality at a maximizer on the compact unit sphere of `Vᗮ`; the general proof
has no compact sphere and replaces the maximizer with an operator norm and an
approximate-supremum limit.

`tan_theta_le'` is strictly more general — it drops `[FiniteDimensional 𝕜 E]` —
and the general file imports only `ForTauCeti` and `Mathlib`, so the finite file
*could* import it and shrink by about 117 lines.  **It should not, without a
decision.**  The general file's own module docstring compares the two proofs at
length, and `Alternative/FiniteDimensional/API/ClassicalProseLike.lean` consumes
the finite one, which reads as a deliberate elementary account kept beside the
general one.  Deleting the classical argument changes what the finite-dimensional
development claims to be.

**The residual-witness pair**, `orthonormal_tanThetaResidualWitness` and
`orthonormal_theorem63ResidualWitness`, is the same situation over different
types (`LinearMap`/`𝕜` against `ContinuousLinearMap`/`ℂ`) and was posted
separately as `{lane:TANTHETA-WITNESS-UNIFY}`.  **No textual check will ever pair
those two** — a cross-file scan returns exactly one match, `0 < c`, which is
noise.  The duplication is real and invisible to tooling, which is the argument
for deciding it deliberately rather than waiting for a scan to raise it.

## Known-blocked

The negation-tendsto fact shared by
`ForTauCeti/Analysis/InnerProductSpace/OneParameterUnitaryGroup/Basic.lean` and
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Generator.lean` is duplicated
verbatim and **has no common `ForTauCeti` ancestor** — the two import closures are
disjoint.  Giving it a home means a new module, and `ForTauCeti`'s
module-to-topic partition is total, so a new module needs a roadmap topic.  That
is `{lane:TAUCETI-ROADMAP-SUBMISSION}`'s call.  `ringInverse_semiconj` hit the
same wall and was parked in `CoerciveUnit.lean`, which has a good but imperfect
claim to it.

## Where the sweep got to

**Identical-body groups: 32 → 14; duplicated volume 248 → 70 lines.**  Eighteen
extractions, every one confirmed byte-identical across its sites before any edit,
each verified by a full `lake build` (9274 jobs) and pushed separately.

**The 33 differing-body groups (493 lines) were not touched and mostly should not
be.**  They are category (2) and (4): the `tan_theta_le` finite/general/unbounded
triple alone is 211 lines of deliberate parallel accounts, and `DkpsQuench2026`'s
augmented-CMDS pair carries an in-source comment saying a cleanup-only refactor
is *deferred* on purpose.

### A fifth category: blocked by instance availability

A genuine duplicate can resist extraction for a reason that is neither
mathematical nor editorial.  `hsq2` in `Geometry/Angle/OperatorAngleComplex.lean`
states a fact about `Uᗮ.starProjection`, so a standalone lemma needs
`Uᗮ.HasOrthogonalProjection`; inline, that instance is already elaborated from
the enclosing theorem's statement, but extracted, the second call site can only
reach it through `CompleteSpace E`, which that theorem does not have.

**The test is whether the call sites can supply what the standalone statement
demands, not whether the statement demands more.**
`subspaceGap_eq_max_directedGap` needed exactly the same extra `CompleteSpace E`
and went through, because both of *its* callers have one.

### What the remaining five look like — and two diagnoses I got wrong

**Identical-body groups are down to 5 (about 25 lines).**  Every one has a
checked reason, and each is a *decision* rather than a mechanical edit.

**Two entries earlier in this note were wrong, and the error was the same both
times: I compared a hypothesis at one site against a different hypothesis at the
other.**

* `RosenblumExistence:hAs` — I wrote that the two sites prove the same statement
  from an open-ball and a closed-ball hypothesis.  They do not; I had compared
  `hA` at one site with `hB` at the other.  Both carry the identical `hA`, and
  the extraction went through.
* `SinTheta/Unbounded:hA₀sym` — I wrote that the two theorems spell
  self-adjointness differently.  Each *file* contains both spellings, but the two
  duplicate sites use the same one.  Extracted.

**The lesson is narrow and worth stating**: when a group looks blocked by
mismatched hypotheses, check that the two things being compared are the two
things the duplicate sites actually use.

The five that remain:

* `Section3Nonacute:hrange` — the copies sit in branches that each bind their own
  `x`, so a `∀`-quantified hoist does not typecheck at the second site without
  restructuring both branches.
* `OperatorAngleComplex:hsq2` — **the only one blocked by elaboration.**  See the
  instance-availability section above.
* `OneParameterUnitaryGroup`/`Sylvester.Generator:hneg` — no common `ForTauCeti`
  ancestor; a new module needs a roadmap topic, which is
  `{lane:TAUCETI-ROADMAP-SUBMISSION}`'s call.
* `OrderedCutoff`/`OrderedFromCutoffs:hpoint` — the natural home is in
  `ForTauCeti`'s approximation-number layer, so it is a cross-library placement
  decision rather than a move.
* `QueryEfficiency` `Finite`/`Infinite:hlipschitz` — the two files share no import
  edge.

## Largest groups still open at the time of writing

| lines × sites | where | category |
|---|---|---|
| 101 × 2 | `tan_theta_le` / `tan_theta_le'` | (4) — do not collapse |
| 54 × 2 | `TanTheta/UnboundedVector.lean`, `TanTheta/Vector.lean` | unclassified |
| 40 × 2 | `PrincipalPlanes/Spectrum.lean`, `.../Variational.lean` | unclassified |
| 32 × 3 | three `TanTheta` vector files | unclassified |
| 28 × 2 | `DkpsQuench2026` geometry / query-efficiency | unclassified |
| 19 × 3 | two `PrincipalPlanes` files + `ForTauCeti` block sum | unclassified |

"Unclassified" means nobody has yet read both sites to decide which of the four
categories it is.  That reading is the work, and it is cheap; the extraction is
the easy part.
