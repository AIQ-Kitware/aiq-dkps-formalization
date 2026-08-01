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

**(5) The same proof over differently-*named* variables.**  Discovered late, by
which point 493 lines had been shelved as category (4) on the strength of
"different bodies".  Two groups were really this, including **the largest single
duplicate in the repository**: fifty-five lines written twice, differing only in
whether the Hilbert space was called `E` or `H` and whether the strip half-width
appeared as `(β - α) / 2` or under its own name.

Blank single-capital identifiers and compare with a similarity ratio before
concluding that two bodies differ:

    a = [re.sub(r"\b[A-Z]\b", "·", l) for l in normalised_body_of_site_1]
    difflib.SequenceMatcher(None, a, b).ratio() > 0.75

Running that over all 33 differing groups took seconds and returned exactly the
two.  **"Different text" is not "different proof"**, and the raw-text comparison
that separates category (1) cannot see the difference.

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

### Result: zero identical-body groups remain

**Identical-body duplication across eight production libraries went from 32
groups / 248 lines to none.**  Thirty-two extractions or collapses, each
confirmed byte-identical across its sites before any edit, each verified by a
full `lake build` at 9274 jobs.

**Every entry this note once called "blocked" turned out not to be**, and the
reasons are worth keeping because they are about how to look, not about the code:

* **Comparing the wrong pair** (twice).  `RosenblumExistence` — I compared `hA`
  at one site with `hB` at the other.  `SinTheta/Unbounded` — each *file* holds
  two spellings of self-adjointness; both duplicate sites use the same one.
* **The wrong shape.**  `Section3Nonacute:hrange` failed as a `∀`-hoist because
  the branches bind their own `x`; a lemma *taking* `x` needs no hoisting.
* **Structure instead of statement.**  `hlipschitz`'s sites sit under different
  assumption structures; a lemma over the *field's statement* covers both.
* **Assuming a distant home.**  `hpoint` needed no cross-library move —
  `OperatorIdeal/ApproximationNumbers/ScalarGeneric` is an internal common
  ancestor at the right generality.
* **Indentation drift** (twice) — matching both indentations is a two-pattern
  replace.
* **An inherited instance the caller had dropped.**  `hsq2` failed with "failed
  to synthesize `CompleteSpace E`" *at the call site*, which reads like the
  caller lacking something.  It was the opposite: the section supplies
  `CompleteSpace E`, the calling theorem declares `omit [CompleteSpace E] in`,
  and my lemma inherited what the caller had deliberately given up.  **When a
  call site cannot synthesize a section instance, check whether it omits it.**
* **Assuming dedup means extraction.**  `hneg`'s two files are in different
  roadmap topics with disjoint import closures, so a shared lemma really would
  have needed a new module and `jon`'s decision.  The four-line proof collapses
  to one line instead, and a one-line duplicate is not worth extracting.
  Shortening both copies is the other way to remove a duplicate, and it needs no
  placement decision.  The same move cleared `UnboundedIdeal`, whose `calc`
  opened with a step that was `rfl`.

**What remains is the 33 differing-body groups**, and the sections above say why
they should not be collapsed: deliberate parallel accounts, shared local naming
over different objects, and thin statements the tool has no opinion about.

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
