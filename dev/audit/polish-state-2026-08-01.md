# Where the polish campaign stands, 2026-08-01

Written because the lane board now carries the detail across a dozen rows and nobody
arriving fresh should have to reconstruct the picture from them.  Everything below was
measured, not estimated; the commands are given so it can be re-measured rather than
trusted.

## The tree

`lake build` EXIT=0 at **9277 jobs**.  `DavisKahan` carries **22 warnings** and that number
is a baseline worth watching — see the trap list.  `ForTauCeti` is built with
`warningAsError`, so it has none by construction.

`python3 scripts/run_gates.py` — **1 of 31 fails**: `check_full_part_iii_math_ahead`, on
**37 `sorry`s, every one in `DavisKahan/Experimental/`**.  That is open research, not
polish, and it has been the suite's only failure throughout.

## What is exhausted

**Inline duplication in `ForTauCeti` is done, from both directions.**  Cross-file and
same-file scans at a **4-line** floor both return zero real groups (one thin false
positive, `Function.Injective f` over unrelated maps).  Body-similarity clustering at 10+
lines returns three pairs, all classified as parallel accounts or as residue of extractions
already made.

**`rw` chains of ≥ 7 named lemmas: `ForTauCeti` 53 → 3, `DavisKahan` 84 → 17.**  Every one
of the 20 survivors carries, in-source, the diagnostic the compiler actually produced when
`simp only` was tried on it.  Nobody needs to retry them to find out why.

**The Real/Complex parallelism is load-bearing and should not be unified.**  Eight parallel
module pairs, 1627 lines on the Real side.  In three of the five substantive pairs the Real
side is *smaller* — it is already delegating.  In the two where it is larger, the excess is
machinery the complex side does not need: `SpectralOrder/Real` because Mathlib has no
`StarOrderedRing (E →L[ℝ] E)`, and `Real/SpectralRestriction` because 25 of its 37
declarations are a complexification bridge.  The one genuine exception was an unfactored
derivation in `Theorem62`'s Real section, and it is fixed.

## What is open, and what kind of thing it is

| lane | kind | first step |
|---|---|---|
| `FTC-SYMGAUGE-COLLIDE` | **decision, then a proof** | disambiguate one namespace, then prove the two `extend`s agree |
| `FTC-DOUBLED-UNIFY` (`horbit`) | **public-API decision** | confirm whether the real theorem is dead; its predicate is not |
| `DK-BODYDUP` | two small targets left | `ShortRotationCounterexample` `hle`/`hle'` |
| `EXP-BUILD-ADJ`, `FTT-PROMOTE` | **blocked on Mathlib** | nothing actionable here |
| 14 `DavisKahan` proofs over 150 lines | judgement | the extraction filter is empty on them; read structure instead |

## The instruments, and what each cannot see

* `scripts/check_rw_chains.py` — the chain count.  **Do not re-derive this with a regex**;
  it was wrong twice that way, both times by counting commas inside a `by` block.
* `scripts/check_duplicate_qualified_names.py` — one fully-qualified name from two modules.
  Ratcheted at 14, all of them the single unresolved `SymmetricGauge` collision.
* `scripts/check_inline_duplicates.py` — groups by **statement**.  It cannot pair a fact
  proved once over `Set.Ici c` and once over `Set.Iic c`; body-token clustering can, and
  that is how two real `ForTauCeti` duplicates were found.
* `scripts/proof_length_census.py` — same-name proofs with a large length delta is a
  genuinely productive signal.  It found the `Theorem62` asymmetry.  It also produces false
  leads: a 79-line gap turned out to be a Mathlib instance that does not exist.

## Traps that cost real time here

1. **`run_gates.py` is the authority on how a gate runs.**  Not whether it accepts
   `--check`.  Three separate mis-verifications came from guessing: a `||` fallback that
   masked failures, `--check` passed to advisory gates producing invented failures, and
   `--check` passed to a gate that has no such flag (argparse exit 2, not a failure).
2. **`DavisKahan` is not `warningAsError`.**  A redundant `simp only` argument lands as a
   silent warning there.  Check the count, not just the exit code.
3. **Never insert between a docstring and its declaration.**  It fails at the *next*
   declaration, far from the edit.  This happened twice.
4. **Anchor lane-board edits on a row heading**, not on a substring that can occur in
   another row's prose.  Also happened twice; once it produced a commit whose message
   claimed work the commit did not contain.
5. **Aliasing leaves dead private definitions behind** and nothing warns.  Grep the
   occurrence count afterwards.
6. **A size threshold selects against shared algebra.**  Facts proved in three places are
   usually short enough to retype; the 4-line floor is what found them.
