# Palomar Registry submission surfaces

**Preparation only. Nothing here claims registration, approval, acceptance, or
peer review by the Palomar Registry.** The execution contract is
[`../dev/palomar-readiness.md`](../dev/palomar-readiness.md).

**Why this directory is `registry/` and not `palomar/`.** It was `palomar/` until
2026-08-29, alongside the Lean library directory `Palomar/`. Two paths differing
only in case are the same path on a case-insensitive filesystem — Windows, and
macOS by default — so a checkout there could conflate them, refuse operations, or
simply differ from what Linux sees. A formalization advertised as independently
reproducible must not have a layout that is ambiguous on a common platform. The
names now differ structurally, and the split is conceptual rather than
capitalisation-based: `Palomar/` is Lean source, `registry/` is submission
configuration and metadata. Palomar selects the Comparator and metadata paths
explicitly, so neither has to live in a directory named after it.

This directory holds one subdirectory per prepared entry. The Lean sources live
under [`../Palomar/`](../Palomar) so they build and can be verified in place; the
configuration, per-entry metadata and extraction skeleton live here.

## Prepared entries

| entry | source result | compared declarations | source relationship | status |
| --- | --- | --- | --- | --- |
| `yws-symmetric` | Yu–Wang–Samworth 2015, Theorem 2 (both conclusions) and Corollary 1 (both displays) | `YWSPalomar.theorem2_sinTheta`, `…theorem2_alignedFrame`, `…corollary1_sinTheta`, `…corollary1_alignedVector` | `formalizes` | Comparator PASS; **source-faithful** — Theorem 2 exact, Corollary 1 with one inherited hypothesis written out, see below |
| `yws-rectangular` | Yu–Wang–Samworth 2015, Theorem 3, right and left, sine and aligned, plus the two singular-frame equivalences | `YWSRectangular.theorem3_rightSinTheta`, `…rightAlignedFrame`, `…leftSinTheta`, `…leftAlignedFrame`, `…isRightSingularBlock_iff_pairedSingularVectors`, `…isLeftSingularBlock_iff_pairedSingularVectors` | `adapts` | Comparator PASS; **source-corrected**, see below |
| `yws-2015` | Yu–Wang–Samworth 2015, Theorem 2, first conclusion, in a general index-set form | `YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap` | — | Comparator PASS; **prototype/regression**, superseded by `yws-symmetric` |
| `dk-1970` | Davis–Kahan 1970, operator-norm sin-Θ | `TauCeti.norm_starProjection_comp_starProjection_le` | — | Comparator PASS; extracted 2026-08-29 |

**The two Yu–Wang–Samworth entries carry their own metadata**, at
`yws-symmetric/formalization.yaml` and `yws-rectangular/formalization.yaml`,
because their relationships to the source differ and one `formalization.yaml`
records one relationship per source. A Palomar submission selects its metadata
path explicitly alongside its Comparator path.

**`yws-symmetric` is the preferred Yu–Wang–Samworth entry.** `yws-2015` compares a
statement in a convenient shape — an arbitrary `Finset` rather than the source's
contiguous `r…s` block, canonical eigenbases rather than arbitrary supplied
frames, no aligned conclusion, and no visible source denominator. It proved the
Palomar mechanics work and is kept as a regression, not as a paper-facing claim.

**`yws-rectangular` compares the corrected Theorem 3, not the printed one.** The
paper's convention `σ²_{rank(A)+1} := −∞` is false: it makes the denominator
infinite at `s = rank(A)`, so the printed bound asserts that two singular
subspaces which can be orthogonal coincide. The entry's Challenge docstring states
this, exhibits the counterexample, and says what is proved instead. Its metadata
says `relationship: adapts` and must not describe it as exact.

Two things that are *not* changed there, and are easy to conflate with the
correction. The paper's own block restriction `1 ≤ r ≤ s ≤ rank(A)` is retained,
as `s < finrank ℝ (range A)`; the lower-level theorems in the development drop it,
which is a valid generalization, but the entry compares at the paper's scope. And
`Δ` is the paper's exact denominator, identified by `SourceSingularGap`, not an
arbitrary positive lower bound.

**`yws-symmetric` is source-faithful, and "exact" is the wrong word for it as a
whole.** Theorem 2's two conclusions are the printed statements with nothing
added or weakened. Corollary 1's two declarations assume `‖v‖ = ‖v̂‖ = 1`, and the
*standalone* printed display does not say that — it says only that `v` and `v̂`
satisfy the two eigenvector equations. Unit vectors are unambiguously meant, since
the paper introduces the corollary as the `d = 1` case of Theorem 2, whose frames
have orthonormal columns; but the omission is not harmless, because the second
printed display is **false** without it. Scaling `v̂` preserves every printed
hypothesis while `‖v̂ − v‖` does not, so `Σ̂ = Σ`, `v̂ = 2v` gives a zero
perturbation against a nonzero distance.
`YuWangSamworth2015.corollary1_printed_unnormalized_counterexample` is the
machine-checked refutation. The source relationship stays `formalizes` — a
hypothesis the paper supplies one sentence earlier is written out, not a result
changed — but no claim of "exactly as printed" or "no added hypothesis" is made
for Corollary 1.

**Theorem 1 and Appendix Lemma A1 are not selected.** Both are formalized in the
development. Theorem 1 is held back because the endpoint conventions its printed
separation uses make it vacuous at any block touching either end of the spectrum;
the published article was re-read on 2026-08-29 and prints them that way, so
selecting Theorem 1 would mean a third `adapts` entry with its own disclosed
correction. See [`YWS_SOURCE_CONTRACT.md`](YWS_SOURCE_CONTRACT.md) row T1. It is
not held back by size.

The clause-by-clause basis for every selection above is
[`YWS_SOURCE_CONTRACT.md`](YWS_SOURCE_CONTRACT.md).

Each entry's Lean sources are `Palomar/<Name>/{Challenge,Solution}.lean`.

Status words mean what they say. *Comparator PASS* means the real Comparator ran:
statements exported with `lean4export` and compared, the independent NanoDa kernel
accepting the solution, and Lean's own kernel accepting it. Alongside that, each
Challenge's transitive import closure reaches nothing in this repository, and each
compared declaration's axiom closure is exactly `propext`, `Quot.sound`,
`Classical.choice`.

`definition_names` is empty in both Yu–Wang–Samworth configurations, and that is
deliberate. Comparator treats a listed name as a *definition hole*: it checks the
name, type, universe levels and safety level, and stops comparing the definition's
value. Every helper definition in these Challenges is fully specified, so listing
them weakened the comparison; with the lists removed Comparator requires the
Challenge and Solution copies to agree as whole constants, bodies included.

It does **not** mean Palomar has seen these, and it is not acceptance. Palomar runs
its own verification and an editorial review, and registration is a maintainer
decision. Setup notes for reproducing the Comparator run — including the toolchain
pin that must match, or the exporter fails on our oleans — are in
[`../dev/palomar-readiness.md`](../dev/palomar-readiness.md) §6.4.

## How an entry is built

A Palomar Challenge may import only Lean core and the allowlisted Mathlib and Tau
Ceti closure. It may not import `ForTauCeti`, `DavisKahan`, or any paper package
in this repository. So each entry states its theorem against Mathlib alone, with a
deliberate statement-side hole, and the Solution supplies the same declaration name
from the ordinary development. Comparator checks that the two agree on name and
type and that the proof uses only the permitted axioms.

The internal [`../Challenge/`](../Challenge) tree is a different thing — a
calibration and regression surface, with modules that deliberately import local
libraries. It is not a Palomar submission surface and must not be used as one.

## Verifying locally

```bash
lake build Palomar
python3 scripts/check_palomar_readiness.py --with-axioms
scripts/verify_palomar.sh                   # every entry, all four stages
scripts/verify_palomar.sh dk-1970           # one entry
```

## Submitting

An agent must not submit. Registration is permanent and the maintainer reviews the
prepared commit first; the human-review checklist is in the contract.

Each entry is submitted from its own standalone repository. Those repositories are
**extractions, not thin wrappers**: since 2026-08-29 each one contains the package
directories its entry needs, copied verbatim, and builds them itself, so it is a
substantive development in Palomar's sense and carries no `repository` key in its
metadata. `Challenge.lean` and `Solution.lean` are byte-identical in both contexts
— an `import` resolves the same way whether the library is local or arrives as a
Lake dependency — so extraction is a copy. The skeletons under `<entry>/wrapper/`
survive only as the metadata and comparator-config source the extraction copies
from; they no longer describe the submitted repository's shape. See
[`../dev/palomar-readiness.md`](../dev/palomar-readiness.md) §5.0.
