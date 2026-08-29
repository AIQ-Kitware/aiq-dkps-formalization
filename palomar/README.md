# Palomar Registry submission surfaces

**Preparation only. Nothing here claims registration, approval, acceptance, or
peer review by the Palomar Registry.** The execution contract is
[`../dev/palomar-readiness.md`](../dev/palomar-readiness.md).

This directory holds one subdirectory per prepared entry. The Lean sources live
under [`../Palomar/`](../Palomar) so they build and can be verified in place; the
configuration, metadata and wrapper skeleton live here.

## Prepared entries

| entry | source result | compared theorem | status |
| --- | --- | --- | --- |
| `yws-2015` | Yu–Wang–Samworth 2015, Theorem 2, first conclusion | `YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap` | Comparator PASS; extracted 2026-08-29 |
| `dk-1970` | Davis–Kahan 1970, operator-norm sin-Θ | `TauCeti.norm_starProjection_comp_starProjection_le` | Comparator PASS; extracted 2026-08-29 |

Each entry's Lean sources are `Palomar/<Name>/{Challenge,Solution}.lean`.

Status words mean what they say. *Comparator PASS* means the real Comparator ran:
statements exported with `lean4export` and compared, the independent NanoDa kernel
accepting the solution, and Lean's own kernel accepting it. Alongside that, each
Challenge's transitive import closure reaches nothing in this repository, and each
compared declaration's axiom closure is exactly `propext`, `Quot.sound`,
`Classical.choice`.

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

Each entry is submitted as its own standalone repository, a Palomar **thin
wrapper** that pins this repository as the substantive formalization. The skeleton
is in `<entry>/wrapper/`; extraction is a copy, because `Challenge.lean` and
`Solution.lean` are byte-identical in both contexts — an `import` resolves the
same way whether the library is local or arrives as a Lake dependency. Only the
lakefile and the module names in `comparator.json` differ.
