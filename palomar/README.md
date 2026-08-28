# Palomar Registry submission surfaces

**Preparation only. Nothing here claims registration, approval, acceptance, or
peer review by the Palomar Registry.** The execution contract is
[`../dev/palomar-readiness.md`](../dev/palomar-readiness.md).

This directory holds one subdirectory per prepared entry. The Lean sources live
under [`../Palomar/`](../Palomar) so they build and can be verified in place; the
configuration, metadata and wrapper skeleton live here.

## Prepared entries

| entry | Challenge | Solution | compared theorem | status |
| --- | --- | --- | --- | --- |
| `yws-2015` | `Palomar/YuWangSamworth2015/Challenge.lean` | `Palomar/YuWangSamworth2015/Solution.lean` | `YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap` | locally verified |

Status words mean what they say. *Locally verified* means the Challenge builds,
the Solution supplies the compared declaration with a matching type, and its axiom
closure is exactly `propext`, `Quot.sound`, `Classical.choice`. It does not mean
Palomar has seen it.

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
python3 scripts/check_comparator_signatures.py --no-build palomar/yws-2015/comparator.json
python3 scripts/check_palomar_readiness.py
scripts/verify_palomar.sh yws-2015          # real Comparator + NanoDa
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
