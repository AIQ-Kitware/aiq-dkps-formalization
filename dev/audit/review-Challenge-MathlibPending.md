# Review — `Challenge/MathlibPending`

**Status: IN PROGRESS.** Started 2026-07-29 by `edward (aiq-gpu)`, lane `AUDIT`.
The finding below is complete and verified; the remaining files in the group are
not yet line-read.

Reviewed:

- [x] `Challenge/MathlibPending/DavisKahanPartIII/Conformance.lean`
- [x] `Challenge/MathlibPending/DavisKahanSinTheta/Conformance.lean`
- [x] `Challenge/MathlibPending/DavisKahanSinTwoTheta/Conformance.lean`
- [x] `Challenge/MathlibPending/DavisKahanTanTheta/Conformance.lean`
- [x] `Challenge/MathlibPending/DavisKahanTanTwoTheta/Conformance.lean`

## Finding CH-1 — one challenge is the union of four others `{lane:CH-DEDUP}`

**`DavisKahanPartIII` pins exactly the four theorems that the four dedicated
Davis–Kahan challenges pin, and nothing else.** Verified from both sides — the
`Conformance.lean` statements and the `comparator/*.json` `theorem_names`:

| theorem | pinned by |
|---|---|
| `TauCeti.DavisKahanTheory.partIII_sinTheta_uiNorm` | `pending-davis-kahan-part-iii`, `pending-davis-kahan-sin-theta` |
| `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm` | `pending-davis-kahan-part-iii`, `pending-davis-kahan-sin-two-theta` |
| `TauCeti.DavisKahanTheory.partIII_tanTheta_vector` | `pending-davis-kahan-part-iii`, `pending-davis-kahan-tan-theta` |
| `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm` | `pending-davis-kahan-part-iii`, `pending-davis-kahan-tan-two-theta` |

So the repository maintains **5 challenge directories, 10 files and 5 comparator
configs to pin 4 theorems.** Across all 23 configs, 32 distinct theorems are
pinned and **4 of them are pinned twice** — every one of those four is this
overlap.

**Why this is a defect and not just redundancy.**

1. `AGENTS.md` sets a deliberately high admission bar and says outright:
   *"Prefer one strong leaf over a long inventory of supporting declarations."*
   Five entries for four theorems is the inventory shape that rule forbids.
2. **A rename now breaks two configs instead of one.** `Challenge` is outside
   `defaultTargets` and `comparator/*.json` stores names as plain strings, which
   is the drift trap this repository has already been bitten by twice. Doubling
   the number of places a name is asserted doubles the exposure for no gain.
3. The comparator **runs the same proof twice**, so the leaderboard reports a
   result that is not four independent achievements.

**The decision is which unit is the challenge, and it is not COORD's to make.**
Two defensible answers:

- **The four are the units.** Each is a recognizable literature endpoint — the
  sin Θ, sin 2Θ, tan Θ and tan 2Θ theorems — which is exactly what the
  admission bar asks for. Then `DavisKahanPartIII` is redundant and should go.
- **Part III is the unit.** The four together are the paper's headline package,
  and a single challenge for "Davis–Kahan Part III" is the stronger leaf. Then
  the four dedicated directories are the inventory and should go.

I lean to the **first**: the four are individually citable, individually
recognizable, and a reviewer can attempt one without the others. But it is jon's
call, and either answer removes the duplication.

## What is good

The conformance files themselves are correct in form — statements only,
placeholders intact, one theorem per dedicated challenge. The immutability rule
is being respected. Nothing here suggests anyone filled a placeholder.

## Method note

This finding came from `scripts/audit_scan.py --dup`, which normalizes theorem
statements and hashes them to find collisions across files. It surfaced in
seconds what a sequential read of 49 files would have found only at the end, and
only if the reader still remembered file 3 when reaching file 47. **That is the
argument for running the detectors before the reading pass, not after.**
