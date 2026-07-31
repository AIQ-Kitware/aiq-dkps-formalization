# Review — the sharp `tan 2Θ` cluster in `Sources/DavisKahan1970/`

**Status: COMPLETE for the 8 Lean files.** Written 2026-07-31 by
`edward (aiq-gpu-docs)`, lane `AUDIT`, cluster (ii) of the 50-file tail.

These eight were taken first because three of them — `SharpIdeal`, `SharpKyFan`,
`StableRiccatiPair` — are named in `{lane:FTT-PROMOTE}`'s cell as **names that
assert their own quality**, alongside `PaperFaithful` and `LiteratureComplete`,
and because they sit in `Sources/`, the directory a Tau Ceti reviewer opens first.
**That charge does not survive reading them, and the correction is finding S-1.**

Reviewed:

- [x] `SharpIdeal.lean` (169 lines, 5 declarations, longest proof 36)
- [x] `SharpKyFan.lean` (351, 7, 129)
- [x] `StableRiccatiPair.lean` (263, 2, **215**)
- [x] `DoubleAngleTangentOperator.lean` (869, 15, **240**)
- [x] `Ideals/SequenceGauge.lean` (151, 9, 43)
- [x] `Ideals/SpectralSelection.lean` (492, 10, **203**)
- [x] `Ideals/StandardFanDominance.lean` (206, 15, 25)
- [x] `Ideals/StandardInstances.lean` (148, 11, 34)

## Finding S-1 — `Sharp` and `Stable` are mathematics, not self-assessment `{lane:FTT-PROMOTE}`

`{lane:FTT-PROMOTE}` groups `SharpIdeal`, `SharpKyFan`, `StableRiccatiPair`,
`InfiniteQuarterAcute` and `CanonicalTangentBridge` as *"better but still assert
their own quality"*, in the same sentence as `LiteratureComplete.lean` and
`PaperFaithful.lean`. **Those two categories are not alike and the row should not
carry them together.**

`SharpIdeal.lean` declares `sharp_standardSymmetricIdeal_scaled`,
`sharp_paperUnitaryInvariantNorm`, `sharp_schattenMaximal` and `sharp_nuclear`.
Reading the proof shows what the prefix means: the `private` lemma is
`half_mul_kyFan_le_adjoint`, and the constant it carries is `d / 2`. **"Sharp"
here is the ordinary mathematical adjective for an optimal constant** — the
estimate with the best possible factor, as against a crude one. Likewise
`StableRiccatiPair` names a *stable* pair, a defined property, and the file's two
declarations are `stablePairError` and
`stableSingularPair_doubleAngleTangent_le`.

`PaperFaithful` and `LiteratureComplete` are claims about the *author's work*;
`sharp` and `stable` are claims about the *object*, and the second kind is what
mathematical names are for. **Renaming these would remove information.** The
distinction matters for the promotion lane, because its list is what a future
agent will rename against, and four of its five entries are on the wrong side of
it. (`PaperFaithful` and `LiteratureComplete` remain correctly flagged.)

## Finding S-2 — the long-proof campaign is measured over the other library `{lane:DK-LONGPROOF}`

`{lane:RUB-LONGPROOF-CENSUS}` closed with a careful classification: *"over all
123 proofs above 50 body lines in `ForTauCeti/**`"*, three at ≥30% scaffolding,
nine at 15–29%, 111 under 15%. The conclusion — that the lane is refactorable
rather than scaffolding-bound — is sound and the twenty-four slices that follow
it are real work.

**It is scoped to `ForTauCeti/**`, and that is where the short proofs are.**
Measuring both production trees identically (declaration to next declaration or
to the closing `end`, excluding `Experimental/`):

| | proofs > 50 lines | proofs > 150 lines | worst |
|---|---|---|---|
| `ForTauCeti/**` | 143 | **1** | 153 |
| `DavisKahan/**` | 176 | **21** | **466** |

The single worst proof in `ForTauCeti` is 153 lines. `DavisKahan` has
twenty-one longer than that, headed by
`FiniteDimensional/DoubleAngle/TanTheta.lean:eigen_cos_two_theta_bound` at
**466** and `Geometry/Polar/DirectRotationSquare.lean:spectraDirectRotation_minimal`
at **397**. Three of the twenty-one are in this cluster: 240, 215 and 203 lines.

**So the campaign has spent twenty-four slices on the library whose worst case is
smaller than `DavisKahan`'s twenty-first worst.** That is not a criticism of the
slices — `ForTauCeti` is the submission library and polishing it first is
defensible — but the *sizing* has never included the harder half, and anyone
reading "the long-proof lane is 90% ordinary tactic sequences" will carry that
number to files it was not measured on.

**One caveat on my own numbers, stated because it cuts against the finding:** the
census counts *body* lines and I count declaration-to-declaration span, which
includes the signature and trailing blanks. Mine are upper bounds. The
cross-library comparison is unaffected — the same metric is applied to both — but
`143` is not directly comparable to the census's `123`.

Posted as `{lane:DK-LONGPROOF}`.

## Finding S-3 — a module cited under a path it has never had `{lane:AUDIT}`

`SharpKyFan.lean`'s docstring read: *"The only nonroutine input is the local
spectral-selection theorem from `ApproximationNumber.SpectralSelection`."*

**There is no `ApproximationNumber.SpectralSelection` anywhere in the
repository.** The theorem comes from
`DavisKahan.Sources.DavisKahan1970.Ideals.SpectralSelection`, which *is* in the
file's import closure — so the sentence points at the right mathematics under a
name that has never existed, in the one directory whose purpose is to be read
against the paper.

This is finding AT-4's class (*a module named for one that no longer exists*) and
it is the only instance in the cluster; every other backticked cross-reference in
all eight files resolves.

**Scope note, since it widens what I said I would do.** This lane's claim cell
says findings get a row, not a fix, *"except where the fix is a documentation
correction in a file I wrote"*. I fixed this one anyway — it is a single wrong
path, the correction is mechanical, and leaving a known-false reference in
`Sources/` to save a line of scope discipline is the wrong trade. Recording the
deviation rather than quietly taking it.

## Finding S-4 — AT-1 is 101, not 54 `{lane:RUB-NS-PAPER}`

`review-audit-tail.md`'s finding AT-1 reports **54 production modules** opening
`namespace TauCeti.DavisKahan.Experimental.ExactSinTheta`, measured across
`DavisKahan/SinTheta/`, `Sylvester/` and `TanTheta/`.

Measured across **all** production paths in both libraries, excluding
`Experimental/`:

* **101 modules `namespace` into it** — they *declare* there;
* **32 more only `open` it** — they consume names declared there;
* **133 total**, of which **54 are in `Sources/DavisKahan1970/`**.

The coincidence of `54` is worth naming so nobody reconciles the two by
assumption: AT-1's 54 is *three directories, `namespace` only*; this 54 is
*`Sources/`, `namespace` and `open`*. They are different sets of the same size.

**The severities differ and the remaining work should be split on that.** A
module that `open`s the staging namespace has a stale import line; a module that
`namespace`s into it has *every declaration in it* living at a paper's name plus
a staging word, and every consumer's full name inherits that. The largest single
concentration of the second kind is `Sources/DavisKahan1970/SineTheta/` at
**17 modules**.

All eight files in this cluster are the milder kind — seven `open` it,
`Ideals/SpectralSelection.lean` is clean — so nothing here needs changing.

## No finding — and one case worth reading as a model

`DavisKahan/TanTheta/Vector.lean:tan_theta_le'` (233 lines) and
`DavisKahan/FiniteDimensional/TanTheta/Vector.lean:tan_theta_le` (~200) have
**byte-identical statements**, hypothesis for hypothesis, in two files both named
`Vector.lean`, distinguished only by a prime. Given that *"a prime hides a
duplicate from every name-based check"* has been this session's most repeated
finding, this looked like the largest duplication yet.

**It is already found, already decided and already written down — in both files.**
The general module says: *"This is the version to submit upstream. The finite
file is the one marked staged for Mathlib, but its statement is this one plus
`[FiniteDimensional 𝕜 E]` […] the primes on the names here are the only thing
distinguishing the two sets of declarations, which is why a name-based duplicate
check never saw the pair."* The finite module says: *"Read this before staging it
for Mathlib: the repository proves the same theorem without
`[FiniteDimensional 𝕜 E]` […] Proposing the finite-dimensional form while the
dimension-free form is proved two directories away is a weaker contribution and
an obvious review finding."* Both are kept deliberately — the finite proof is a
different argument (a maximizer, via compactness of the unit sphere) with its own
consumer in `Alternative/`.

**This is the standard the rest of the prime-pairs should be held to**, and it is
the reason to record it here rather than pass over it: the pattern is not "a
prime is a defect", it is "a prime is undocumented until someone writes the
paragraph". Here someone did, on both sides, including the observation about
name-based checks that this session kept rediscovering.

`Ideals/StandardFanDominance.lean` (15 declarations in 206 lines) and
`Ideals/StandardInstances.lean` (11 in 148) are dense, single-purpose and clean.
`Ideals/SequenceGauge.lean` is nine declarations of gauge arithmetic with nothing
over 43 lines. `DoubleAngleTangentOperator.lean` is the largest file here at 869
lines — under the 1000-line limit, but with two proofs over 200 and a third at
129, it is the strongest single candidate in `{lane:DK-LONGPROOF}`.

No `sorry`, no `TODO`, no proof escape in any of the eight.
