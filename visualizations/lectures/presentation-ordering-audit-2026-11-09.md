# Presentation-order audit of the TTS lecture series

Date: 2026-11-09 · Audited by `qwen3.8-27b-dbirks-hyperqwen-huge` (via LiteLLM, pi agent)
Scope: all 22 authored transcripts under `visualizations/lectures/`, the prerequisite
graph in `index.yaml`, and — where a numbered lecture was re-edited from a frozen
reference deck — the reference scene files under `dkvis/`.

Method: every `lecture.md` was read in full in numbered order. The "order" being
audited is the one a TTS listener actually receives: the six-digit lecture numbers,
i.e. the NetworkX topological linearization of `index.yaml` with YAML order as tie
break (`python -m dkvis.lectures` previews it). Two notions are kept distinct
throughout:

- **`requires`** — a hard prerequisite edge in `index.yaml`;
- **numbered before** — the presentation position.

The numbers inherit the DAG, so most findings below are really findings about the
`requires` edges and about what each lecture contains, and the recommendations
follow from that.

## The order as it stands today

| # | ID | Title (short) | series | requires (hard edges) |
|---|----|---------------|--------|------------------------|
| 000010 | basics | Before the Series: Foundations | prerequisites | — |
| 000505 | history_overview | How eigenvector stability became a subject | history | — |
| 000670 | history_people_foundations | People — geometry, sound, approximation | history_people | — |
| 000835 | history_people_operators | People — operators, reliable computation | history_people | — |
| 001000 | projections | Subspaces and projections | prerequisites | basics |
| 001250 | invariant_blocks | Invariant subspaces | bridges | projections |
| 001500 | complementary_projection | Thinking about I minus P | prerequisites | projections |
| 002000 | singular_norms | Singular values and displacement cost | prerequisites | projections |
| 002250 | principal_angles | Principal angles | bridges | projections, singular_norms |
| 002500 | matrix_exponential | The exponential of a matrix | prerequisites | projections |
| 002666 | minmax | Rayleigh quotients, min-max, Weyl | operators | projections, singular_norms |
| 002749 | rayleigh_ritz | Rayleigh–Ritz | spectral_foundations | projections, minmax, invariant_blocks |
| 002833 | polar | Operator absolute value, polar decomposition | operators | projections, singular_norms |
| 002916 | pvm | Projection-valued measures | spectral_foundations | projections, minmax, invariant_blocks |
| 002958 | trace_gradients | Trace pairings and matrix gradients | bridges | basics, singular_norms |
| 003000 | variations | Feasible variations and stationarity | prerequisites | projections, singular_norms, matrix_exponential, trace_gradients, invariant_blocks |
| 003500 | sylvester | Sylvester equations and spectral separation | operators | minmax, matrix_exponential |
| 003750 | sine_theta | Davis–Kahan sine theta ("How far can an eigenvector turn?") | spectral_perturbation | sylvester, complementary_projection, rayleigh_ritz |
| 003875 | yws | Yu–Wang–Samworth | spectral_perturbation | sine_theta, singular_norms, minmax, principal_angles |
| 003937 | uniform_minima | Uniform approximation and minima | bridges | basics |
| 004000 | matching_study | The matching proof, a learner's walkthrough | *(missing)* | variations, principal_angles, invariant_blocks, uniform_minima |
| 005000 | matching_proof | The matching proof, a compact presentation | *(missing)* | variations, principal_angles, invariant_blocks, uniform_minima |

The DAG has two nearly disjoint tracks that share the early foundations:

- **Track A — the DK perturbation core:** projections → {invariant_blocks,
  complementary_projection, singular_norms, minmax} → rayleigh_ritz → sylvester →
  sine_theta → yws.
- **Track B — transport/optimization:** projections → singular_norms →
  matrix_exponential → trace_gradients → variations → uniform_minima → the two
  matching lectures.

`matrix_exponential` is the only shared junction node (it is required by both
`sylvester` and `variations`).

---

## Findings

Severity: **H** = a linear student learns the wrong material at the wrong time;
**M** = a specific ordering inconsistency a listener will notice; **L** = catalog
hygiene.

### H1. The optimization track is numbered *before* the DK core it does not serve

The three Track-B setup lectures — `matrix_exponential` (002500),
`trace_gradients` (002958), `variations` (003000) — are all numbered before the
three Track-A capstones `sylvester` (003500), `sine_theta` (003750), `yws` (003875),
even though none of those three require `trace_gradients` or `variations`.

Evidence:

- `sylvester` requires `{minmax, matrix_exponential}`; its proof (SyGap) uses the
  exponential only as the decay flow `e^{-tA} X e^{tB}` and its norm bound. It does
  not use `trace_gradients` or `variations`.
- `sine_theta` requires `{sylvester, complementary_projection, rayleigh_ritz}`.
  Its only contact with the optimization machinery is one sentence in `S08Why`:
  "For whole subspaces the same spectral-separation idea becomes a Sylvester
  equation."
- `yws` requires `{sylvester …}` only transitively through `sine_theta`; its proof
  never uses any of the Track-B machinery (see M3).
- The only consumers of `variations` are the two matching lectures at the very end
  of the series (004000, 005000).

Consequence: a linear listener is made to sit through `matrix_exponential` (a
314-line lecture), `trace_gradients`, and `variations` (a 287-line lecture on
constrained transporter optimization) **before** reaching the series' headline
result, and then carries that machinery unused through `sylvester`, `sine_theta`,
and `yws` — four lectures, roughly the second half of the course. `variations`
sits 1000 numbers before its first consumer.

The `matrix_exponential` lecture itself advertises its true audience:
`Ex11SourcePreservation` says "We have arrived at the exact feasible curve in the
variations lecture," and `ExFacts` closes with "These are the identities that let
us construct continuous families of legal motions in constrained optimization." A
listener in the numbered order meets that promise four lectures before the theorem
that needs it — and, if their goal is the DK core, never meets a need for it at all.

**Proposed fix.** Renumber so the two tracks are contiguous:

```text
Track A first:
  000010 → history triad → 001000 → 001250 → 001500 → 002000 → 002250
        → 002666 → 002749 → 003500 → 003750 → 003875
Track B after:
  002500 (matrix_exponential) → 002958 → 003000 → 003937 → matching pair
```

i.e. move `matrix_exponential`, `trace_gradients`, `variations` to *after*
`yws` (keeping their internal order and stable IDs; only the six-digit numbers
change, which the organizer's `--rebalance` exists for). If that is too disruptive,
the cheaper fix is to weaken nothing but *label* these three clearly as
"Track B — needed only for the matching lectures," since `sylvester` is the only
Track-A consumer of `matrix_exponential` and uses a small slice of it.

### H2. Two optional dead-end lectures sit in the middle of the required path

`polar` (002833) and `pvm` (002916) are required by **no** other lecture. In the
numbered order they are interleaved between `rayleigh_ritz` (002749) and
`trace_gradients` (002958) — i.e. a linear listener must pass through both before
reaching `sylvester`/`sine_theta`, even though neither is a prerequisite of
anything downstream.

This is confusing in both directions:

- **Skip them:** fine mathematically, but their position in the linear path makes
  them look load-bearing. `pvm` ends with `PvDk`: "Where the PVM enters
  Davis–Kahan … the ranges of P and Q are the spaces we want to compare … That is
  the bridge from finite eigenvector pictures to the Hilbert-space statements."
  The listener is then taken to `sine_theta`, whose `S00bSetting` re-derives the
  spectral decomposition locally ("In infinite dimensions the corresponding object
  is a decomposition into spectral subspaces") and whose Lean statement is
  presented without any reference to the PVM API just taught. The promised bridge
  is never used.
- **Take them:** the listener has invested two substantial lectures in a PVM API
  that the capstone theorem's Lean statement (S12Lean) does not visibly use.

**Proposed fix.** Move both to the end of the linear order (they are genuinely
optional deep-dives), or mark them as an optional detour in the catalog so the
numbered path does not read as if they gate the DK core.

### H3. The headline lecture (003750) is a re-edited *standalone* talk wearing the
number of an 18th lecture in a dependency chain

Three independent facts collide in `sine_theta`:

1. `index.yaml` places it at the end of a 17-lecture path and lists hard
   prerequisites (`sylvester`, `complementary_projection`, `rayleigh_ritz`). The
   generated README repeats them: "Prerequisites: sylvester,
   complementary_projection, rayleigh_ritz."
2. The transcript's own header says: "The audience is a specialist … A local
   notation refresher appears on the second slide, so **no earlier video is
   needed**."
3. The content is a re-edited composition of the frozen 18-scene
   `sine-theta-short` reference deck (provenance: "15 of the 18 scenes"), and it
   *re-teaches, at compressed level, everything the linear path already covered
   in full*: the elliptic picture of a symmetric matrix (S01/S02, cf. `minmax`
   and `rayleigh_ritz`), Weyl (S02/S03, cf. `minmax`), the frame-overlap error
   (S04, cf. `principal_angles`), the residual and its forms (S05, cf.
   `rayleigh_ritz`), and the `I − P` sine block (S04, cf. `complementary_projection`).

So a linear student who did the prescribed path experiences the course's climax
twice: once slowly (001500 → 002250 → 002666 → 002749 → 003500) and once as a
compressed re-telling that claims it needs none of them. And a standalone viewer
told "no earlier video is needed" is still, in the catalog, gated behind five
lectures. The two audiences get contradictory statements from the same artifact.

**Proposed fix.** Pick one identity and make the catalog say it. If it is the
standalone specialist talk (as the header claims), its `requires` should reflect
that (at most `basics`, or none), and the course should present it as an optional
capstone *after* the path, not as its 18th step. If it is the path's capstone,
the "no earlier video is needed" header is false and should go.

### H4. The 003750 scene numbering no longer follows presentation order, and its
cut scenes are invisible

The numbered transcript presents scenes in this order (verified against
`dkvis/slides_sine_theta.py`, where the reference order is
S03 → S03c → S03b → S03d → S04 → … → S11 → S12 → S13 → S14):

```text
S00 → S00b → S01 → S02 → S03b → S03 → S03c → S04 → S05 → S06 → S07 → S08
→ S11 → D01 → S12 → P01 → P02 → S14
```

Problems:

- `S03bWanted` is presented **before** `S03NoGap` (a deliberate re-edit that
  arguably reads better — define "wanted" before showing instability — but the
  label order now contradicts the presentation order).
- The sequence jumps `S08 → S11`: `S03dCompute`, `S04bSinThetaOperator`,
  `S07bReading`, `S08Components`, `S09Sylvester`, `S10Sharp`, and `S13Family`
  were dropped or merged, but nothing in the transcript says so. `S08Why` silently
  absorbs part of `S08Components` + `S09Sylvester` ("the same spectral-separation
  idea becomes a Sylvester equation"); the **sharpness** content of `S10Sharp`
  disappears entirely; `S13Family` (the norm-family scene) is gone. A reader
  comparing against the paper or the reference deck sees holes in the numbering
  with no explanation.
- `D01Planes` (from `slides_sine_theta_3d.py`) is sandwiched between `S11Payoff`
  and `S12Lean`, and the `P01Claim`/`P02Counterexample` block (from
  `slides_prop44.py`) is inserted between `S12Lean` and `S14Summary`. The mixed
  `S`/`D`/`P` namespaces make the transcript read as though scenes are missing
  rather than re-edited.

**Proposed fix.** Renumber the scenes sequentially in presentation order (the
scene *IDs* are local to this numbered edition; the frozen reference deck keeps
its own), or at minimum add a one-paragraph note in the transcript header listing
exactly which of the 18 reference scenes were dropped and where their content went
(`S09`'s Sylvester pointer → folded into `S08Why`; `S10Sharp` → dropped; etc.).

### M1. The history triad contains a pointer in the wrong direction

Numbered order is `000505` (overview) → `000670` (people I) → `000835` (people II).

- `000670` closes with: "Further episodes can introduce Hotelling, Courant and
  Fischer, the norm theorists, and the modern statisticians." **No such episodes
  exist**, and every one of those people is already covered in `000505` — which
  *precedes* `000670` (HiHotelling, HiNormPeople, HiYws). The forward pointer
  points at content that lies behind the listener.
- `000835` closes the other way: "Rosenblum, Dixmier, the singular-value
  researchers, and YWS remain visible in our coverage notes and **the broader
  historical overview**" — i.e. `000505`, the first of the three.
- `000505` is the *broadest* of the three (it covers all the cast, the whole
  matching-theorem arc, the Prop-4.4 counterexample, and the norm theory), yet it
  is positioned as the *first* of three. It also spoils the punchlines of the
  series' final lectures (the R^4 counterexample, the matching reduction) in
  lecture two of twenty-two.

**Proposed fix.** Either (a) reverse the triad — `000670`, `000835`, then `000505`
as the synoptic overview — or (b) delete the "further episodes" sentence in
`000670` (its "Recall: no proofs required" siblings make it a standalone
biography lecture, and the promised content is in a different lecture than the
one that follows it).

### M2. The two matching lectures present the *same* proof in the order
long → short

`004000` (935-line "learner's narrated walkthrough") is followed by `005000`
(297-line "compact presentation") of the same theorem with essentially the same
`requires` list. As a linear sequence this reads as a 30-minute summary following
a 90-minute version of the identical argument — the natural reading order for a
talk is the compact version first, with the walkthrough as the study companion.
These are alternates, not a sequence; the numbering presents them as a sequence.

**Proposed fix.** Present them as a pair with an explicit "choose one" label in
the catalog (or swap the numbers so the compact talk precedes the walkthrough).

### M3. `yws` hard-requires `sine_theta`, but its proof never uses the sine-theta
theorem — and it invokes an inequality the series never teaches

The YWS proof (YsResidual → YsLowerIdentity → YsEntrywise) is an elementary
residual-sandwich argument. Its actual inputs are: principal angles (`YsGeometry`,
`YsAlignmentProof`), Weyl (`YsOperatorUpper` — taught in `minmax`), Hoffman–
Wielandt (`YsFrobeniusUpper`), and a one-line recognition that the lower bound "is
the same operator-equation structure that appears in Sylvester estimates"
(`YsLowerIdentity`) — a pointer to `sylvester`, not to `sine_theta`. The
`requires: sine_theta` edge is a *series-level* dependency (YWS is a variant of
Davis–Kahan), not a *proof-level* one, and it forces the 598-line `sine_theta`
lecture — including its Prop-4.4 counterexample block — to be a hard gate for a
statistical-estimation lecture whose proof could stand on `minmax` +
`principal_angles` alone.

Worse, `YsFrobeniusUpper` states the **Hoffman–Wielandt inequality** by name
with no local derivation, and **no lecture in the series teaches it** (a grep of
all 22 transcripts finds it only in `003875` and its `sources.md`). A student
who has taken the whole prescribed path has never seen the theorem.

**Proposed fix.** Demote `sine_theta` from a hard `requires` to a "recommended
context" note (keeping the soft ordering), and either add the two-line
Hoffman–Wielandt statement + one-line proof sketch to `YsFrobeniusUpper`, or
teach it in `minmax` (it is a direct corollary of the same weighted-average
machinery `MmRayleigh` already develops).

### M4. "Direct rotation" is the object of a whole lecture block but is never
taught

The P01/P02 block in `sine_theta` is about **Proposition 4.4 — the optimality of
the direct rotation** — yet the concept is defined in exactly one sentence, in
that block: "it turns by exactly the principal angles and does nothing else"
(P01Claim). The only other mentions are a schematic in `000505` (HiCorrection)
and the same one-sentence treatment as a "convenient reference map" in
`M20PairCoordinates` and `T06LocalFibers` of the matching lectures. The 1970
paper devotes a full section to it; the series never builds it up (no scene in
any lecture develops the multi-plane construction from the one-plane rotation/
reflection material of `002000` Sn05). So the P01/P02 block, and the matching
proof's reference map, both rest on an undefined term for any listener who did
not happen to retain a sentence from lecture two.

**Proposed fix.** Either give `principal_angles` (002250) or `002000` a short
scene that constructs the direct rotation from the principal-plane pairs and
states its displacement singular values per plane, or add that construction to
P01 itself.

### M5. Premature seeding of the sin-theta notation

`complementary_projection` (001500) — an early "prerequisites" lecture about
`I − P` — already introduces the *theorem's* lettering in `CpSineBlock`:
"F zero … the wanted space … F one … the unwanted space … E zero is an orthonormal
trial frame … the operator residual R, defined using the studied operator A hat
and a trial operator A zero." These are exactly the symbols of the `sine_theta`
theorem, introduced 16 lectures before it appears, without saying that is what
they are. Likewise `002000` Sn06SmoothCost pre-announces the entire matching
strategy ("first use p between one and two to derive stationarity and a
decomposition, then let p approach one from above"). Both are defensible as
foreshadowing, but neither says so, so a listener either forgets the seeding or
wonders where `E0/F0/F1/A0/R` will show up.

**Proposed fix.** One sentence each: "These letters are the ones the
sine-theta theorem of lecture 003750 will use" / "This is the plan of the
matching lectures at the end of the series."

### M6. The `sylvester → minmax` edge is not used by the proof

`sylvester` requires `minmax`, but the lecture's argument (scalar division
SyEntries → exponential decay SyGap) never invokes Courant–Fischer or Weyl; the
gap is a quadratic-form bound, and `SySetup` says "Recall: Know operator norms and
matrix exponentials." The edge looks like soft pedagogical ordering that has
become a hard edge, and it is one of the two forces keeping `minmax` (and
everything it gates) interleaved into Track B's numbering.

**Proposed fix.** Demote to a soft "review before this" note, or keep the edge
but document why (e.g. so the listener has seen Weyl before `sine_theta` S02,
which does use it — in which case the edge belongs on `sine_theta`, where it is
actually consumed).

### L1. Catalog hygiene

- `matching_study` and `matching_proof` are the only two of the 22 entries in
  `index.yaml` with **no `series` field** (`matching_study` also lacks
  `background`). Every other entry has one.
- The `series` vocabulary does not match the roles: `prerequisites` contains
  `matrix_exponential` and `variations` (prerequisites *of the matching track
  only*), and `bridges` contains four lectures scattered from 001250 to 003937.
  A student who follows the *series* groups gets a different sequence than the
  numbers; right now the two orderings disagree on where the optimization track
  belongs.
- `000505`'s closing map — "start with projections and principal angles, then
  residuals and spectral separation" — does not match the numbered path, which
  inserts `invariant_blocks`, `complementary_projection`, `singular_norms`, and
  `matrix_exponential` between those waypoints.

**Proposed fix.** Assign the two matching lectures a series (e.g.
`transport_optimization`), align `series` labels with the two tracks of H1, and
sync `000505`'s roadmap paragraph with whichever order the course actually adopts.

---

## What would the cleanest ordering be?

Keeping all stable IDs and content, the DAG plus the findings above suggests:

```text
Prerequisites / foundations
  000010 basics
  000505 / 000670 / 000835   (history triad — order per M1)
  001000 projections
  001250 invariant_blocks
  001500 complementary_projection
  002000 singular_norms
  002250 principal_angles

Track A — the DK core (contiguous)
  002666 minmax
  002749 rayleigh_ritz
  003500 sylvester            (needs matrix_exponential — see below)
  003750 sine_theta           (standalone identity per H3)
  003875 yws                  (demote sine_theta edge per M3)

Track B — transport & optimization (contiguous, after the core)
  002500 matrix_exponential
  002958 trace_gradients
  003000 variations
  003937 uniform_minima
  004000 / 005000              (pair, per M2)

Optional deep-dives (no consumer)
  002833 polar
  002916 pvm
```

One wrinkle to settle before renumbering: `sylvester` genuinely uses the matrix
exponential (H1's junction node). Two options: (a) accept `matrix_exponential`
as a dual-track prerequisite placed before `sylvester` and renumber only
`trace_gradients`/`variations`/`uniform_minima` to after `yws`; or (b) extract the
small slice of `matrix_exponential` that `sylvester` needs (existence,
invertibility, the exponential norm bound) into `sylvester` itself and move the
full lecture to Track B.

## Notes for the reviewer (GPT)

1. Findings H1–H4 are about *presentation order*; M1–M6 are about *content
   placement inside or between lectures*; L1 is catalog data. The DAG edges
   themselves (`index.yaml`) were read as ground truth and not re-audited against
   the Lean dependencies.
2. The renumbering machinery the README describes ("existing numbers stay fixed
   when possible; use `--rebalance` to regenerate") is the intended vehicle for
   the H1/H2/M2 fixes; this audit does not perform them.
3. `004000_matching_study/lecture.md` was checked for a suspected text splice
   between M19 and M20 and is currently clean; the suspicion came from an
   artifact of reading the file in two windows, not from the file itself.
4. The scene-ID analysis in H4 is based on the class definitions in
   `dkvis/slides_sine_theta.py` (S03NoGap → S03cUnstable → S03bWanted →
   S03dCompute → … → S11Payoff → S12Lean → S13Family → S14Summary) and the
   section order of `003750/lecture.md`
   (S03bWanted → S03NoGap → S03cUnstable → S04 → … → S08 → S11 → D01 → S12 →
   P01 → P02 → S14).
5. Deliberately *not* flagged: the `S03b-before-S03` re-edit is pedagogically
   defensible (it is flagged only because the labels no longer match the order);
   and the fact that the two history-people lectures repeat people from the
   overview is by design (biography vs. lineage), though the overview-first
   ordering is the part in question (M1).
