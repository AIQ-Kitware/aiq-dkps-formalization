# Qwen TTS audit — transcript-first draft lectures (2026-11-08, re-evaluation)

**Auditor:** Qwen (independent listening-format review)
**Subject:** `visualizations/draft-stages/tts-lectures/000000–149000` — the 150
transcript-first TTS drafts, **in their current state after three revision
campaigns**: the standalone-listening revision, the pedagogical-structure
revision, and the LLMism/assistant-style revision (all dated 2026-11-08, each
distributed as an incremental overlay).
**Companion ledger:** [`qwen-audit-candidates-2026-11-08.tsv`](qwen-audit-candidates-2026-11-08.tsv)
(67 rows; the final column `v2_status` says for each original finding whether
it is `resolved`, `open`, or `open_moved` in the current tree — **47 open,
20 resolved**).

## What changed since the first audit, and how the feedback stands

The first version of this audit (written at ~15:00) found: 15 residual
cross-episode references, a 9-item ambiguous-math cluster, 2 raw-notation
items, a 10-item pronunciation listening list, cross-lecture convention
drift, and a small pile of self-referential phrasings. Between then and this
re-evaluation two more overlays landed:

- **Pedagogical-structure revision** (80 of 150 revised): restored local
  prerequisites in place of episode pointers, repaired the `045000` broken
  opening, corrected the `005000` category error (bounded operators as a
  complete normed algebra, not "linear functionals"), and — notably — **fixed
  two of my P1 items with exactly the rewordings suggested here**: `134000`
  now says "the square root of the *quantity* two minus square root of two"
  and "sixteen times the *quantity* two minus square root of two".
- **LLMism revision** (86 of 150 revised): removed the residual
  process/authoring frames ("the source formalizes", "the formalized
  rectangular theorem", "implementation", "source-shaped wrapper"), cut the
  "Today we will" template from 45 occurrences to 6, and removed the last
  "Yesterday…" and "the previous theorem" callbacks.
- **New metadata layer (no TTS impact):** 150 `metadata/*.json` citation
  sidecars (49 historical-claim anchors, all `pending_primary_passage_comparison`;
  300 optional-resource links; 18 bibliographic records) plus
  `reference_metadata.py` / `test_reference_metadata.py` and the
  `reference-metadata-report-2026-11-08.md` / `reference-audit-by-lecture`
  ledgers. These sit *outside* the spoken region and the display-only
  appendix; the extraction check still passes on all 150 files. They change
  nothing a TTS listener hears — they are relevant only if the same narration
  later drives interactive slides with citation chips.

**Net effect on my findings: 20 of 67 are resolved** — all 15 residual
cross-episode references (the pedagogical pass screened spelled-out lecture
numbers too), the two `134000` nested-radical ambiguities, the `006000`
"formalized operator theory" phrase, and the `149000` "before hearing the
verification" line. **47 remain**, and they are now the entire actionable
queue. No *new* TTS-hostile constructs were introduced by the rewrites: the
post-overlay rescan shows the same category profile (no raw markup beyond the
known `111000` subscript, same non-ASCII set, no scientific notation, no new
digit tokens, all 150 files still extract cleanly; sentence cadence unchanged).
The rewrites themselves read well on a listening simulation — the `045000`,
`011000`, `038000`, `116000`, `005000` and `006000` openings I re-read are
cleaner than before, and the pedagogical pass's claim that "no residual
episode references remain" is confirmed by a direct grep (the only remaining
matches for those patterns are intra-lecture phrases like "an earlier
contrast" and "first in the bounded setting").

## Overall verdict (re-evaluated)

The series is **ready for a first synthesized-audio pass with a short, well-
understood edit queue**. What remains is smaller and mostly mechanical:

1. **One notation cluster** (`111000:51` — the only raw markup in the corpus).
2. **One un-introduced symbol** (`009000` — "eye").
3. **One unparseable sentence** (`036000:61`).
4. **One inconsistent subscript idiom** (`096000`/`097000` — "a one" vs "a sub k").
5. **The "over two" half-angle family** (9 remaining occurrences across
   `134000`, `132000`, `133000`, `145000`, plus the doubled-angle naming
   variants).
6. **A pronunciation listening session** (word list unchanged; `adjoint` is
   now 1,142 occurrences — the largest single pronunciation risk in the
   series, with no verified remedy in the pronunciations README).
7. **Convention sweeps** (`ell two`/`L two`, `adjoint`/`star`, p-ordinal,
   doubled-angle naming, en-dash/hyphen) and the **P3 cosmetic batch**
   (asterisks in 32 files, curly quotes in 2, the `083000` orphan line, three
   "read aloud" self-references, `Section six` without a paper name).

Priority legend: **P1** = a listener can genuinely mis-hear a mathematical
claim (fix before synthesis); **P2** = consistency / pronunciation risk;
**P3** = cosmetic.

Line numbers in the ledger are line numbers of the **extracted narration**
(`extract_narration.py` output); every `match` string is greppable verbatim in
the `.md` file. The ledger's `v2_status` column records this re-evaluation per
row, so the document remains a usable work queue.

---

## A. Pronunciation-risk vocabulary (P2 — one listening session)

Frequencies in the **current** spoken text. The pronunciations README policy
stands: only listening-verified aliases go into `breeze-tested-en-us.pls`.

| Word (family) | Now | Where | Note |
| --- | ---: | --- | --- |
| **adjoint** | **1,142** (was 1,117) | everywhere; peaks 084000, 013000, 105000, 108000, 040000, 033000 | Top unverified problem word, and it *grew* slightly across the revision passes. A single verified remedy here pays more than any other fix in the series. |
| Hilbert / orthonormal | 407 / ~240 | everywhere | README-listed problem words; `ortho-normal` remedy known to over-pause. |
| Sylvester | 233 | 063000–071000, 086000, 093000–094000, 104000, 108000–110000, 128000–129000, 141000, 149000 | |
| Frobenius | 165 | 023000–059000, 099000, 135000–147000 | |
| **Ky Fan** | **162** in 34 lectures (densest: 054000 15×, 122000 14×, 104000 10×) | the 054000–061000, 096000–101000, 104000–124000, 127000–140000 blocks | Used as an adjective for a person; confirm the voice doesn't render it as the common English word. |
| Borel / Banach / Schatten | 108 / 57 / 46 | 073000–081000 / 003000, 005000, 068000, 098000, 104000 / 057000, 099000, 132000 | |
| Rayleigh / Ritz / Parseval / Halmos / Riesz / Weyl / Cayley / Lebesgue / Courant / Fischer / Eckart / Young / Toeplitz / Yosida / Rosenblum / Kato | 87 / 125 / 12 / 9 / 16 / 11 / 10 / 9 / 15 / 15 / 6 / 6 / 5 / 5 / 4 / 1 | Courant-family names now span 027000, 028000, 029000, 052000, 061000, 096000, 119000 and neighbors | One listening sentence each is cheap. |
| **Sz.-Nagy** | 1 (`048000:9`) | unchanged | The mid-name period forces a TTS pause; say "the Nagy–Kato intertwiner". |
| **Hölder** | 1 (`099000:65`) | unchanged | The only accented letter in the corpus; the en-US voice may glitch on "ö". The attribution adds little — "the Schatten product estimate" is cleaner. |

## B. Notation tokens inside the spoken region

| # | Location | Status | Item |
| --- | --- | --- | --- |
| B1 | `111000:51` | **STILL OPEN (P1)** | "Split E into C equals **P_U** E and S equals **P_{U perpendicular}** E" — still the only raw markup in the spoken corpus; the extractor's `--check` misses it (it bans only ` ``` `, `$$`, `\[`, `\<`, `<!--`). The pedagogical and llmism passes both touched neighboring lectures but not this line. Rewrite in words. |
| B2 | `009000:31, 99` | **STILL OPEN (P1)** | "the one-coordinate vector **eye**" — the imaginary unit spelled as a word, still never introduced; the rest of the course uses bare *i* with on-the-spot glosses (081000, 087000). Introduce the imaginary unit once, then use *i*; hearing-test bare *i* (181 "i" tokens) for the pronoun reading. |
| B3 | `146000:71` | **STILL OPEN (P2)** | "Wedin-type **sin-theta** phenomena" — bare "sin" + hyphenated code token. |
| B4 | `135000:53, 55, 57` | **STILL OPEN (P2)** | **theta-max** three times, including "secant of theta-max over two" and "cosine theta-max over two" (which are also half-angle ambiguities, see C4). |
| B5 | `048000:9` | **STILL OPEN (P2)** | **Sz.-Nagy** (see A). |
| B6 | `099000:65` | **STILL OPEN (P2)** | **Hölder** (see A). |
| B7 | 32 files | **STILL OPEN (P3)** | Markdown emphasis in the spoken region (`016000` 9×, `017000` 7×, `030000` 6×, `031000` 8×, …) — the revision passes did not strip them. Breeze ignores the asterisks; captions would print them. |
| B8 | 2 files | **STILL OPEN (P3, reduced)** | Curly quotes down from 4 to 2 occurrences (019000's smart apostrophe went; 028000:27 and 032000:7 remain). |

## C. Ambiguous spoken mathematics

| # | Location | Status |
| --- | --- | --- |
| C1 | `134000:41` "the square root of two minus square root of two" (∨√2−√2=0) | **RESOLVED** — now "the square root of the **quantity** two minus square root of two". The fix is exactly the one suggested. |
| C2 | `134000:45` "sixteen times two minus square root of two" (∨16·2−√2) | **RESOLVED** — now "sixteen times the **quantity** two minus square root of two". |
| C3 | `134000:77` "sine theta equal **two sine theta over two times cosine theta over two**" then the doubled version | **STILL OPEN (P1)** — three stacked "over"s; say "sine theta equals two times the sine of **half** theta times the cosine of **half** theta…". The same line also carries "the competitor's … two sine theta, twice" (fine as a label). |
| C4 | The "over two" half-angle family — `134000:29` (sine phi over two), `132000:63`, `133000:21, 27`, `145000:15, 17` | **STILL OPEN (P1 first three, P2 rest)** — each means f(θ/2) but hears as (f θ)/2; "twice sine of theta over two" hears as sin θ. Standardize on "the sine of **half** theta" / "twice the sine of **half** theta". |
| C5 | `036000:61` "the pair **consisting of its first coordinate twice**" | **STILL OPEN (P1)** — the listener cannot recover (a,b,c) ↦ (a,a); say "the pair whose two entries are both the first coordinate of the triple". |
| C6 | `149000:65` "For **sine of two theta**" | **STILL OPEN (P2)** — ambiguous between sin(2θ) and sin(2)·θ. The course now carries four naming variants for the doubled-angle family: `sine of twice` (18), `sine-two` (24), `sine of two` (2), and a fourth bare `sine two theta` / `tangent two theta` label pair in the `121000` opening. Pick one (the "twice" form is the unambiguous one) and sweep. |
| C7 | `141000:65` "a factor of pi over two divided by the gap" | STILL OPEN (P3, parses correctly left-to-right; optional clarification). |
| C8 | `009000` bare *i* (181 tokens course-wide) | **STILL OPEN (P2, hearing test)** — letter vs pronoun risk; see B2. |

## D. Cross-episode references

**All 15 residual references flagged in the first audit are RESOLVED** by the
pedagogical-structure pass (dual-space, two-lectures-ago, singular-value,
Ky Fan ×2, majorization ×2, lecture sixty-six, principal-angle, lecture
seventy-two, domain, lecture ninety-six, tangent-two-theta, Sylvester unit,
Rayleigh–Ritz/Courant–Fischer lectures). A direct grep of the current
narrations for the pattern families returns only intra-lecture phrases ("an
earlier contrast" in `074000`, "first in the bounded setting" in `110000`,
"first in the complex setting" in `102000`) — none of these is an episode
reference. **No action needed.**

## E. Cross-lecture consistency (still open)

| Convention | Current state |
| --- | --- |
| **ell two vs L two** (P2) | 65 + 6 vs 62. Still mixed *within* `072000` (7 vs 5), `073000` (2 vs 1, line 85), `088000` (1 vs 2). `010000:15` still says "ell two, pronounced ell two". |
| **X adjoint vs X star** (P2) | Unchanged: 20 lectures use postfix "star" (`012000`–`027000` early-matrix block, plus the later `084000`–`087000`, `094000`, `138000`, `140000`, `141000`), while the rest of the course says the word. |
| **p-th ordinals** (P3) | `p th` / `p-th` / `pth` all still present. |
| **doubled-angle naming** (P2) | See C6 — four variants now. |
| **author-name dashes** (P3) | `149000:3` still opens with hyphenated "Davis-Kahan" (course-wide form is the en dash); "Hilbert-Schmidt" hyphens remain in `069000`, `128000`, `141000`. |

## F. Unnatural / self-referential phrasings

| Location | Status |
| --- | --- |
| `083000` final line — "The answer requires a domain of its own." (orphan fragment) | **STILL OPEN (P1 for editing, trivial)** |
| `134000:9` — "The matrix looks cumbersome **when read aloud**" | STILL OPEN (P3) |
| `015000:63` — "In symbols **read aloud**: T after P equals P after T" | STILL OPEN (P3; say "In words:") |
| `010000:15` — "ell two, **pronounced ell two**" | STILL OPEN (P3) |
| `149000:57` — "the ambient sine theorem of **Section six**" (no paper named) | STILL OPEN (P3; the same lecture later says "the original paper's Section ten") |
| `006000:75` — "the formalized operator theory" | **RESOLVED** by the llmism pass (now a plain mathematical explanation of the Hahn–Banach step) |
| `149000:5` — "before hearing the verification" | **RESOLVED** |

## G. Cadence and length — no action

Re-verified after the rewrites: all 150 files extract cleanly; no digit tokens
other than "1970"; no scientific notation; sentences remain short (the
pedagogical pass even made several openings terser). The two longest lectures
(`002000`, `003000`) are flagged by the pedagogical ledger as >2,200 words —
a deliberate content decision, not a TTS defect; noted only so the batch
synthesizer's per-chunk guards in `tts.toml` are tested on them.

## H. Out of scope / notes

- The **citation sidecars** (`metadata/*.json`, `reference_metadata.py`, the
  reference-audit ledgers) are a display/metadata layer; 49 historical
  anchors are `pending_primary_passage_comparison`. That is a *mathematical
  fidelity* audit, explicitly queued after this listening work — it does not
  change what TTS speaks.
- The style rules' four-multiple-choice-question requirement is still
  implemented here as reconstruction prompts (unchanged by either campaign) —
  an editorial judgment call, not a TTS issue.
- `000000` remains exempt from a Lean appendix and now has a valid spoken
  region (verified, unchanged).

## Priority queue (re-evaluated)

1. **P1 — remaining mis-hearable math (8 local rewrites):** `111000:51`
   (P_U), `009000` (eye → introduced i), `036000:61`, `096000:11,13` +
   `097000:11` (a sub one/two/three), `134000:29,77`, `132000:63`,
   `133000:21,27`, `145000:15` (half-theta idiom), `149000:65` (+ sweep the
   C6 naming variants including `121000:3`).
2. **P2 — listening session** on the section A list; highest value:
   `adjoint` (1,142×), `Ky Fan`, bare *i*, `Hölder`, `Sz.-Nagy`.
3. **P2 — sweeps:** ell/L two, adjoint/star, p-ordinal, doubled-angle naming,
   dash normalization, `theta-max`.
4. **P3 — cosmetic batch:** asterisks (32 files), curly quotes (2), `083000`
   orphan line, the three "read aloud" self-references, `Section six`.

After these, re-run `python3 extract_narration.py --check [0-9]*.md` (must
stay 150/150 green) and re-extract before synthesis.
