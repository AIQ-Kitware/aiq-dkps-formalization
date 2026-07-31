# Draft: the roadmap-family submission

Scratch space for the pull request that proposes
[`HilbertSpaceOperatorTheory/`](../HilbertSpaceOperatorTheory/README.md) to
[`TauCetiProject/TauCetiRoadmap`](https://github.com/TauCetiProject/TauCetiRoadmap). Edit
freely — this file is internal and is not submitted.

Upstream the family lands as `TauCetiRoadmap/HilbertSpaceOperatorTheory/`, alongside
`RepresentationTheory/`, which is the existing family of the same shape (an index `README.md`
plus one subdirectory per roadmap). The root `README.md` and `TauCetiRoadmap.lean` each need
one line per new roadmap.

---

## PR title

> Add the Hilbert-space operator theory roadmap family

## PR body — draft

*Six roadmaps covering bounded operators on Hilbert spaces and the spectral perturbation
theory built on them.*

**What this proposes.** [one paragraph: the six roadmaps, one clause each]

**Why one family.** [why these six are one body of mathematics and not six unrelated
roadmaps: the shared vocabulary, the dependency DAG, the single endpoint]

**What it deliberately excludes.** [the exclusion list from the family README, compressed]

**Relationship to existing roadmaps.** One-parameter semigroups borders
`SelfAdjointSpectralTheory`; the boundary is stated in the family README, both sides model
an unbounded operator as a `LinearPMap`, and landing Stone's theorem discharges that
roadmap's `C₀`-group stretch goal.

**Provenance and coordination.** A substantial implementation of most of this material
exists in the AIQ DKPS formalization (Kitware, Inc., Apache-2.0). Feasibility is therefore
not in question, but the roadmaps specify the mathematics intrinsically and do not prescribe
that implementation's API. [note the Spectra-derived material and the coordination already
done or still needed]

**Size.** [how many documents, how long, and what a reviewer should read first — probably
the family README, then `HilbertSpaceOperatorFoundations`, since everything else cites it]

---

## Open discussion points

Things to raise in the PR, or settle before opening it. Each is a real decision, not a
loose end in the writing.

### 1. The name of the square operator modulus — **undecided**

The finite-dimensional `RCLike` construction `|A| = (A⋆A)^(1/2)` currently has no settled
public name, and the roadmap says so rather than picking one. Three candidates, none free:

| name | for | against |
|---|---|---|
| `abs` | the mathematical spelling; what the implementation uses today | collides with the lattice absolute value that `\|·\|` denotes in Lean, so an unqualified `abs A` reads as the wrong object in any file with both in scope |
| `modulus` | no collision; matches `ContinuousLinearMap.modulus`, the rectangular complex construction already named that way | two names for one notion unless both are renamed, and `modulus` is less standard in the matrix-analysis literature this roadmap cites |
| `operatorAbs` | unambiguous, and a distinctive token, so adopting whatever wins is one mechanical replacement | nobody's first choice; reads as a placeholder, which is what it is |

`operatorAbs` is what the roadmap and `Suggested.lean` currently carry, on the grounds that
a placeholder that is trivially replaceable costs less than a premature decision. **This is
worth putting to the Tau Ceti reviewers explicitly** — it is exactly the kind of naming call
a roadmap review exists to make, and the answer also determines whether
`ContinuousLinearMap.modulus` keeps its name.

Whatever is chosen, the derived lemmas follow it (`norm_*_apply`, `ker_*`, `*_mul_self`), and
the two constructions need the agreement theorem either way.

### 2. Moore–Penrose: predicate or four hypotheses — **decided, worth flagging**

The roadmap asks for a named `IsMoorePenroseInverse` predicate rather than four anonymous
hypotheses repeated at each use. Mathlib has neither a Moore–Penrose inverse nor such a
predicate today; worth re-checking Zulip and open PRs immediately before submitting, and
worth saying in the PR that the shape is proposed rather than copied.

### 3. Roadmap ownership of the spectral-band approximation numbers — **decided**

Three modules computing approximation numbers of spectral bands were the sole reason the
spectral-theory roadmap looked like a consumer of the operator-ideal roadmap. Ownership
follows the mathematics: `OperatorIdeals` owns them, and `SelfAdjointSpectralTheory` depends
only on the foundations. Reviewers may reasonably ask why an operator-ideal result is
proved through the unbounded spectral measure; the answer is that the proof runs through the
spectral theory while the statement does not, and that is the right cut.

### 4. The domain-aware `sin Θ` statement — **repaired, worth surfacing**

The earlier draft of this milestone quantified over an arbitrary unconstrained sine
operator, which makes the inequality false by scaling, and carried a gap constant no field
constrained. The current statement constructs the directed sine operator from the problem
data and constrains the gap by a spectral separation between the two blocks. This is the
milestone most worth an adversarial read from a reviewer.

### 5. Ideal-gauge form of the `sin Θ` conclusion — **open**

The perturbation roadmap states its headline in the operator norm. Its natural form
quantifies over a Ky Fan dominant symmetric ideal gauge from `OperatorIdeals`, with
membership of the sine operator in the ideal as part of the conclusion. That form cannot be
written in `Suggested.lean` without restating the gauge interface there, so the README
states it in prose. Decide whether the roadmap should carry the gauge-valued signature.

### 6. Suggested-signature files and `sorry` — **check upstream expectations**

Upstream's convention is that `Suggested.lean` files carry `sorry` bodies and are read as
suggested forms. This repository additionally builds them as a Lean library so a signature
that stops elaborating is a build failure. Confirm that the upstream build accepts the same
arrangement for a family of six.

---

## Checklist before opening

- [ ] re-run the family checks (`--roadmaps`, `--check`, `lake build ForTauCetiRoadmap`)
- [ ] re-search Zulip and open Mathlib PRs for each roadmap's "what Mathlib already has"
      section; the singular-value and pseudoinverse areas move
- [ ] confirm the licence and coordination position on the Spectra-derived material
- [ ] register an intention issue upstream and claim it, per that repository's README
- [ ] decide item 1 above, or decide to ask
