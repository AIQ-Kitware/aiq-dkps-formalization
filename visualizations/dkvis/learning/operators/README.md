# Accepted operator-theory foundations

Three lectures connect central accepted Tau Ceti results to reusable proof ideas.
They assume basic linear algebra; each gives motivation, a short historical
connection, a local notation refresher, a proof or construction, an example, a recap,
and paired mathematical/Lean facts, one Lean statement per card. Numerical
considerations follow as an optional bonus slide. Two multiple-choice questions close each
lecture, with a thinking interval before the explained answer.

| Lecture | Proof idea | Prerequisites |
| --- | --- | --- |
| `operators-minmax` | A forced subspace intersection proves Courant–Fischer; uniform Rayleigh bounds imply Weyl stability. | Projections, singular-value/operator norms |
| `operators-polar` | Equal output norms construct the canonical partial isometry, including a nontrivial kernel. | Projections, singular values |
| `operators-sylvester` | Ordered spectral separation gives exponential decay and an integral inverse estimate. | Min-max, matrix exponentials |

From `visualizations/`:

```bash
make operators                         # Manim slides, handouts, speech text
make video DECK=operators-sylvester TTS_PROFILE=crall
make lectures-video TTS_PROFILE=kokoro  # the whole indexed library
```

## Acceptance and provenance

The maintained [contribution census](../../../../dev/tauceti/dkps-upstream-contribution-census.md)
and [publication direction](../../../../dev/publication-direction-dkps-to-transport-2026-10-27.md)
are the basis for this selection. Acceptance here means integration into Tau Ceti,
not mathematical novelty or ownership of all implementations on the roadmap.
These lectures do not assert that sine-theta logically implies matching.

The exact source signatures used by the new companions were inspected at the
root's Tau Ceti pin `85f3eb5579df5ca44ba8cd0921d614b41ab72174`.

- **Courant–Fischer and Weyl:** `TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`,
  accepted [PR #13599](https://github.com/TauCetiProject/TauCeti/pull/13599).
  This is a documented DKPS proof adaptation. The decreasing, zero-based
  eigenvalue convention is explicit in the lecture and companion.
- **Absolute value and polar decomposition:** `Polar/Finite.lean` and
  `Polar/Bounded.lean` under `Analysis/InnerProductSpace`, with positive-square-root
  infrastructure. The census records accepted PRs #13940, #16086, #16450 and
  #16523, and bridge #20358. The polar implementations are independent work,
  not DKPS ports. The displayed Lean examples specialize the finite API;
  bounded Hilbert-space scope is explained separately. The canonical factor is
  zero on the kernel; a numerical routine's unitary extension may differ there.
- **Sylvester:** `TauCeti/Analysis/InnerProductSpace/Sylvester.lean` supplies the
  displayed bounded API, accepted independently in [PR #15457](https://github.com/TauCetiProject/TauCeti/pull/15457).
  The distinct domain-aware `LinearPMap/Sylvester` theory, accepted in
  [PR #18917](https://github.com/TauCetiProject/TauCeti/pull/18917), is an explicit
  DKPS adaptation. The latter's unbounded scope is not attributed to the simple
  matrix examples or the displayed bounded norm lemma.

The classical names identify mathematical lineage. See each transcript's linked
SciPy reference for computational conventions. These are three selected central
foundations, not an exhaustive tour of the operator roadmap.

## Code and companions

`model.py` contains the numerical examples, without Manim dependencies.
`minmax.py`, `polar.py`, and `sylvester.py` contain the scenes. The numbered source
folders are resolved from `lectures/index.yaml`; each has `lecture.md`,
`facts.lean`, and `quiz.yaml`. The shared Lean slide reads actual code from its
companion, and repeats its symbolic statement beside it. See
[validation notes](../../../lectures/LEAN_FACTS.md) for the available build cache.
