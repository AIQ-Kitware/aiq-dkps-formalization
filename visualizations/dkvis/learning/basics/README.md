# Before the series: a mathematics refresher

Lecture **000010**, deck `prereq-basics`, is a short review and readiness map.
It assumes school algebra and is aimed at viewers who have met elementary
linear algebra and calculus before. It helps a new learner identify what to
study before following the later lectures; it does not compress a first course
into one video.

The twenty scenes include a short cover, an orientation, eleven topic cards,
a readiness recap, symbolic facts, two Lean correspondences, an optional
numerical bonus, and two answered multiple-choice questions. Topics include
real/complex scalars, vectors, matrix action, span/basis/dimension, kernel/range,
inner products, orthogonality, adjoints, symmetry/unitarity, trigonometry,
eigenvectors, norms/trace, limits, derivatives, and integrals. Matrix
exponentials and the later series topics are signposted rather than assumed.

From `visualizations/`:

```bash
make slides DECK=prereq-basics
make text DECK=prereq-basics
make video DECK=prereq-basics TTS_PROFILE=crall SKIP_RENDER=1
```

The transcript, quiz, provenance, and checked `facts.lean` companion live in
[`lectures/000010_basics/`](../../../lectures/000010_basics/lecture.md).
The Lean cards apply existing Mathlib facts: `real_inner_self_eq_norm_sq` and
`IsLocalMin.hasDerivAt_eq_zero`. No new library declarations or paper completion
obligations are introduced. The complex inner product uses conjugation in the
first argument, matching Mathlib's convention.

Historical context is Cayley's *A Memoir on the Theory of Matrices* (1858),
with primary links in the transcript. It gives a historical landmark, not a
priority claim for all the mathematical ideas reviewed here.
