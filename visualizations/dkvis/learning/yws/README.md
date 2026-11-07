# Yu–Wang–Samworth: a population-gap perturbation theorem

Lecture **003875**, stable ID `yws`, deck **`yws-population-gap`**.
The 27-scene presentation states and proves both conclusions of Theorem 2,
explains the population-coordinate block structure, and derives the corrected
rectangular Gram-matrix extension. It includes two checked Lean applications,
a numerical bonus slide, and four study questions. The complete transcript is
about 3,200 words, approximately 22 minutes at 150 words/minute before animation
and thinking pauses.

The technical route assumes familiarity with symmetric eigenproblems,
orthonormal frames, Frobenius and operator norms, and principal angles. These
objects are recalled locally. Suggested earlier lectures are sine theta,
singular-value norms, and min–max/Weyl. The history lecture supplies context but
is not a mathematical prerequisite.

From `visualizations/`:

```bash
make slides DECK=yws-population-gap
make text DECK=yws-population-gap
make video DECK=yws-population-gap TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

It is part of `make lectures-video`. Restart an existing library server to load
the new registration. Generated outputs remain ignored and use the numbered
public basename `003875_yws-population-gap`.

- [Transcript](../../../lectures/003875_yws/lecture.md)
- [Mathematical and Lean correspondence](../../../lectures/003875_yws/sources.md)
- [Complete Lean companion](../../../lectures/003875_yws/facts.lean)

Validate the companion from the repository root with:

```bash
lake env lean visualizations/lectures/003875_yws/facts.lean
```

If the imported YWS module is absent or was compiled with an older toolchain,
fetch the pinned Mathlib cache and build `YuWangSamworth2015.Symmetric.Theorem2`
first. The companion applies existing results; it changes no library theorem.

`model.py` supplies the published mixed-gap example and a rotating 2D example.
Their tests check the eigen-equation, residual, norms, and displayed bounds.
The proof scenes use entrywise Frobenius estimates so viewers do not need to
learn vectorization or Kronecker products merely to understand this proof.
