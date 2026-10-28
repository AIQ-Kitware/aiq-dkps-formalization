# Optimal spectral subspace transport (preserved working paper)

This directory preserves the mathematics-first combined journal source from
27 October 2026 **before** the Davis--Kahan manuscript was refocused.
The prior `paper.tex` and its mathematical sections remain together and
should compile with the included `Makefile` and bibliography. All source
material on the two-parameter complex smoothed-power theory, real matching,
nuclear endpoints, Charbonnier optimization, infinite-dimensional ideal
lifts, optimizer structure, and related-work attribution is retained here.

**Editorial status:** This is a preservation fork of the combined paper,
not a submission-ready standalone spectral-transport article. Its original
formalization sections remain in the preserved draft. A later revision may
separate those sections, but should retain all mathematical arguments,
provenance, and proof boundaries when doing so.

The primary Davis--Kahan *formalization* article is now
[`../dk_formalization_journal/paper.tex`](../dk_formalization_journal/paper.tex).
The new theorem statements are already formally verified in the main Lean
repository; the historical priority of some exact transport classifications
is still an active research question.

Build from this repository root with:

```bash
make -C papers/optimal_spectral_transport paper
```
