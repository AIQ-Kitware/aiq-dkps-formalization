# Compact presentation of the matching proof

The author requested an independent, smaller talk for an audience already
familiar with the standard background. This is `matching-proof-talk`, not a
revision or subset of the 40-slide `matching-proof` study deck. Its thirteen proof
scenes, attributed cover, local setup, optional numerical bonus, and review
questions are composed in `dkvis/decks/matching_talk.py`. The frozen Kitware talk,
comprehensive deck, and existing study materials retain their scenes and order.

Assume principal angles, singular-value norms, orthogonal spectral
decompositions, the two-projection decomposition, and compact variational
arguments. Define the new proof-specific objects locally. Explain the
gradient/conjugation construction, common invariant blocks, phase reduction,
both matching inequalities, and uniform continuation. Do not turn the talk into
a glossary or silently assume the minimizer preserves principal planes.

The script is `lectures/README.md#matching_proof`. Its motivating lines explain
the purpose of the inference; its spoken text assumes the background. The
bottom progress line keeps stationarity, blocks, local costs, matching, and the
endpoint in view. Animations show the gradient-level intersections, the closed
coordinate plane, the comparison with an attainable phase edge, and matching
selection. They do not assert a monotone feasible matrix path from the phase
comparison.

| Scenes | Argument |
| --- | --- |
| T00–T01 | State the attained unrestricted real minimum; choose a smooth minimizer and identify the structural lower-bound problem. |
| T02 | Feasible right variations and the trace gradient imply zero diagonal gradient compressions. |
| T03–T05 | Positive gradient levels give a complex structure and at most two phases; the phase projection and conjugation yield real two/four-dimensional blocks. Include endpoint eigenvalues and zero gradient. |
| T06–T09 | Solve the full local fibers, establish the phase rectangle and attainable edge, and account for negative determinant and zero-angle partners. |
| T10–T11 | Prove both matching inequalities; pass minimum values to the trace norm and evaluate the block weights. |
| T12 | Maximum-weight matching and the explicit three-angle attainer. |

The proof follows the current matching section in
`papers/dk_formalization_journal/formalization_enabled_extension.tex` and its
six steps. The endpoint is `RealNuclearMatching.lean`; the supporting files
include `SchattenRealStationarity.lean`, `SchattenGradientSpectrum.lean`,
`SchattenRealDecomposition.lean`, `RealFourPositive.lean`,
`RealFourPhaseRectangle.lean`, and `RealFourOptimization.lean` under
`DavisKahan/FiniteDimensional/DirectRotation/`. No new theorem or mathematical
priority claim is made. The complex coordinates are on the original real
space. The conclusion is a finite real matching minimum and an attainer,
without an all-minimizer classification or infinite-dimensional claim.

Run `make matching-talk` for the standalone HTML, PDFs, and narration exports.
`make matching-talk-text` needs no render or TTS server. The existing video
pipeline accepts `--deck matching-proof-talk`; `make matching-talk-video`
uses the same editable profiles, ignored `.env`, audio safeguards, caches,
and timing logs, with separate deck output directories. No audio is requested
when building the slides or text.
