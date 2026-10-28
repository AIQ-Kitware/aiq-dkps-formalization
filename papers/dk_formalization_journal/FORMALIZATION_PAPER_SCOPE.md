# Paper scope: Davis--Kahan formalization first

The submission under `papers/dk_formalization_journal/` is a **formalization
paper**. Its scientific spine is the source-level verification of the 1970
Davis--Kahan work, the required reusable operator theory, and the checked
counterexample to printed Proposition 4.4.

For the 28 October author-review decisions and the evidence index, read
[AUTHORING_NOTES.md](AUTHORING_NOTES.md). Those decisions govern the next
manuscript correction pass; this document records scientific scope.

The companion paper project `papers/optimal_spectral_transport/` preserves
the previous 27 October mathematics-first manuscript and all the associated
transport sections. It is intentionally still a combined working draft and
needs its own separate editorial revision before any submission. Do not erase
its proofs, related-work discussion, or provenance when shortening this paper.

## Publication narrative and boundaries

- Formalized the original Davis--Kahan theory and its mathematical
  dependencies in Lean 4. The reviewed target set is 29 source results:
  28 proved with the reviewed scope, and printed Proposition 4.4 refuted.
- Formalized foundations include principal angles, direct rotations,
  operator ideals, Sylvester estimates, and unbounded self-adjoint calculus.
  Some original donor work was subsequently upstreamed into Tau Ceti.
  A `TauCeti.*` dependency therefore does not by itself prove independent
  upstream origin. Conversely, the roadmap also contains independent
  contributions. Use the donor / accepted-PR provenance records to attribute
  adaptations, including the Spectra ancestry of some spectral machinery.
- The original 1970 complex phase nonminimality mechanism is classical.
  The real four-dimensional counterexample is its realification; it refutes
  the printed real small-angle claim but not the main perturbation theorems.
- The new real nuclear weighted-matching theorem is separately Lean-verified
  and demonstrates further work enabled by the foundation. It is not a
  corollary of the Davis--Kahan sine-theta inequality. Its publication
  priority remains to be determined against operator-theory literature.
  Use trace-norm terminology in the manuscript. Support any qualified novelty
  statement with the precise comparison in the author evidence files.
- Do not expand the formalization manuscript into an exhaustive treatment
  of the new complex spectral-penalty, Charbonnier, infinite-dimensional
  transport, and optimizer-classification theory. Use the companion paper.
- Formal kernel checking and mathematical fidelity to the source remain
  repository obligations. State the source-result selection criterion and
  mathematical coverage in the article; keep review procedures in the author
  evidence files. The included correction and follow-on theorem must have
  enough explanation for this paper to be assessed on its own, without sending
  readers to a separate working manuscript.

## Open questions for the research and publication agents

1. Compare the unrestricted real matching reduction with the exact statements
   in the minimal-distortion literature. Which hypotheses and conclusions
   coincide, and which require additional mathematics?
2. Can the global matching lower bound be explained concisely to a
   mathematical reader with an ordinary conventional proof? This proof is
   needed to explain the included result. Keep its exposition proportional to
   this article's formalization focus.
3. Before using a sorting refinement, inspect the current matching and
   adjacent-pair Lean declarations. Historical plans are not evidence that a
   result remains unproved, and additional proved results do not automatically
   belong in this article.
4. Which upstream Tau Ceti declarations were adapted from DKPS donor files,
   which were independently re-proved, and which descend partly from Spectra?
   Preserve explicit credit at the theorem-family level.
5. What evidence shows the published correction has independent scientific
   relevance beyond the falsity of Proposition 4.4? Do not manufacture
   consequences for the sine-theta bounds or downstream applications.
6. What can a reader reproduce from the code and result mapping? Report the
   actual mathematical statements and the exact selection criterion; link to
   the artifact for declaration mappings, build details, and review evidence.

Further automated theorem proving should prioritize these concrete
questions rather than inflating the formalization paper with new results.
