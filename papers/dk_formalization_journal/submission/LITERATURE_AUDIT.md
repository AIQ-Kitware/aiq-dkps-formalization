# Proposition 4.4 — scholarly attribution summary

23 October 2026. This is the editorial summary of the source-level study in
`../PROPOSITION_4_4_LITERATURE_MAP.md`, which gives original page locations,
verification levels, and mathematical comparisons. The work establishes
important antecedents, not a proof of first-publication priority.

## Primary mathematical sources

| Source | Verified relevance | Manuscript use |
|---|---|---|
| Davis--Kahan, *The Rotation of Eigenvectors by a Perturbation. III*, SIAM J. Numer. Anal. **7** (1970), 1–46, doi:10.1137/0707001. | §4, Example 4.2 exhibits complex phase improvement of trace displacement. Proposition 4.3 supports squared displacement; Proposition 4.4 wrongly asserts universal full-displacement minimization for real angles `<= pi/3`. The invalid sum step occurs in equation (4.3). | Credit the original phase mechanism; identify precisely which printed proposition fails and which preceding theorem survives. |
| Bolotnikov--Li--Rodman, *Minimal distortion problems for classes of unitary matrices*, ELA **8** (2001), 26–46, doi:10.13001/1081-3810.1058. | Theorem 3.1: related Q-norm minimization; Lemma 3.3: failure for Schatten `1 <= p < 2`; Theorem 4.2: Frobenius minimizers. | Do not call general nonminimality or Q-norm optimality newly discovered. Do not mistake Frobenius for trace-minimum classifications. |
| Qiu--Zhang--Li, *Unitarily invariant metrics on the Grassmann space*, SIAM J. Matrix Anal. Appl. **27** (2005), 507–531, doi:10.1137/040607605. | §5, item 3 repeats the `pi/3` full-displacement assertion; its logarithmic/minimal-metric results have a different objective. | Identify the repeated assertion without suggesting that the paper's Grassmann metric theorems are false. |
| Zhang--Qiu, *On the angular metrics between linear subspaces*, Linear Algebra Appl. **421** (2007), 163–170, doi:10.1016/j.laa.2006.08.015. | Principal-angle singular values of `P-Q` (printed p. 165), including the doubled sine list. | Cite the classical singular-value ingredient for projection lower bounds and sharp displacement. |
| Zhang--Qiu, *From subadditive inequalities of singular values to triangle inequalities of canonical angles*, SIAM J. Matrix Anal. Appl. **31** (2010), 1606–1620, doi:10.1137/09074841X. | §4 (p. 1615) acknowledges trace-norm nonminimality in general, but does not specifically refute the real short-angle proposition. | Explicitly recognize preexisting awareness of nonminimality, not claim novelty for it. |

Bhatia, *Matrix Analysis* (Springer, 1997), supplies standard pinching and
symmetric-gauge machinery; see the full map for other adjacent results,
including operator-norm extremal theorems.

## Consequences now formalized

For finite-dimensional real/complex spaces, any UI seminorm `N`, and any
admissible map `W`, the projection-distance lower bound is
`N(P-Q) <= N(I-W)`. For acute pairs with maximum angle `alpha`, the
canonical direct rotation satisfies

`N(I-R) <= sec(alpha/2) N(P-Q) <= sec(alpha/2) N(I-W)`.

The constant is sharp across all UI norms and dimensions at each positive
acute angle, attained by the real four-dimensional trace example; it is
not the best constant separately for Q-norms. That real example globally
minimizes trace displacement with value `4 sin(theta)`. These are proven
in Lean in `ProjectionDisplacement.lean`, `SharpDisplacement.lean`, and
`TraceOptimality.lean` in the October 23 source snapshot. The complex
exact-minimum theorem is verified for supplied principal-plane models and
their coordinate transports, not for arbitrary complex pairs.

## Priority boundary

The project provides a source-faithful formal refutation within the printed
real short-angle hypotheses, an exact diagnosis of equation (4.3), and
formal quantitative repairs. The real example is the realification of the
1970 complex phase mechanism; the sharp factor follows from established
singular-value and pinching ingredients. No original-source paper examined
explicitly stated the precise real correction or the sharp all-norm ratio,
but absence in the searched material is not proof of historical priority.
Do not claim first discovery of trace-norm failure, the phase mechanism,
Q-norm minimality, or the general complex trace formula.
