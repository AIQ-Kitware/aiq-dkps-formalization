# Davis--Kahan 1970, Section 8 — complete

Closed 2026-08-07 by Claude Opus 5.  This file used to be a campaign handoff
listing Section 8's open obligations; every one of them has landed, so it is now
a short state record.  **Do not read the git history of this file as a worklist.**

## State

`dev/davis-kahan-1970-full-source-census.json` rows **DK-8.1-thm** and
**DK-8.2-thm** are `compiled_exact` / `proved_in_build`, with no blocker.  The
`section8-source-hypotheses` blocker is removed: it described caller-supplied
continuation witnesses, contour smallness constants, spectral orientations and
half-gap bridges, none of which appears in any Section 8 source statement any
more.

**Remaining Section 8 mathematical obligations: none.**

## Where things are

| Layer | Module |
| --- | --- |
| Theorem 8.1 core, upstream of the analytic layer | `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean` |
| Low-level facade (imported *by* Frontier) | `DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean` |
| Part (i), both blocks | `DavisKahan/Frontier/Section8.lean` |
| Parts (ii), both blocks, and the lower-block objects | `DavisKahan/Frontier/Section8PartII.lean` |
| Part (iii), both blocks | `DavisKahan/Frontier/Section8PartIII.lean` |
| Theorem 8.2, perturbation alternative | `DavisKahan/Frontier/Section8Perturbation.lean` |
| Krein completion | `DavisKahan/Frontier/Section8Krein.lean` |
| Theorem 8.2, residual alternative | `DavisKahan/Frontier/Section8Residual.lean` |
| Eigenvalue/angle source dictionary | `DavisKahan/Frontier/Section8SourceDictionary.lean` |
| Theorem 8.2 under the standing convention (1.5) | `DavisKahan/Frontier/Section8SourceTheorem82.lean` |
| **Production facade** | `DavisKahan/Frontier/Section8SourceSurface.lean` |
| **Audit of the capstones** | `DavisKahan/Frontier/Section8Audit.lean` |
| Audit of internal bridges only | `DavisKahan/Sources/DavisKahan1970/Audits/Section8.lean` |

The production facade is downstream of Frontier and cannot live under
`Sources/`: Frontier imports the low-level facade, so the reverse import would
be a cycle, and `check_library_structure` rule 4 requires every
`DavisKahan.Sources.*` module to be reachable from the curated `DavisKahan`
root, which the Frontier layer is not.  Its declarations nevertheless land in
`TauCeti.DavisKahan1970.Section8`, and it is reachable from `DavisKahan.All`
through `DavisKahan.Frontier.All`.

## The printed section, claim by claim

| Printed claim | Declaration |
| --- | --- |
| Opening: `‖sin Θ₀‖₁ ≤ 1/2` "is exactly `Θ ≤ π/6`" | `maximalAngle_le_pi_div_six_iff`, `arcsin_one_div_two` |
| 8.1: `Θ ≤ π/4` iff `Λ₁ ≥ α+δ`, `Λ₀ ≤ α` | `theorem8_1_source_characterization` |
| 8.1: such a `Q` always exists | `theorem8_1_source` (and it is *unique*: `theorem8_1_source_uniqueness`) |
| 8.1(i) upper: `A₁ - α ≤ C₁(Λ₁-α)C₁` | `theorem8_1_upperCompressionRepulsion_source` |
| 8.1(i) "similar relation for `A₀`" | `theorem8_1_lowerCompressionRepulsion_source` |
| 8.1(ii) upper: `α_k - α ≤ ‖C₁‖₁²(λ_k-α)` | `theorem8_1_upperApproximationRepulsion_source`, `..._angle_source` |
| 8.1(ii) "similar relation for `Λ₀`" | `theorem8_1_lowerApproximationRepulsion_source`, `..._angle_source` |
| 8.1(ii) "natural infinite-dimensional extensions" | the same theorems: the Weyl step used is dimension-free, so neither carries a finite-dimensionality hypothesis |
| 8.1(iii) upper, every symmetric gauge | `theorem8_1_upperSymmetricGaugeRepulsion_angle_source` (from the stronger `theorem8_1_upperWeightedWeakMajorization_source`) |
| 8.1(iii) "similar relation for `Λ₀`" | `theorem8_1_lowerSymmetricGaugeRepulsion_angle_source`, `theorem8_1_lowerWeightedWeakMajorization_source` |
| 8.2: `δ‖sin 2Θ‖ ≤ 2‖H‖` | `theorem8_2_sinTwoTheta_perturbation_source_complex` |
| 8.2: `δ‖sin 2Θ₀‖ ≤ 2‖R‖` | `theorem8_2_sinTwoTheta_residual_source_complex` |
| 8.2: `Θ < π/4` from `‖H‖₁ < δ/2` | `theorem8_2_perturbationHalfGap_source_maximalAngle_lt` |
| 8.2: `Θ < π/4` from `‖R‖₁ < δ/2` (Krein) | `theorem8_2_residualHalfGap_source_maximalAngle_lt` |
| 8.2, whole printed statement | `theorem8_2_source_complex` |

Equations (8.1) and (8.2) are steps inside the printed proof of the
quarter-angle bound.  They are not separately formalized because the repository
proves that bound by a *stronger* route: `theorem8_1_canonicalBranch` gives the
**strict** bound `IsQuarterAcute P Q` in arbitrary dimension, whereas the printed
argument is finite-dimensional with "the infinite-dimensional case follows by
approximation".

The section's closing sentence — "the `sin 2θ` theorem can be extended to the
case `dim 𝓧(E₀) < dim 𝓧(F₀)`, similarly to Theorems 6.1 and 6.3.  No
corresponding extension of the `tan 2θ` theorem is known." — has two halves.
The second is an open question, not proof debt.  The first is an
unequal-dimension extension of the **`sin 2θ` theorem**, asserted without proof;
it is a claim about a Section 2 / Section 7 theorem, not about Theorem 8.1 or
8.2, and it is recorded on the census row `S2-sin-two-theta`, which is
`compiled_specialization` for exactly this kind of reason.  It is not a
Section 8 obligation and was deliberately left out of scope for this campaign.

## The two conventions, and one source finding

**Eigenvalue ordering.**  The repository indexes approximation numbers and
principal cosines *decreasingly*; the paper prints `λ₁ ≤ λ₂ ≤ ⋯` increasing and
`θ₁ ≥ θ₂ ≥ ⋯` decreasing, so its `cos²θ_k` is increasing and the printed
right-hand side pairs `k`-th smallest with `k`-th smallest.  That is the same
multiset of products as pairing largest with largest.  The reindex is compiled,
not asserted: `theorem8_1_{upper,lower}SymmetricGaugeRepulsion_angle_rev_source`
apply `Fin.rev` to **both** sides at once and are the printed increasing reading.

**The `Θ` convention in Theorem 8.2, and why the directed theorem survives.**
`Θ` is only defined when Section 1's equation (1.5) holds — equal dimensions of
both subspaces and both complements — because it is built from the entries of a
unitary satisfying (1.4).  In its finite form (1.5) is `finrank P = finrank Q`,
and `subspaceGap_eq_directedGap_of_finrank_eq` then converts the directed
conclusion the printed argument actually delivers into the printed symmetric
one.

**CORRECTED 2026-08-11 (Claude Opus 5, coordinator).  THE PARAGRAPH THAT STOOD
HERE CLAIMED A COUNTEREXAMPLE THAT IS NOT ONE, AND THE PAPER ITSELF SAYS SO.**

It read: "Under the **cardinal** form of (1.5) the printed conclusion is
*false*.  Take `H := E × E` … `Q := E × 0`, `P := span{e₁, e₂, …} × 0`.  Every
printed hypothesis of Theorem 8.2 holds, both halves of (1.5) hold as cardinals,
and yet `‖P_P - P_Q‖ = 1`."

The configuration does **not** satisfy every printed hypothesis, because it
violates the standing assumption (3.5).  Against
`non-distributable/davis-kahan-1970-modernized-transcription.tex`:

* (3.5) is stated at **L901–908** (Proposition 3.2) as
  `dim(P𝓗 ∩ Q̃𝓗) = dim(P̃𝓗 ∩ Q𝓗)` — equality of the two *crossed* intersection
  dimensions.
* **L961: "We shall assume (3.5) as well as (1.5) except where stated
  otherwise."**  So (3.5) is a printed *standing* hypothesis from Section 3
  onward, and is therefore in force for Theorem 8.2.
* In the configuration above `P𝓗 ∩ Q̃𝓗 = 0` while `P̃𝓗 ∩ Q𝓗 = span{e₀} × 0`.
  **0 ≠ 1, so (3.5) fails.**
* The paper's own Remark after Proposition 3.2 (**L911–916**) exhibits the same
  phenomenon — with the two subspaces interchanged — as its illustration that
  (3.5) *fails* under the cardinal reading of (1.5): "`P Q̃` is the projector
  upon the subspace of sequences with `aₙ=0` for `n≠0`, whereas `P̃ Q = 0`; so
  (3.5) fails."

So the paragraph reproduced the paper's own (3.5)-failure example and labelled
it a counterexample to a theorem that assumes (3.5).  This is audit
disagreement 19, now upheld and closed.

**WHAT SURVIVES, on better grounds.**  The finite form of (1.5) is still the
right reading, but because of the Remark's *positive* justification rather than
any claim about the cardinal form: "Since we are assuming (1.5), (3.5) will hold
automatically if either `dim P𝓗` or `dim P̃𝓗` is finite."  The finite form is
precisely the regime in which the standing (3.5) is free.  Whether the printed
conclusion holds under the cardinal form together with (3.5) is **not settled
here** and must not be asserted either way.  `theorem8_2_branch_source_directed_complex`
— the strongest statement from the explicit printed hypotheses alone, with no
dimension convention — is kept and must not be collapsed into the symmetric one.

The paper's configuration is no longer documented-only: it is machine-checked as
`Section3.directedGap_asymmetric_coordinateHalfSpace` with
`coordinateHalfSpace_dimensions_agree` and
`not_crossedDefectsEquivalent_coordinateHalfSpace`
(`DavisKahan/Frontier/Section3BilateralShift.lean`).

## Gates at the close of the campaign

* `lake build` — 9481 jobs, green.
* `lake build DavisKahan.Experimental Challenge FinishTanTwoTheta` — 9407 jobs, green.
* census — CLEAN, 48/48 rows agree with the build; declaration probe 257/257.
* `check_declaration_name_drift.py` — OK, 0 findings.
* `check_dependency_layers.py` — 4 violations, all `SpectralTheory/FormMethod/Beam*`
  importing Section 9 facades.  Pre-existing baseline, untouched by this campaign.
* `check_library_structure.py` — rule 3 reports 16 violations, unchanged from the
  baseline.  It is the standing worklist of `Experimental/` modules that have
  become admission-free and ought to move out.
* `DavisKahan/Frontier/Section8Audit.lean` — 42 targets, every one
  `[propext, Classical.choice, Quot.sound]`.
