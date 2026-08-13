# Proof obligations

Numbering below is the **published** Biometrika numbering, checked against the
article on 2026-08-13: Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1,
equations (1)–(4), appendix equations (A1)–(A8).  The 2014 arXiv preprint shares
one counter and numbers the last three Corollary 3, Theorem 4 and Lemma 5, which
is what many Lean declaration names in this library still spell.  The census
records the translation table under gap `preprint-numbering-aliases`; the names
are not being changed because `comparator/*.json` pins some of them.

## Numbered paper results

Every numbered result has a theorem surface, and since 2026-08-13 every one of
them is stated at the printed generality:

* Theorem 1, in unitarily invariant, Frobenius and operator-norm form;
* Theorem 2, both conclusions, for **arbitrary ordered eigenframes** — the
  paper's `V̂` is any orthonormal family with `Σ̂ v̂ⱼ = λ̂ⱼ v̂ⱼ`, with no sample
  eigengap, so a repeated sample eigenvalue leaves it undetermined and the
  theorem must quantify over the choice;
* Corollary 1, both displays, including the literal real sign-aligned bound
  `‖v̂ − v‖ ≤ 2^{3/2} ‖Σ̂ − Σ‖_op / Δⱼ` under `v̂ᵀv ≥ 0`;
* Theorem 3, right and left, in the corrected form (see below);
* Lemma A1, both halves.

## Additional completed source material

* the sharper residual-numerator forms of Theorem 2 that the paper says its
  proof establishes — `‖sin Θ‖_F ≤ ‖V̂Λ − ΣV̂‖_F / Δ` and the aligned form with
  the factor `2^{1/2}`;
* corrected equation (4), with the printed polynomial refuted;
* the refutation of Theorem 3's printed rank-boundary convention;
* direct right and left rank-one singular-vector corollaries;
* exact operator/Frobenius minimum and aligned-frame constants;
* all three Section 2 sharpness constructions, including the *published*
  middle-block one;
* the Section 1 numerical illustration that Theorem 1's separation `δ` can
  vanish, together with the operator-level population gap at the same block;
* the deterministic content of the Section 3 diagnosis: the Weyl recovery of a
  mixed gap, the fact that on the event it needs it reproduces Theorem 2's
  constant, and a witness that the event can fail.

## Source defects recorded

Two printed statements in this paper are false as printed, and both are machine
checked in both directions.

1. **Equation (4).** The printed right-hand side omits a square on
   `2 − ‖v̂ − v‖²`.  Corrected identity and counterexample in
   `Symmetric/AngleIdentity.lean`.
2. **Theorem 3's convention `σ²_{rank(A)+1} := −∞`.** Found 2026-08-13; no
   erratum located.  Taking `s = rank(A)` makes the printed denominator
   infinite, so the printed bound asserts that the sample and population right
   singular subspaces coincide — and they can be orthogonal.  Refuted in
   `Rectangular/RankBoundary.lean`.  The repair is the convention the paper's
   own proof uses: `σ²_{q+1} := −∞` at the **ambient** dimension, with
   `σ_j := 0` for `min(p,q) < j`.  That is exactly the intrinsic gap of `A⋆A`
   that this library's theorems carry, so no new theorem was needed.

## Remaining non-numbered source-fidelity work

* optional wrappers whose hypotheses are literal contiguous matrix indices
  `r..s` with the gap read off as `min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`, rather
  than an index embedding plus an ordered eigenframe;
* migrate reusable results from this completion lane into canonical modules.

None of these is a gap in a numbered result.

## Build guard

`FinishYuWangSamworth` **is** a default build target: it joined `defaultTargets`
on 2026-08-02, so `lake build` compiles everything here and a regression cannot
land unnoticed.  The library also carries `warningAsError` under the Mathlib
standard linter set, matching the option set Tau Ceti's own `lean_lib` applies.

## Census state (2026-08-14)

`dev/yu-wang-samworth-2015-full-source-census.json`: **24 of 24 rows proved in
the default build.**  The two rows that were short on 2026-08-13 are closed:
the Section 1 numerical illustration is formalized, and the Section 3 row —
exposition, and still not proof debt — now carries the compiled deterministic
core of its claims.  Two gaps were retired with them, `section1-toy-example`
and `published-sharpness-example`.

Closing the published sharpness example needed new mathematics rather than new
bookkeeping.  Its block sits in the *middle* of both spectra, so the
branch-selection hypothesis cannot come from any "leading `d` eigenvectors"
argument, and the missing foundation was the position of an arbitrary
eigenvalue level set inside Mathlib's sorted eigenbasis:
`LinearMap.IsSymmetric.eigenvalues_level_eq_Ico` (every level set is the
contiguous index range `[m, m+d)`), `TauCeti.card_filter_lt_eigenvalues_basisDiagonal`
(for a diagonal operator `m` is read off the coefficient list), and
`TauCeti.correspondingEigenblock_eigenvalueLevel`, of which the earlier
top-eigenspace constructor is now the case `m = 0`.

The census was rekeyed to the published numbering on 2026-08-13 and three of its
judgements were corrected in the process.  `YWS-T2-sinTheta`,
`YWS-T2-alignedBasis` and `YWS-C1-rankone` had been marked `compiled_exact`
while the only statement carrying them assumed `CorrespondingEigenblock`, which
is strictly stronger than the paper's hypothesis at a degenerate **sample**
eigenvalue — the exact case removing the sample eigengap exists to cover.
`YWS-T3-right` and `YWS-T3-left` are now `compiled_corrected` rather than
`compiled_exact`, because the printed convention they were claimed to match is
false.  A census that reports `compiled_exact` for a statement it has not
compared clause by clause with the printed one is worth less than no census.
