# Lemma 6.3 promotion scratch lane

Base: `7f9f562`.

At the base revision this scratch work was isolated from the active spectral,
continuation, polar, rectangular-ideal, and Section 8 source-assembly files.

## Mathematical finding

The two declarations currently in `Experimental/Frontier/Lemma63.lean` use

```text
K * P = Q * K
```

rather than the source block equation

```text
K * P = Q * K * P.
```

The stronger equation immediately gives

```text
Q * K * (1-P) = K * P * (1-P) = 0.
```

Consequently, the current frontier conclusions are true without the rank or
near-saturation hypotheses, but they do not represent the quantitative lemma
from the paper.

The scratch module supplies both tracks:

1. complete zero-leakage proofs matching the current frontier signatures;
2. corrected paper-faithful approximation-number and finite singular-value
   statements built on the existing full mathematics-ahead proof.

## Files

- `DavisKahan/Experimental/Scratch/Section6/Lemma63Promotion.lean`
- `DavisKahan/Experimental/Scratch/Section6/All.lean`
- `dev/lemma63-scratch-candidates-7f9f562.json`

## Promotion recommendation

Do not silently claim that grounding the current frontier bodies completes
Lemma 6.3.  Prefer this sequence:

1. compile the scratch module;
2. use the zero-leakage candidates to remove the current proof placeholders if
   an immediate frontier-score improvement is useful;
3. change the canonical source-facing signatures to the corrected block
   equation;
4. promote the paper-faithful candidates;
5. update the frontier manifest and source census to identify the corrected
   declaration as the source theorem.

The corrected proof explicitly assumes `0 < n`.  This is the natural prefix
condition used to control the operator norm by the zeroth approximation
number.  If the canonical theorem must allow `n = 0`, add a separate rank-zero
branch showing that the target projection is zero.

## Lemma ledger

### Confident repository declarations

- `Submodule.isIdempotentElem_starProjection`
  - assumed: `P.starProjection ∘L P.starProjection = P.starProjection`.
- `ContinuousLinearMap.comp_apply`
  - assumed: evaluation of bundled composition.
- `ContinuousLinearMap.comp_assoc`
  - assumed: associativity of bundled composition.
- `ContinuousLinearMap.approximationNumber_eq_singularValues`
  - finite-dimensional identification of approximation numbers and ordinary
    singular values.
- `MathAhead.Section6Appendix.lemma6_3_approximationNumber_leakage_completed`
  - corrected approximation-number leakage theorem with `0 < n`, the source
    block equation, and target-rank bound.
- `Frontier.Section6Appendix.approximationEnergy`
- `MathAhead.Section6Appendix.approximationSquareEnergy`
- `norm_zero`, `map_zero`, `sub_self`, `Finset.sum_congr`.

### Likely mechanical repairs

- The projection-idempotence equality may need multiplication notation rather
  than `∘L` after elaboration unfolds the algebra instance.
- Rewriting the `NNReal` equality returned by
  `approximationNumber_eq_singularValues` inside a real square may require
  `exact_mod_cast` or a one-line coercion equality.
- The `simpa only` converting the two energy definitions may need both
  definitions unfolded explicitly.
- The line break after the namespace qualification of the mathematics-ahead
  theorem may need to be collapsed if the parser treats it poorly.

## Confidence

- `strongBlockEquation_forces_zero_leakage`: complete mathematics.
- current frontier wrappers: complete mathematics; statement is overstrong.
- energy-name bridge: complete, expected definitional equality.
- corrected approximation theorem: complete modulo elaboration of the exact
  application.
- finite energy/singular-value bridge: probably complete; coercion spelling is
  the likely repair point.
- corrected finite theorem: complete once the bridge elaborates.

## Divergences

- The current frontier equation is stronger than the paper's equation and
  trivializes the leakage conclusion.
- The corrected scratch theorem adds `0 < n`.  The existing mathematics-ahead
  proof needs a nonempty approximation-number prefix.  A rank-zero branch can
  remove this explicit assumption if required.
- The corrected proof uses only the rank bound on `Q`; the rank bound on `P` is
  retained in the source-facing wrapper for compatibility and symmetry.
