# Exact specification for the Davis--Kahan 1970 sine-theta section

Date: 2026-07-19

This document is the acceptance contract for the source-faithful formalization
of Section 6 and the corresponding unbounded appendix statements.  The
compiler-accepted central theorem is a major dependency, but it is not by
itself the endpoint.  The endpoint is literal agreement with the objects,
quantifiers, hypotheses, conclusions, and optimality claims in the paper.

## Source objects

The paper works with orthogonal projectors `P`, `Q`, their complements, and the
canonical direct-rotation angle operators.  A source-faithful API must include:

1. the positive cosine blocks;
2. positive angle operators with spectrum in `[0, pi / 2]`;
3. their functional-calculus sines;
4. proofs that these sines have exactly the singular values assigned in the
   paper to `sin Theta`, `sin Theta_0`, and `sin Theta_1`;
5. the full symmetric sine, whose singular values equal those of `P - Q`.

It is not enough to name a projection residual `sinTheta`.  The projection
residual may be used as a proof representative only after an explicit
singular-value equivalence with the literal functional-calculus object.

## Source norm quantifier

A paper norm is one normalized symmetric norming function, coherently used in
all finite dimensions.  For an infinite singular-value sequence its canonical
ideal and norm are determined by finite prefixes.  Membership is not an
independent predicate.

The formalization must prove:

* normalization;
* absolute homogeneity and triangle inequality;
* adjoint and two-sided unitary invariance;
* contraction compatibility;
* Ky Fan dominance;
* transport across operators with identical complete singular-value data;
* that every source norm can be used in Theorem 6.1 and Proposition 6.1.

Concrete Schatten, trace, Hilbert--Schmidt, Ky Fan, and operator norms are
important usability instances, but the universal source quantifier cannot be
replaced by a list of examples.

## Lemma 6.1

For orthogonal projectors `Omega`, `Gamma` and their complements, if the two
selected blocks are weakly majorized by corresponding comparison blocks, then
their orthogonal sum is weakly majorized by the sum of the comparison blocks.
The converse requires the matching singular-value hypotheses stated in the
paper.

The implementation must prove simultaneous finite Ky Fan inequalities first
and then invoke source Fan dominance.  A triangle inequality is not a
replacement: it loses the sharp coupling.

## Lemma 6.2

For projectors `Omega`, `Gamma` and every bounded operator `K`,

    N (Omega K Gamma + Omega_compl K Gamma_compl) <= N K

for every source norm.  The source proof uses the reflection identity

    2 selected(K) = K + (Omega - Omega_compl) K (Gamma - Gamma_compl),

where both reflections are unitary involutions.  The formalization must expose
this identity and derive the norm contraction without a factor loss.

## Original sine theorem

The original one-sided theorem must be available in the paper's literal angle
vocabulary, for every source norm, with the sharp constant `1 / delta` and the
paper's interval/exterior spectral hypothesis.  Ordered half-line variants may
remain as useful extensions, but they do not replace the literal source form.

## Proposition 6.1

Under both directional source sine-theorem gaps,

    delta * N (sin Theta) <= N H

for every source norm.  The proof must follow the paper:

1. apply the directed theorem twice;
2. use Lemma 6.1 to combine the two sine blocks;
3. use Lemma 6.2 to contract the two perturbation blocks;
4. identify their sum with the literal full sine.

## Theorem 6.1

The generalized theorem must retain exactly:

* bounded `E_0`, not necessarily isometric;
* `E_0^* E_0 >= epsilon^2` with `epsilon > 0`;
* no equal-dimension assumption;
* the residual `R = (A + H) E_0 - E_0 A_0`;
* either orientation of interval/exterior separation between `A_0` and
  `Lambda_1`;
* an arbitrary source representative with the same singular values as
  `P Q_compl`;
* every normalized unitarily invariant norm;
* conclusion `delta * epsilon * N (sin Theta_0) <= N R`.

The exact common-domain form from the unbounded appendix must also be exposed.
For bounded `E_0`, the common domain is the pullback of the ambient domain and
must equal `dom A_0`; a merely unspecified dense core is not silently
substituted.

## Theorem 6.2

The only spectral restriction is pairwise distance:

    |lambda - alpha| >= delta > 0

for every `lambda` in the spectrum of `Lambda_1` and every `alpha` in the
spectrum of `A_0`.  The conclusion is specifically the square or
Hilbert--Schmidt norm:

    delta * epsilon * HS (sin Theta_0) <= HS R.

This is a constant-one result.  The general `pi / 2` arbitrary-norm separated-
spectrum theorem is a different result and cannot replace it.

The paper also records the bound-norm fallback

    delta * epsilon * opNorm (sin Theta_0)
      <= opNorm(R) * sqrt(rank R).

Here the paper's subscript-one notation denotes the operator or bound norm,
not the trace norm.  In infinite dimensions the displayed right-hand side is
finite only when `R` has finite rank.  The formal statement must make that
premise explicit rather than hide it in an extended-real convention.

## Sharpness and equality

The paper states that the constants are best possible and can be attained
simultaneously for all normalized unitarily invariant norms by direct sums of
two-dimensional examples.  The formalization must contain:

* one explicit two-dimensional equality model;
* rank-one normalization showing equality for every source norm;
* finite direct sums producing simultaneous equality at arbitrary finite
  multiplicity;
* a theorem that no smaller universal constant is valid.

The counterexample immediately before Proposition 6.1 must also be represented:
one directional gap does not imply the symmetric square-norm estimate.

## Trust and public surface

Completion requires all source aliases to compile from source and print only
Lean's standard foundational dependencies.  The exact-paper audit must cover:

* Lemmas 6.1 and 6.2;
* original sine theorem;
* Proposition 6.1;
* Theorems 6.1 and 6.2;
* real and complex forms;
* bounded and unbounded common-domain forms;
* source norm universality;
* literal angle bridges;
* sharpness/equality and the one-sided counterexample.

No theorem is called source-faithful merely because an equivalent block
inequality exists elsewhere in the repository.
