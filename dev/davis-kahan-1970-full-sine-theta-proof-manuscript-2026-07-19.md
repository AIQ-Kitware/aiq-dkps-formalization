# Mathematical proof manuscript for the remaining source-faithful sine-theta results

This manuscript isolates the hard mathematics from Lean elaboration.  It is
written against the exact specification in the companion document.

## 1. Rectangular modulus and literal directed angles

For a bounded operator `T : E -> F`, put `|T| = (T^* T)^(1/2)`.  Then

    || |T| x ||^2 = <T^* T x, x> = ||T x||^2.

The exact Courant--Fischer characterization of approximation numbers depends
only on the lower bounds of `x |-> ||T x||` on finite-codimensional subspaces.
Therefore

    a_n(|T|) = a_n(T)

for every `n`, without invoking a polar decomposition or compactness.  This is
the clean bridge between a rectangular cross-projection block and the positive
operator used in the paper's angle definition.

For the directed angle from the trial subspace `U` to the exact subspace
`V`, take the source cosine block and its positive modulus

    C_0 = P_V restricted to U,
    cos(Theta_0) = |C_0|,
    Theta_0 = arccos(|C_0|).

This is the order of definition used in the paper.  Orthogonal decomposition
gives the operator Pythagoras identity

    |P_(V^perp) restricted to U|^2 + |C_0|^2 = I_U.

The spectrum of `|C_0|` lies in `[0,1]`, so continuous functional calculus
gives a positive angle with spectrum in `[0,pi/2]`.  Functional calculus,
operator Pythagoras, and uniqueness of the positive square root then give

    sin(Theta_0) = |P_(V^perp) restricted to U|.

Thus the literal functional-calculus sine has exactly the complete singular-
value sequence of the rectangular cross-projection block printed in the
paper.  The full angle is the orthogonal direct sum of the two directed source
angles; its sine has exactly the singular values of `P_U - P_V`.  The earlier
ambient `arcsin |P_U-P_V|` construction is retained only as a proved equivalent
representative, not as the source definition.

## 2. Universal source norms

Let `Phi_n` be one coherent family of normalized symmetric gauges on `R^n`,
with invariance under permutations and signs and compatibility under trailing
zero extension.  For a bounded operator `T` define

    |||T|||_Phi^ext = sup_n Phi_n(a_0(T),...,a_(n-1)(T)).

The canonical ideal is the set on which this supremum is finite.  Coherence
makes this exactly the symmetric sequence ideal associated to the source
norming function.

Ky Fan dominance is proved at each finite prefix by the finite-dimensional
T-transform theorem.  Taking the supremum gives the infinite-dimensional
statement.  Triangle inequality follows from Ky Fan submajorization of
approximation numbers, finite gauge monotonicity, and the supremum.  Two-sided
unitary invariance and adjoint invariance follow from exact equality of all
approximation numbers.  The ideal estimate follows from

    a_n(L T R) <= ||L|| ||R|| a_n(T).

This proves the full source norm package, rather than assuming a separate
membership predicate.

## 3. Lemma 6.1

The two selected blocks have orthogonal initial spaces and orthogonal final
spaces.  Their sum is unitarily equivalent to their orthogonal direct sum.
For compact or approximation-number formulations, the singular-value sequence
of the direct sum is the decreasing rearrangement of the multiset union of the
two sequences.

Suppose every finite Ky Fan prefix of `A_0` is bounded by the corresponding
prefix of `B_0`, and likewise for `A_1`, `B_1`.  For a fixed prefix length `k`,
choose the number `j` of entries contributed by the first component in a
maximizing prefix of `A_0 directSum A_1`.  Then

    KF_k(A_0 directSum A_1)
      = KF_j(A_0) + KF_(k-j)(A_1)
      <= KF_j(B_0) + KF_(k-j)(B_1)
      <= KF_k(B_0 directSum B_1).

This proves weak majorization and hence every source norm inequality.  The
converse in the paper follows by replacing the two comparison components with
operators having the same singular sequences as the corresponding selected
blocks and applying the same direct-sum formula.

## 4. Lemma 6.2

Let `R_Omega = Omega - Omega_compl` and
`R_Gamma = Gamma - Gamma_compl`.  These are self-adjoint unitary involutions.
Expanding the four projector corners gives

    2 (Omega K Gamma + Omega_compl K Gamma_compl)
      = K + R_Omega K R_Gamma.

Absolute homogeneity, triangle inequality, and two-sided unitary invariance
then give

    2 N(selected K) <= N(K) + N(R_Omega K R_Gamma) = 2 N(K).

No factor is lost.

## 5. Proposition 6.1

Apply the one-sided theorem to the selected block of `A` and complementary
block of `A+H`, obtaining

    delta s(P_compl Q) weakly-majorized-by P_compl H Q.

Apply it in the reverse direction:

    delta s(P Q_compl) weakly-majorized-by P H Q_compl.

Lemma 6.1 combines these into the full cross sum.  Lemma 6.2 contracts the two
perturbation corners by `H`.  The cross sum has exactly the complete singular-
value sequence of `sin Theta`, so every source norm yields

    delta N(sin Theta) <= N(H).

## 6. Theorem 6.1

Whiten `E_0` by its Gram inverse square root.  The lower-frame bound implies

    ||E_0 (E_0^* E_0)^(-1)|| <= epsilon^(-1).

The complementary residual identity is

    R^* F_1 = E_0^* F_1 Lambda_1 - A_0 E_0^* F_1.

The sharp ordered/interval Sylvester theorem gives every finite Ky Fan bound

    delta KF_k(E_0^* F_1) <= KF_k(R^* F_1) <= KF_k(R).

The projector identity

    P Q_compl = E_0 (E_0^* E_0)^(-1) E_0^* F_1 F_1^*

and the ideal property give the factor `epsilon^(-1)`.  Universal Fan
dominance then yields the conclusion for every source norm and for any source
representative sharing the singular values of `P Q_compl`.

## 7. Exact common-domain appendix form

For bounded `E_0`, the domain of `E_0 A_0` is `dom A_0`, while the domain of
`A E_0` is `{x | E_0 x in dom A}`.  Thus "common dense domain" for the two
products means equality of these sets.  The accepted theorem uses the forward
inclusion because it is sufficient, but the literal source wrapper records the
equality and derives the accepted hypothesis.  Density follows from dense
definition of `A_0`.

## 8. Theorem 6.2: the square-norm estimate

The Hilbert--Schmidt class `S_2(F,E)` is a Hilbert space.  Under the standard
identification with `E tensor conjugate(F)`, left multiplication by a self-
adjoint operator `A` corresponds to `A tensor 1`, and right multiplication by
`B` corresponds to `1 tensor conjugate(B)`.  Their spectral measures commute,
so the Sylvester operator corresponds to multiplication by

    (lambda, alpha) |-> lambda - alpha

with respect to the product spectral measure.

If every spectral pair satisfies `|lambda-alpha| >= delta`, then for every
Hilbert--Schmidt `X` in the natural domain,

    ||A X - X B||_2^2
      = integral |lambda-alpha|^2 d mu_X
      >= delta^2 integral 1 d mu_X
      = delta^2 ||X||_2^2.

Taking square roots gives the sharp constant-one estimate.  The same cutoff
argument extends it to closed self-adjoint operators and a bounded residual
extension.

Apply this to `X = E_0^* F_1`, then repeat the whitening argument of Theorem
6.1.  This proves

    delta epsilon ||sin Theta_0||_2 <= ||R||_2.

For finite-rank `R` of rank at most `r`, the square norm is controlled by
the operator norm:

    ||R||_sq <= sqrt(r) ||R||_op.

Also `||sin Theta_0||_op <= ||sin Theta_0||_sq`.  Therefore the square estimate
gives exactly the paper's fallback

    delta epsilon ||sin Theta_0||_op
      <= ||R||_op sqrt(r).

The subscript-one notation in the paper denotes the operator or bound norm; it
is not a nuclear-norm statement.

## 9. Sharpness

Take the two-dimensional rank-one model with one exact line and one trial line
at angle `theta`.  Choose diagonal block eigenvalues separated by `delta`, and
choose the perturbation so the residual block equals `delta sin(theta)` times a
rank-one partial isometry.  Then the sine block and residual are positive
multiples of rank-one partial isometries.

Every normalized unitarily invariant norm assigns a rank-one partial isometry
norm one.  Therefore equality holds simultaneously for every source norm:

    delta N(sin Theta) = N(R).

Orthogonal direct sums of this model give equality at every finite
multiplicity.  Since equality occurs for positive `theta`, no smaller universal
constant can replace one.

The paper's one-direction counterexample is a separate two-dimensional model:
its one-sided theorem is sharp, while the attempted symmetric square-norm
conclusion fails.  Formalizing its matrices protects Proposition 6.1's second
gap hypothesis from accidental deletion.
