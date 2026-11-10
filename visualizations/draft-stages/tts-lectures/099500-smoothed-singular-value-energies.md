# 099500 — Smoothed singular-value energies

**Draft status:** audio-first mathematical lecture. **Recommended background:** `096000` singular-value sequences, `098000` symmetric operator ideals, `099000` Hilbert–Schmidt and trace-class operators.

<!-- BEGIN SPOKEN LECTURE -->

# Smooth spectral penalties and their hidden domain

The nuclear norm measures the sum of singular values of an operator. It is a powerful way to encourage low rank, but an individual singular value enters through an absolute-value-like cost that is not differentiable at zero. A common mathematical strategy is to replace that sharp cost by a smooth scalar function.

There is a catch in infinite dimensions. A scalar penalty that looks like the absolute value for large inputs may behave quadratically near zero. An operator has infinitely many small singular values, so the near-zero behavior determines which operators have finite total cost.

We can see this exactly for a smoothed square-root penalty, sometimes called the Charbonnier penalty.

## Start from one singular value

Fix a positive smoothing scale tau. For a nonnegative number s, define the penalty as the square root of tau squared plus s squared, minus tau. Subtracting tau makes the cost zero at s equal to zero.

Rationalize the expression by multiplying numerator and denominator by the sum of the square root and tau. The result is s squared divided by the square root of tau squared plus s squared, plus tau.

Two regimes become visible. When s is much smaller than tau, the denominator is close to twice tau, so the penalty is approximately s squared divided by twice tau. When s is large compared with tau, the square root is close to s, so the penalty is approximately s minus tau.

The function is nonnegative and increasing for nonnegative s. Its first derivative is s divided by the square root of tau squared plus s squared; that derivative is zero at s equal to zero. Its second derivative is tau squared divided by tau squared plus s squared to the three-halves power, which is positive. Thus the scalar penalty is smooth and convex.

## Apply the function to singular values

Let T be a bounded operator between Hilbert spaces, with singular values s one, s two, and so on, when a compact singular-value description is available. Sum the smoothed penalties of those values.

For an infinite-dimensional noncompact operator, one can use approximation numbers or an extended spectral ideal formulation to define an extended-valued cost. To understand finiteness, we can first work with compact operators and their singular-value sequences.

Let M be the operator norm of T. Every singular value lies between zero and M. The rationalized formula bounds the penalty from below by s squared divided by the square root of tau squared plus M squared, plus tau. It bounds the penalty from above by s squared divided by twice tau.

These constants are finite and positive because tau is positive and T is bounded. Sum the inequalities across the singular values. The total smoothed cost is finite exactly when the sum of squared singular values is finite.

But square-summability of singular values is precisely the Hilbert–Schmidt condition. Thus, for every fixed positive smoothing scale, the smoothed nuclear-type energy has the Hilbert–Schmidt class as its finite-cost domain.

The proof is not an analogy. It is a two-sided comparison with the Hilbert–Schmidt energy, with explicit constants depending on tau and the operator norm.

## A diagonal example that separates the ideals

Take the diagonal operator on square-summable sequences whose n-th diagonal entry is one divided by n. Its singular values are one over n. Their squares sum to a finite value, but their ordinary sum diverges.

Therefore this operator is Hilbert–Schmidt but not trace class. For every fixed positive tau, the total smoothed penalty is finite, because its high-index terms behave like one divided by twice tau n squared.

Now let tau decrease toward zero. At every fixed positive singular value s, the smoothed penalty approaches s. Moreover, decreasing tau increases the penalty. Monotone convergence for the nonnegative series then shows that the total cost tends to the sum of singular values, which is infinite for this example.

Thus an operator can have finite cost at every positive smoothing scale, while the zero-smoothing limit diverges. One cannot interchange the limiting parameter and the infinite singular-value sum without checking summability.

## Why this is an energy rather than a norm

The total cost vanishes at the zero operator. But it is not homogeneous in the way a norm must be. Doubling a very small singular value approximately quadruples its penalty, because the local behavior is quadratic, whereas doubling a very large one approximately doubles the cost.

It is better to call this a spectral energy or penalty. Its finite-cost domain may agree with a normed operator ideal, but that does not make the penalty itself an ideal norm.

The distinction is useful in optimization. A quadratic region near zero makes differentiable optimization easier, while the near-linear region at large singular values retains some of the behavior of nuclear-norm regularization.

## A finite-dimensional gradient calculation

For a finite rectangular matrix T, consider the trace of the square root of T adjoint T plus tau squared times identity, minus tau times the input-space dimension. This equals the sum of the smoothed penalties of the singular values, including zeros.

The gradient of this cost, for the Frobenius inner product, is T times the inverse square root of T adjoint T plus tau squared identity. In a singular-value decomposition, this simply replaces each nonzero singular value s by s divided by the square root of tau squared plus s squared, leaving its left and right singular vectors aligned.

Because tau is positive, the inverse square root is bounded. There is no division by an individual singular value, even if the matrix loses rank. This explains why smoothing is convenient for gradient-based methods.

The finite-dimensional gradient formula should not be transferred blindly to arbitrary bounded infinite-dimensional operators. One must first specify the operator ideal, the topology of differentiation, and whether the trace being differentiated is finite.

## The limiting choices

There are three mathematical decisions here: which singular-value penalty is used, which operator ideal is its natural domain, and how the smoothing limit is taken. The scalar rationalization answers the second question for this penalty. It also provides the exact bounds needed to pass from finite-rank truncations to Hilbert–Schmidt operators.

The example with singular values one over n shows why smoothing and the infinite-dimensional limit must be handled separately. A smooth-looking scalar objective can encode a stronger or weaker summability condition than its zero-smoothing counterpart.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and source correspondence (display only)

For \(\tau>0\) and \(s\ge0\),
\[
\phi_\tau(s)=\sqrt{\tau^2+s^2}-\tau
=\frac{s^2}{\sqrt{\tau^2+s^2}+\tau},\qquad
\frac{s^2}{\sqrt{\tau^2+M^2}+\tau}\le\phi_\tau(s)\le\frac{s^2}{2\tau}\quad(0\le s\le M).
\]
For a compact bounded T, \(\Phi_\tau(T)=\sum_j\phi_\tau(s_j(T))\) is finite if and only if \(T\in S_2\). The extended cost defined using approximation-number singular values can be treated across bounded operators, with nonmembership recorded as infinity. For a finite rectangular complex matrix, \(\nabla\Phi_\tau(T)=T(T^*T+\tau^2I)^{-1/2}\) in the real Frobenius pairing.

**Checked source map.** `ForTauCeti/Analysis/OperatorIdeal/Charbonnier.lean` includes `charbonnier_quadratic_bounds`, `charbonnierCost`, `schatten_two_sq_le_mul_charbonnierCost`, `charbonnierCost_le_mul_schatten_two_sq`, and `charbonnierCost_ne_top_iff_schatten_two`. `ForTauCeti/Analysis/OperatorIdeal/SmoothedPower.lean` develops a wider family of smoothed spectral power costs. The matrix gradient is an independent finite-dimensional calculus calculation; the named declarations above establish the quadratic bounds and domain characterization, not that gradient formula.
