# 099500 — Smoothed singular-value energies

**Draft status:** audio-first mathematical lecture. **Recommended background:** `096000` singular-value sequences, `098000` symmetric operator ideals, `099000` Hilbert–Schmidt and trace-class operators.

<!-- BEGIN SPOKEN LECTURE -->

# Making a sharp singular-value penalty smooth

Suppose we want to encourage a matrix to have few significant singular values. One familiar penalty is the nuclear norm: add all the singular values. Large singular values are expensive, and setting a singular value to zero removes its contribution entirely.

There is an optimization difficulty. A singular value behaves rather like an absolute value, and the nuclear norm can fail to be differentiable when singular values reach zero. In numerical optimization, it can be useful to replace this sharp cost with a smooth one.

But there is a mathematical surprise. In infinite dimensions, smoothing the cost changes which operators have finite total energy. To understand why, we need to look closely at one scalar function near zero.

## Start with one nonnegative number

Let s be a singular value, so s is nonnegative. Choose a positive smoothing scale, which we'll call tau.

Define the smoothed penalty by taking the square root of tau squared plus s squared, and then subtracting tau.

This is sometimes called a Charbonnier-style penalty. It equals zero when s is zero. It is smooth as a function of s because tau is strictly positive.

Let's set tau equal to one for a numerical picture.

If s is one, the cost is square root of two minus one, about zero point four one four.

If s is one tenth, the cost is square root of one point zero one minus one, approximately zero point zero zero five. That is much smaller than one tenth.

If s is ten, the cost is square root of one hundred and one minus one, a little more than nine. For large s, it behaves approximately like s minus tau.

So the smoothed penalty has two regimes. It is roughly quadratic for singular values much smaller than tau. It is roughly linear for singular values much larger than tau.

That change near zero is the entire story behind its infinite-dimensional domain.

## Reveal the quadratic behavior exactly

There is a useful algebraic trick. Take the square root of tau squared plus s squared minus tau, and multiply numerator and denominator by the matching sum, the square root plus tau.

In the numerator, the difference of squares simplifies to s squared. In the denominator, we retain the square root of tau squared plus s squared, plus tau.

So the penalty is exactly s squared divided by that denominator.

When s is very small, the square root in the denominator is close to tau. The denominator is therefore close to twice tau, and the penalty is approximately s squared divided by twice tau.

The derivative tells the same story. Its first derivative is s divided by the square root of tau squared plus s squared, which becomes zero at s equal to zero. The second derivative is positive for tau greater than zero. The penalty is smooth and convex.

For a scalar input, the calculation is straightforward. But summing these penalties over infinitely many singular values requires more thought.

## From one value to a whole operator

Let T be a bounded compact operator on a Hilbert space, or between two Hilbert spaces. It has singular values listed in descending order, possibly infinitely many.

Define its smoothed spectral energy by applying our scalar penalty to every singular value and adding the results.

The total could be finite or infinite. To decide which, remember that a bounded operator has a finite largest singular value. Call that upper bound M.

Every singular value s lies between zero and M. In our rationalized expression, the denominator is at least twice tau, and it is at most the square root of tau squared plus M squared, plus tau.

Therefore the penalty lies between two positive constant multiples of s squared. One constant comes from twice tau, and the other from the upper bound M.

Now sum those inequalities across all singular values.

We find that the total smoothed energy is finite exactly when the sum of squared singular values is finite. And that is precisely the Hilbert-Schmidt condition.

This is the crucial conclusion. For every fixed positive smoothing scale, this smooth nuclear-like penalty has the Hilbert-Schmidt class as its finite-energy domain.

It may look approximately like a sum of singular values for large s, but there can only be finitely many singular values above a fixed positive threshold for a compact operator. It is the infinite tail of small singular values that determines whether the total converges.

The near-zero quadratic behavior wins.

## Two diagonal operators clarify the boundary

First take an operator on ell two with diagonal entries one over n. Its singular values are one, one half, one third, and so on.

The sum of the singular values diverges, because it is the harmonic series. So this operator is not trace class.

However, their squares have finite sum. For every fixed positive tau, the smoothed penalty is comparable to the square of each small singular value, so the total smoothed energy is finite.

Now change the diagonal coefficients to one over the square root of n. They still tend to zero, so the operator is compact. But their squares add to the harmonic series and diverge. Consequently, even the smoothed energy is infinite for every fixed positive tau.

These two examples separate three different properties: compactness, finite Hilbert-Schmidt energy, and finite trace norm.

Our smooth penalty detects the second one.

## What happens when smoothing disappears?

Return to the operator with coefficients one over n. Keep the operator fixed, and make tau smaller and smaller.

For every fixed positive singular value s, the penalty approaches s as tau approaches zero. The smoothing disappears, and we recover the sharp absolute-value-like penalty.

There is an additional useful fact. As tau decreases, the penalty for each fixed s increases. So the total energies form an increasing family as the smoothing parameter moves down toward zero.

Because every summand is nonnegative, monotone convergence lets us pass the limit through the infinite sum. The limiting total is the sum of the singular values, which is infinite for this operator.

Thus every positive smoothing scale gives a finite answer, yet the energy tends to infinity as the smoothing scale goes to zero.

That is a real change of domain at the limiting parameter. It is a warning against treating an infinite sum as though it were a finite list of singular values.

## Why the energy is not a norm

A norm must scale linearly with the absolute value of a scalar. Double an operator, and its norm must double.

Our smoothed energy does not obey that rule. For a very small singular value, the cost is approximately proportional to its square. Doubling that singular value multiplies its cost by about four, not two.

For a very large singular value, the cost behaves more nearly linearly. So the scaling behavior depends on the magnitude relative to tau.

The smoothed energy is a convex spectral penalty, not a norm, even though the class of operators on which it is finite is a familiar normed ideal.

That distinction is useful. Optimization methods may use the penalty because it has a smooth gradient, while functional analysis uses an ideal norm to describe the underlying space and convergence.

## The finite-dimensional gradient

For a finite rectangular matrix T, we can express the smoothed energy as the trace of the positive square root of T adjoint T plus tau squared times identity, minus tau times the number of input coordinates.

The subtraction is essential. Every zero singular value contributes zero to the desired cost. If we did not subtract tau for each input coordinate, extra zero directions would add an irrelevant constant in finite dimensions and an infinite offset in infinite dimensions.

The gradient of the finite-dimensional energy, with respect to the Frobenius inner product, has a clean expression. Multiply T on the right by the inverse square root of T adjoint T plus tau squared identity.

Why is that reasonable? In a singular-value decomposition, the gradient acts along the same left and right singular directions. It replaces each singular value s by the derivative of the scalar penalty: s divided by the square root of tau squared plus s squared.

Because tau is positive, the denominator never vanishes, even when s is zero. This is the computational advantage of smoothing.

In an infinite-dimensional setting, differentiability must be considered on a specified operator space, with a specified norm or topology. The finite matrix formula alone does not justify taking traces or gradients of arbitrary bounded operators.

## The underlying principle

A scalar penalty can be smooth and finite for every individual input, while its sum over infinitely many singular values is infinite.

For this particular square-root penalty, rationalizing the expression showed exactly why: near zero, it is comparable to the square of the singular value. That determines a Hilbert-Schmidt finite-energy domain. Sending the smoothing scale to zero recovers the trace-norm sum, and the domain can become smaller.

The reliable method is to examine the penalty near zero, compare it with a familiar power, and only then sum over the singular-value sequence. That tells us what an infinite-dimensional regularizer is actually measuring.

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
