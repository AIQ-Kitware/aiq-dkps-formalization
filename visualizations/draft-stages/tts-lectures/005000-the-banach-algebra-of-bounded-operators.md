# The Banach algebra of bounded operators

<!-- BEGIN SPOKEN LECTURE -->

For a bounded linear map, the operator norm measures the largest possible amplification of a unit input. Composing bounded maps leads to a space of operators where addition, multiplication by composition, and limits interact.

This is where several ideas from our first three lectures meet. We need linear maps because we want to compose them. We need operator norms because we want quantitative bounds. And we need completeness because we want infinite sums of operators to converge to actual operators.

The result is called a Banach algebra. The name is less important than what the structure lets us do: construct inverses, estimate errors, and make sense of operator power series.

## An algebra made of transformations

Let E be a Banach space. Consider every bounded linear operator that takes E back into E. We can add two such operators by adding their outputs. We can multiply an operator by a scalar. And we can multiply operators with each other by composition: apply one transformation, then the other.

There is a distinguished operator called the identity. It leaves every vector unchanged. Composing it with another operator, on either side, changes nothing.

Composition is associative. If we have three operators, we obtain the same result whether we group the first two or the last two, because both groupings apply the same three transformations in the same order.

But composition need not be commutative. Imagine one map that stretches horizontally and another that rotates the plane. Stretching before rotating generally gives a different result from rotating before stretching. So this algebra is not like ordinary multiplication of real numbers.

We already know how to bound the size of a product: the norm of a composition is at most the product of the two norms. This is called a submultiplicative norm. It tells us that multiplying operators respects our quantitative notion of size.

For a nonzero Banach space, the identity has operator norm one. Applying it to any unit vector preserves length exactly. In the zero-dimensional space the identity operator is also the zero map, so its norm is zero; that harmless exceptional case is why we should not silently assume every identity has norm one.

## Why the operator space is complete

The missing piece is completeness. Suppose we have a sequence of bounded operators that is Cauchy in operator norm. That means that, sufficiently far along the sequence, any two operators send every input to nearly the same output, with an error bounded by a small constant times the input length.

Fix one vector x. Apply all the operators to that vector. The resulting sequence of output vectors is Cauchy, because the operator differences are small. Since E is Banach, those output vectors converge to a vector in E.

Do this for each input x, and define a new map T by taking those limits. Is T linear? Yes. Each approximate operator respects addition and scaling, and the corresponding limits preserve those operations. Thus T is linear.

Is T bounded? Fix a sufficiently late operator from the sequence. The Cauchy estimate bounds the difference between that operator and every later one, uniformly relative to input length. Let the later operator index tend to infinity. The same bound holds between the fixed operator and T. Since the fixed operator is bounded, T must be bounded too.

That argument gives more than pointwise convergence. It shows that the operator norm of the difference between T and our approximations tends to zero. We have found a limit inside the space of bounded operators.

So the bounded operators on E, equipped with addition, scalar multiplication, composition, the identity, and the operator norm, form a complete normed algebra: a Banach algebra.

## Inverting by repeated correction

Here is a practical consequence. Suppose T is a bounded operator whose norm is strictly smaller than one. We want to invert the operator that takes a vector x to x minus T of x. In symbols we might call it identity minus T, but keep the action in mind: subtract one application of T from the original vector.

Start with a very simple example on the plane. Let T halve horizontal coordinates and erase vertical coordinates. Then identity minus T halves the horizontal coordinate but leaves the vertical coordinate unchanged. Its inverse must double the horizontal coordinate and leave the vertical coordinate unchanged.

Watch what happens if we try to build that inverse by repeated corrections. Start with the identity. Add T. Add T composed with T. Then add T applied three times, and so on. On a horizontal input, these terms contribute one, one half, one quarter, one eighth, and so forth. Their total is two. On a vertical input, T and all its later powers vanish, leaving one. We recover the inverse exactly.

Now prove this in general. Because the norm of a product is at most the product of the norms, the norm of T applied n times is at most the nth power of the norm of T. The operator norms of the powers are therefore bounded by an ordinary geometric series with ratio smaller than one.

That geometric series has a finite sum. Our Banach-algebra completeness theorem tells us that the infinite series of operator powers converges in operator norm. Call its limit S.

Multiply a finite partial sum by identity minus T. All intermediate terms cancel: the first identity remains, and we subtract the final power of T. As we include more terms, that final power tends to zero in operator norm. Passing to the limit gives identity minus T, composed with S, equals the identity.

The cancellation also works in the opposite multiplication order, because all the terms are powers of the same T. Thus S is a two-sided inverse.

We have constructed an inverse, not merely asserted that one exists. This is called the Neumann series. It is the operator version of the geometric series you learned in calculus.

## A quantitative estimate and a warning

The same geometric sum bounds the inverse norm. The norm of the inverse of identity minus T is at most one divided by one minus the norm of T. As T's norm approaches one from below, this bound becomes large.

That does not mean the inverse always becomes large. It means the estimate becomes less informative. The condition that T has norm below one is sufficient for the construction; it is not necessary for invertibility.

For instance, consider a plane transformation that sends the vertical coordinate to ten times that coordinate in the horizontal direction, and sends horizontal vectors to zero. Apply it twice and everything becomes zero. Its norm is ten, yet identity minus this map has inverse identity plus the map, because its square is zero. The Neumann series ends after two nonzero terms even though the simple geometric norm test fails.

Now suppose A already has a bounded two-sided inverse, and H is another bounded operator. Factor A plus H as A composed with identity plus A inverse composed with H. In the order of evaluation, apply the parenthesized operator first and then apply A. If the norm of A inverse composed with H is below one, the Neumann construction proves that A plus H is also invertible.

This is a first quantitative reason that invertibility is stable under sufficiently small operator changes. We have not yet entered spectral perturbation theory; we are establishing an elementary analytic tool that the spectral theory will later need.

One caution matters. When we say an operator is invertible in this Banach algebra, we mean that its inverse is itself a bounded everywhere-defined operator. A separate theorem will tell us when a bounded bijection between Banach spaces automatically has a bounded inverse. We have not assumed that theorem here.

## Reconstruction

Can you reconstruct the Neumann inverse without remembering its name? Begin by expanding the finite sum of the identity and powers of T. Multiply by identity minus T. Observe the cancellation. Then explain exactly where the hypothesis that T has norm below one enters: it makes the tail vanish and guarantees convergence of the operator series.

For a second check, explain why we needed E to be complete. We first obtain limiting outputs for each input, and then we use an operator-norm Cauchy estimate to assemble those limits into a bounded operator. Without completeness, the would-be outputs might lie outside E.

We now have a space of operators in which addition, composition, limits, and certain inverses coexist. Such maps are called linear functionals, and they will lead us to dual spaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For a Banach space \(E\), \(\mathcal B(E)=\{T:E\to E:T\text{ linear and bounded}\}\) is a Banach algebra under composition, with \(\|ST\|\le\|S\|\|T\|\). If \(\|T\|<1\), then \(I-T\) has a two-sided inverse and
\[
(I-T)^{-1}=\sum_{n=0}^\infty T^n,\qquad
\|(I-T)^{-1}\|\le\frac1{1-\|T\|}.
\]
For an invertible bounded operator \(A\), if \(\|A^{-1}H\|<1\), then \(A+H=A(I+A^{-1}H)\) is invertible. The multiplication order matters.

**Lean bridge.** `DavisKahan/Sources/DavisKahan1970/DoubleAngleTangentOperator.lean` uses the Neumann-series construction in a later, more specialized proof. This excerpt is from the proof of `norm_ringInverse_doubleAngleDenominator_le`:

```lean
  have hgeomRaw := tsum_geometric_le_of_norm_lt_one T hTlt
  rw [ContinuousLinearMap.one_def] at hgeomRaw
  have hgeom : ‖∑' n : ℕ, T ^ n‖ ≤ (1 - ‖T‖)⁻¹ := by
    have hone : ‖ContinuousLinearMap.id ℂ E0‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact hgeomRaw.trans (by linarith)
  change ‖Ring.inverse (1 - T)‖ ≤ (1 - r ^ 2)⁻¹
  rw [NormedRing.inverse_one_sub T hTlt]
```

Here `∑'` denotes an infinite sum, `T ^ n` an operator power, and `NormedRing.inverse_one_sub` identifies the inverse with the convergent series. The surrounding theorem concerns a particular positive Gram-type operator; it is not necessary to understand that later application yet. `ContinuousLinearMap.opNorm_comp_le` is the norm inequality for composition used elsewhere in the same source.

**Provenance and validation.** The excerpt is present in the supplied 2026-11-07 DKPS snapshot. The general Neumann facts are imported from Mathlib, while this application appears in the local `DavisKahan` development. No new Lean code has been compiled for this lecture.
