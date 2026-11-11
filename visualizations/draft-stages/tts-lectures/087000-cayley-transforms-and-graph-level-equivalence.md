# 087000 — Cayley transforms and graph-level equivalence

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `014000` unitary operators, `083000` graphs, `086000` resolvents. **Next:** `088000` unbounded spectral theorem.

<!-- BEGIN SPOKEN LECTURE -->

# The Cayley transform: encoding an unbounded operator in a unitary

Imagine trying to describe an unbounded self-adjoint operator using only bounded operators. At first that sounds impossible. If the original operator can amplify some unit vectors by arbitrarily large amounts, how could a bounded operator retain enough information to reconstruct it?

The answer is that the bounded operator can carry information in the failure of another bounded map to have a bounded inverse. The Cayley transform gives a precise version of this idea.

It turns a self-adjoint operator into a unitary operator, meaning a linear transformation that preserves lengths and is onto. And from that unitary, we can recover the original operator together with its domain.

## Begin with a resolvent

Let A be a self-adjoint operator on a complex Hilbert space. Its domain may be proper, and A may be unbounded.

A useful theorem says that if we shift a self-adjoint operator by a nonreal complex number, the shifted operator has an inverse that is bounded and defined on the whole Hilbert space. In particular, both A plus i times the identity and A minus i times the identity are bijections from the domain of A onto the Hilbert space.

Here i is the imaginary unit, the number whose square is negative one.

The Cayley transform uses these two shifts. To apply it to an arbitrary vector y, first invert A plus i. That produces some vector x in the domain of A. Then apply A minus i to x.

The input to the second step is guaranteed to be legal. That is crucial. We have constructed a map on the whole Hilbert space, even though its formula includes an unbounded operator.

Call the resulting map U. It is the Cayley transform of A.

We can rewrite the formula without explicitly applying A. The expression A minus i is the same as A plus i minus two i. Therefore U equals the identity minus two i times the inverse of A plus i.

The inverse in this formula is a bounded resolvent. So U is bounded, too.

But something stronger is true: U is unitary.

## Why the Cayley transform preserves length

Take any vector x in the domain of A. Compare the lengths of A x plus i x and A x minus i x.

When we square these lengths, both expressions contain the squared length of A x and the squared length of x. The cross terms have opposite signs. They disappear when compared because the inner product of A x with x is real for a self-adjoint operator.

Thus A plus i applied to x and A minus i applied to x have equal lengths.

Now start with an arbitrary vector y. Because A plus i is onto, there is a domain vector x for which y equals A plus i applied to x. By definition, U y equals A minus i applied to that same x. The equality we just proved gives equal lengths for y and U y.

So U preserves every vector's length.

It is also onto. Given any target v, solve A minus i applied to x equals v, and then choose y to be A plus i applied to x. The Cayley transform sends that y to v.

A surjective linear isometry is unitary. We have converted a possibly unbounded self-adjoint operator into an everywhere-defined bounded unitary operator.

## A calculation with a single spectral value

Before discussing infinite dimensions, try the formula on an ordinary scalar. Suppose A is just multiplication by the real number one.

The Cayley transform multiplies by one minus i divided by one plus i. Multiplying numerator and denominator appropriately gives negative i. The complex number negative i lies on the unit circle, so it preserves absolute value.

If A is multiplication by two, the Cayley scalar is two minus i divided by two plus i. This is also on the unit circle.

In fact, for any real lambda, lambda minus i and lambda plus i have the same absolute value. Their ratio must therefore have magnitude one.

This scalar picture helps explain the operator result. The real line is being mapped around the unit circle. The transform replaces unbounded real spectral values with unit-magnitude complex values.

There is one point on the circle that no finite real lambda reaches: the number one. As lambda becomes very large in either direction, its Cayley value approaches one.

That exceptional point is where information about unboundedness is stored.

## The domain is hiding in one minus U

From the earlier formula, U equals the identity minus two i times the inverse of A plus i. Rearranging, one minus U equals two i times that resolvent.

Now think about the range. The inverse of A plus i takes the whole Hilbert space onto the domain of A. It lands in every allowed input, and only allowed inputs. Multiplying by two i does not change the range.

Therefore the range of one minus U is exactly the domain of A.

This is the central reconstruction fact. The bounded operator one minus U has a range that may be a dense, proper subset of the Hilbert space. That subset remembers the domain of the unbounded operator.

Can we also recover the action of A? Yes.

Take any vector y and form x equal to one minus U applied to y. We already know x lies in the domain of A. Then A applied to x equals i times one plus U applied to y.

We can verify this with a direct substitution. Let v be the inverse of A plus i applied to y. Then one minus U applied to y equals two i times v. And one plus U applied to y equals two times A applied to v. Multiplying the latter by i gives two i times A v, exactly A applied to the former.

So the action of A is recovered from U by this equation. There is no ambiguity in choosing y, because one minus U is injective.

Why injective? If U y equaled y, write y as A plus i applied to a domain vector v. The equation would force A minus i applied to v to equal A plus i applied to v. Subtracting shows v is zero, so y is zero.

U has no nonzero fixed vector. Equivalently, one is not an eigenvalue of U.

## Why missing an eigenvalue is not enough

It is tempting to conclude that because one is not an eigenvalue, one minus U must be invertible on the whole Hilbert space. That conclusion is false in infinite dimensions.

Return to ell two and let A multiply coordinate N by N, on its weighted square-summability domain.

Every coordinate vector is an eigenvector of A. Its eigenvalue is N. Under the Cayley transform, that coordinate vector has eigenvalue N minus i divided by N plus i.

None of those Cayley eigenvalues equals one. But they approach one as N increases.

So we can find unit vectors whose images under one minus U get arbitrarily small. If one minus U had a bounded inverse on the whole space, that could not happen.

The number one belongs to the spectrum of U as a limit of its eigenvalues, although it has no eigenvector there.

And look at what the range of one minus U is: precisely the proper domain of our original diagonal operator. That is how the bounded Cayley transform retains the unboundedness of A.

## Can every suitable unitary be reversed?

Yes. Start with a unitary operator U that has no nonzero fixed vector. Define a candidate domain to be the range of one minus U.

First check density. If a vector were orthogonal to this range, the adjoint of one minus U would send it to zero. Since U is unitary, that would force the vector to be fixed by U. Only zero is fixed. Thus the range is dense.

Now define A on this range. For an input of the form one minus U applied to y, set A of that input equal to i times one plus U applied to y. Injectivity of one minus U makes the definition single valued.

The unitary identity shows that this operator is symmetric. The shifted equations are especially revealing: A plus i applied to that domain vector equals two i times y, while A minus i applied to it equals two i times U y. Both shifts are onto the whole Hilbert space.

For a densely defined symmetric operator, surjectivity of both nonreal shifts implies self-adjointness. So the reconstructed A is self-adjoint, and its Cayley transform is exactly U.

We have a genuine correspondence: self-adjoint operators, including unbounded ones, are encoded by unitary operators with no nonzero fixed vector.

The bounded unitary carries the geometry. The range of one minus U carries the domain. And the reconstruction equation recovers the operator's action. None of those pieces can be omitted if we want the original unbounded operator back.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Use \(U=(A-iI)(A+iI)^{-1}=I-2i(A+iI)^{-1}\). This bounded operator is unitary, \(\ker(I-U)=0\), and \(D(A)=\operatorname{Ran}(I-U)\). Recover the graph by \(A((I-U)y)=i(I+U)y\). The source's `LinearPMap.resolvent A (-i)` is the inverse of \((-i)I-A\); hence its displayed identity \(I-U=-2iR(-i)\) agrees with the lecture's \(I-U=2i(A+iI)^{-1}\). The Cayley spectral point \(1\) can belong to continuous spectrum despite having no eigenvectors.

### Scalar and diagonal checks

For the chosen Cayley convention,
\[c(\lambda)=\frac{\lambda-i}{\lambda+i},\quad c(1)=-i,\quad
1-c(\lambda)=\frac{2i}{\lambda+i}.\]
For \(A=\operatorname{diag}(1,2,3,\ldots)\) on its maximal domain,
\(Ue_n=c(n)e_n\), \(c(n)\to1\), and \(Ue_n\ne e_n\). Hence
\(1\in\sigma(U)\) but \(\ker(I-U)=\{0\}\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `one_sub_cayley_apply`:

```lean
theorem one_sub_cayley_apply (ξ : H) :
    ((1 : H →L[ℂ] H) - A.cayley) ξ
      = -((2 * Complex.I) • resolvent A (-Complex.I) ξ) := by
```

This is the exact convention-sensitive Cayley/resolvent identity.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `injective_one_sub_cayley`:

```lean
theorem injective_one_sub_cayley :
    Function.Injective ((1 : H →L[ℂ] H) - A.cayley) := by
```

It proves the Cayley transform has no nonzero fixed vector.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `spectralPVM_def`:

```lean
theorem spectralPVM_def :
    spectralPVM hA
      = BorelCalculus.toProjValMeasure (hA.isStarNormal_cayley)
          (measurable_cayleyInv A) := (rfl)
```

The unbounded self-adjoint spectral measure is recovered by relabeling the Borel calculus of the Cayley unitary.

**Scope:** The full converse Cayley correspondence and graph-reconstruction calculations are established in the lecture; the displayed declarations are selected bridge results from the actual project source. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
