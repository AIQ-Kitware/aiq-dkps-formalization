# Real and complex scalars

<!-- BEGIN SPOKEN LECTURE -->

Real and complex scalars support different kinds of linearity. A real-linear map preserves sums and multiplication by real numbers; a complex-linear map must also preserve multiplication by the imaginary unit. We will see how complexification changes eigenvalue and spectral questions.

This is not a detour. The distinction changes what an eigenvalue can be, what it means for an operator to have an inverse after subtracting a scalar, and eventually how we build a spectral theory that works even when an operator has no eigenvectors at all.

The main idea is simple: moving from real to complex scalars allows us to describe rotations in a way that the real numbers alone cannot. But the move has rules. We cannot just put imaginary numbers into an existing calculation and assume that every definition stays unchanged.

## What a complex number does

A complex number has two real components. We write it as a real part plus an imaginary part. The imaginary unit, pronounced eye, is a number whose square is negative one. For example, three plus two eye is a complex number with real part three and imaginary part two.

Addition works component by component. Multiplication is governed by ordinary distributivity and the rule that eye squared is negative one. Multiply one plus eye by one minus eye. The mixed terms cancel, and the last term subtracts eye squared, so the product is two.

A useful way to visualize the complex numbers is as a plane. The horizontal coordinate is the real part and the vertical coordinate is the imaginary part. Multiplying by eye rotates this plane by a quarter turn counterclockwise. Apply the multiplication twice and you rotate through a half turn, which is the same as multiplying by negative one.

Every complex number also has a conjugate. To conjugate a number, keep the real part and reverse the sign of the imaginary part. For three plus two eye, its conjugate is three minus two eye.

Multiplying a number by its conjugate gives the sum of the squares of its real and imaginary parts. This is a nonnegative real number. Its square root is the modulus, or absolute value, of the complex number. For three plus four eye, the modulus is five.

Here is why we care about the modulus. It provides a notion of size that does not change when we multiply by a complex number of modulus one. A pure rotation changes direction, but not length. We can build norms and operator norms over the complex numbers just as we did over the real numbers.

## A real operator that asks for complex numbers

Take the real plane, with a vector described by a horizontal coordinate and a vertical coordinate. Define an operator R that turns every vector through a quarter turn counterclockwise. It sends the pair x, y to the pair negative y, x.

This is a real-linear map. It respects sums and real scalar multiples. If we apply it twice, every vector reverses direction. In symbols we could say that R squared is negative the identity.

Now ask whether this rotation has a real eigenvector. An eigenvector would be a nonzero direction that stays on its own line after applying R, changing only by multiplication by some real eigenvalue.

But a quarter turn sends every nonzero real direction to a perpendicular direction. So no nonzero real vector can be an eigenvector of R.

Does that mean the operator has no spectral information? Not at all. It means we need a broader setting in which to look.

Allow the two vector coordinates to be complex. The same rule, sending x, y to negative y, x, now defines a complex-linear operator on the complex two-dimensional space. If we apply it to the vector whose coordinates are one and negative eye, the result is eye and one. That is eye times the original vector. So eye is an eigenvalue.

Similarly, the vector one, eye has eigenvalue negative eye. We have not changed the numerical entries of the rotation matrix. We have changed the scalar field in which its eigenvectors and eigenvalues are allowed to live.

The two complex eigenvectors are not two real directions hiding in the original plane. They are useful algebraic descriptions of the real rotation. In fact, their eigenvalues occur as a conjugate pair, matching the reality of the original matrix.

## Why the scalar field matters to invertibility


Pick a real number a, subtract the rotation operator R from a times the identity, and ask whether the result has an inverse.

Remember that R squared is negative the identity. Multiply the operator a times the identity minus R by a times the identity plus R. The cross terms cancel. What remains is a squared times the identity minus R squared, or a squared plus one, times the identity.

For any real a, a squared plus one is positive. Therefore the operator a times the identity minus R is invertible; its inverse is a times the identity plus R, divided by a squared plus one.

But over complex numbers, we can choose a equal to eye. Then a squared plus one is zero, and the operator fails to be invertible. The same happens for negative eye.

So looking only at real scalar shifts would miss the very values that characterize this rotation. This is one reason the complex scalar field is the standard home for the general theory of operator spectra.

## What is complexification?

Suppose we begin with a real vector space E. A way to introduce complex coordinates is to consider formal expressions x plus eye times y, where x and y are vectors in E. Addition is componentwise. Multiplication by a complex number mixes the two real components, in the same way complex multiplication mixes the real and imaginary parts of a complex number.

This construction is called complexification. It creates a complex vector space from a real one without discarding the original real vectors. We can identify each real x with x plus eye times zero.

If T is a real-linear operator, we extend it by acting separately on both components: T of x plus eye times y becomes T of x plus eye times T of y. That extended map is complex-linear. We call it the complexification of T.

For finite-dimensional real spaces this is particularly transparent. We keep the same real matrix and permit complex inputs. In infinite-dimensional normed or Hilbert spaces, there is additional work: we must choose the correct norm or inner product on the new complex space and show that the extended operator is bounded. We will develop those structures later rather than assume them now.

Complexification gives us a useful bridge. Sometimes a theorem is easier to prove for complex operators, because complex spectral methods are available. We can then ask whether the result restricts to the original real setting. But that final step requires an argument; a complex theorem is not automatically a real theorem with the words changed.

## A caution about complex linearity

There is also an important difference between real linearity and complex linearity.

Consider complex conjugation, viewed as a map from the complex numbers to themselves. It takes x plus eye y to x minus eye y. It respects addition, and it respects multiplication by real numbers. So it is real-linear.

But it is not complex-linear. Conjugating eye times one gives negative eye. On the other hand, eye times the conjugate of one is positive eye. Those are different.

In other words, even when a space has complex scalars, not every transformation that looks linear over the real numbers is linear over the complex numbers. We must always say which scalar field we mean.

The distinction has a mathematical consequence: a map preserving real linear combinations need not preserve multiplication by the complex unit. Complex-linear theorems can only be applied after complex linearity has been established.

## What to retain

Try to reconstruct three arguments without looking back.

First, why does a quarter-turn rotation have no nonzero real eigenvector, but two conjugate complex eigenvalues? Work directly with the vectors one, negative eye and one, eye.

Second, take the product of a times the identity minus R and a times the identity plus R. Explain why the resulting inverse formula works for every real a, and why it can fail at a complex value.

Third, explain why complex conjugation is real-linear but not complex-linear. Your explanation should use the definition of linearity rather than a slogan about imaginary numbers.

We have learned that the scalar field is not background decoration. It determines which multiples count as scalars and therefore which eigenvalues and inverses we can discuss.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

Write the real quarter-turn operator as
\[
R=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad R^2=-I.
\]
Over \(\mathbb R\), \((aI-R)^{-1}=(aI+R)/(a^2+1)\) for every real \(a\). Its complexification has characteristic polynomial \(z^2+1\), with eigenvalues \(i\) and \(-i\). An example of eigenvectors is \((1,-i)\) for eigenvalue \(i\), and \((1,i)\) for eigenvalue \(-i\).

For a real-linear map \(T:E\to E\), the complexified map obeys \(T_{\mathbb C}(x+iy)=Tx+iTy\). Normed and inner-product complexification need additional structure, developed in later lessons.

**Lean bridge.** A source-grounded result in `ForTauCeti/Analysis/InnerProductSpace/Complexification/Spectrum.lean` states, for a real Hilbert space and bounded real-linear operator, that real invertibility is preserved and reflected by complexification:

```lean
theorem isUnit_complexify_iff {T : E →L[ℝ] E} :
    IsUnit (complexify T) ↔ IsUnit T :=
  ⟨isUnit_of_isUnit_complexify, isUnit_complexify_of_isUnit⟩
```

Here `E →L[ℝ] E` is a *bounded real-linear* map, while `complexify T` is a *bounded complex-linear* map on the complexified space. `IsUnit` means invertible inside the appropriate operator algebra. The file also proves the corresponding equivalence for real spectral points. Those Hilbert-space hypotheses and spectral APIs will become meaningful over later lectures; this is an advance view of why we cannot omit scalar types.

**Source and provenance.** The excerpt appears in the provided DKPS snapshot, in the current `ForTauCeti` tree. The source header explicitly describes relocation from earlier DKPS complexification modules; its location does not erase that origin. Checked against source text, not recompiled for this draft.
