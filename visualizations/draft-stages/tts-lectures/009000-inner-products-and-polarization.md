# Inner products and polarization

<!-- BEGIN SPOKEN LECTURE -->

We have spent several lessons studying length, distance, limits, and bounded operators. But a norm tells us only how long a vector is. It does not immediately tell us whether two vectors are perpendicular, whether they point mostly in the same direction, or how much of one vector lies along another.

Today we add a structure that answers those questions: the inner product. In ordinary Euclidean space it is the dot product. In more general spaces it is a rule that measures the relationship between two vectors and recovers their lengths as a special case.

We will build the basic rules, prove the Cauchy–Schwarz inequality, see why an inner product gives us geometry that a general norm does not, and learn how the inner product can actually be recovered from the norm by polarization.

## Start with a dot product

Consider two ordinary vectors in the plane. Let x point three units to the right and four units up. Let y point one unit to the right and zero units up.

Their dot product is three times one plus four times zero, which is three. Their lengths are five and one. Dividing the dot product by the product of their lengths gives three fifths, the cosine of the angle between them.

But the dot product contains more than an angle. If y points straight up instead, the dot product becomes four. And if y points four units right and negative three units up, the dot product is zero. The vectors are perpendicular.

So the dot product knows something that length alone cannot directly express: how two directions interact.

In two dimensions we define the dot product by multiplying matching coordinates and adding the results. The same rule works in three dimensions and in any finite-dimensional real Euclidean space. We now want to identify the properties that matter, without depending on a particular coordinate basis.

## The defining rules

An inner product takes two vectors and returns a scalar. For a real vector space, that scalar is real. We require the rule to be linear in each argument, symmetric when we swap the arguments, and positive when we take the inner product of a vector with itself.

More precisely, the inner product of a vector with itself is nonnegative, and equals zero only for the zero vector. That last clause prevents a nonzero vector from having zero length.

From the inner product we define the norm of a vector as the square root of its inner product with itself. Our familiar Euclidean norm comes from the familiar dot product this way.

We have not yet proved this is a norm in the full sense, because the triangle inequality is not an immediate part of the definition. The Cauchy–Schwarz inequality supplies what we need.

## Why the complex case needs conjugation

Recall that a complex number may have an imaginary part. If we naively multiply complex coordinates and add, the dot product of a vector with itself need not be nonnegative or even real. The simplest example is the one-coordinate vector eye. Multiplying eye by itself gives negative one, which cannot represent a squared length.

The fix is to conjugate one factor. For a complex vector with two coordinates, take the conjugate of the first vector's first coordinate times the second vector's first coordinate, then add the corresponding product for the second coordinate.

With the same vector on both sides, each term becomes a complex number times its conjugate. The sum is real and nonnegative. This produces the squared Euclidean length of the complex vector.

We will use the convention that the inner product is linear in the second argument and conjugate-linear in the first. Conjugate-linear means that multiplying the first vector by a complex scalar multiplies the inner product by the conjugate of that scalar. Swapping the two input vectors conjugates the answer. These rules are called conjugate symmetry and sesquilinearity.

Over the real numbers, conjugation does nothing, so the complex rules reduce to the ordinary symmetric bilinear dot product. Some books use the opposite convention for which argument is linear. The mathematics works either way, but we must be consistent. In particular, we will state the convention when translating formulas to Lean.

## Proving Cauchy–Schwarz

The Cauchy–Schwarz inequality says that the absolute value of the inner product of x and y is no greater than the product of their lengths.

Why should that be true? Imagine trying to remove from x the part that points along y. If y is nonzero, choose a multiple of y so that the remainder is perpendicular to y.

The required multiple is the inner product of y with x, divided by the squared length of y. Subtract that multiple of y from x. Call the resulting vector r.

By linearity in the second argument, the inner product of y with r is zero. That is the algebraic definition of orthogonality.

Now consider the squared length of r. Expand the inner product of r with itself. The mixed terms cancel in exactly the right way, leaving the squared length of x minus the squared absolute value of the inner product of y with x, divided by the squared length of y.

Since squared lengths cannot be negative, that expression must be at least zero. Rearranging gives the Cauchy–Schwarz inequality. If y is zero, the inequality is immediate, so the proof handles all cases.

There is a geometric interpretation too. The selected multiple of y is the component of x along y. Whatever remains is perpendicular, so no component of x along y can be longer than x itself.

Notice that we did not merely quote the inequality. We constructed a perpendicular remainder and used its nonnegative squared length. That proof will reappear when we build orthogonal projections.

## Deriving the triangle inequality

We can now prove that the norm induced by an inner product really is a norm.

Take the squared length of x plus y and expand. We obtain the squared length of x, plus the squared length of y, plus twice the real part of the inner product of x with y.

The real part can never exceed the absolute value of a complex number. By Cauchy–Schwarz, that absolute value is at most the length of x times the length of y.

Therefore the squared length of x plus y is at most the square of the sum of the two lengths. Taking square roots gives the triangle inequality.

The proof makes the geometry visible: adding two vectors is longest when they point in the same direction, and the cross term measures how closely they align.

This also gives us the familiar Pythagorean theorem. If x and y are orthogonal, the inner product cross term is zero, so the squared length of their sum equals the sum of their squared lengths.

## The parallelogram law

Let us now turn the direction around. Does every norm come from some inner product?

An inner-product norm must obey a special identity called the parallelogram law. The sum of the squared lengths of x plus y and x minus y equals twice the squared length of x plus twice the squared length of y.

To see why, expand both squared lengths. In the first expansion the mixed terms are added; in the second they are subtracted. They cancel, leaving two copies of each squared length.

Why call it a parallelogram law? If x and y describe two adjacent sides of a parallelogram, then x plus y and x minus y describe its diagonals. The identity relates the squares of the diagonal lengths to the squares of the side lengths.

Now try a different norm on the plane. Measure the vector with coordinates x and y by adding the absolute values of its coordinates. This is called the one norm.

Take one vector along the horizontal axis with length one and another along the vertical axis with length one. Their sum has one-norm two, and so does their difference. The sum of the squares of these lengths is eight. But twice the squared norm of each original vector adds up to only four.

The parallelogram law fails. Therefore this norm does not come from any inner product. It is a perfectly valid norm; it just does not carry the special geometric structure that an inner product provides.

## Recovering the inner product from lengths

Here is the surprising converse idea. If a norm really does come from an inner product, then the lengths alone are sufficient to recover that inner product.

In a real inner-product space, subtract the squared length of x minus y from the squared length of x plus y. By expanding both expressions, we find that the difference is four times the inner product of x and y.

So the inner product is one quarter of that difference. This is the real polarization identity.

It tells us that an inner product can be reconstructed from measurements of sums and differences. Even if someone gives us only lengths, we can recover angles and orthogonality, provided those lengths satisfy the special structure of an inner-product norm.

Over complex numbers, there is an additional problem: squared lengths are real, while the inner product may be complex. The real polarization identity recovers only its real part. To recover the imaginary part, we also compare the squared lengths of x plus eye times y and x minus eye times y. With our choice of which argument is linear, this second difference has the opposite sign from four times the imaginary part.

Combining the two measurements recovers the entire complex inner product. Conjugation is not an incidental detail here; it determines the correct sign in the complex polarization formula.

## Why this matters for the course

Our next lesson will introduce Hilbert spaces: inner-product spaces that are complete under the norm we just constructed. Their geometry lets us define perpendicular complements and, eventually, nearest-point projections onto closed subspaces.

Later, the inner product lets us express a Gram matrix, a matrix of pairwise inner products among vectors. It also supports adjoints, whose defining equation moves an operator from one side of an inner product to the other. Those are among the fundamental constructions needed for the Davis–Kahan theory.

But the main idea today is simpler. A norm measures the size of one vector. An inner product measures how two vectors fit together, while also determining their sizes.

To check that you understand the mechanism, try reconstructing three things. Why is the complex dot product conjugated in one argument? Why does subtracting the component of x along y prove Cauchy–Schwarz? And why does the one norm on the plane fail the parallelogram test?

If you can answer those, you have the conceptual and algebraic ingredients needed to begin Hilbert-space geometry.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For the convention conjugate-linear in the **first** argument and linear in the **second**, an inner product satisfies \(\langle x,x\rangle\ge0\), \(\langle x,x\rangle=0\iff x=0\), and \(\langle x,y\rangle=\overline{\langle y,x\rangle}\). The induced norm is \(\|x\|=\sqrt{\langle x,x\rangle}\). The Cauchy–Schwarz inequality is \(|\langle x,y\rangle|\le\|x\|\|y\|\).

The real polarization formula is
\[
\langle x,y\rangle=\tfrac14\big(\|x+y\|^2-\|x-y\|^2\big).
\]
The complex formula, for our convention, is
\[
\langle x,y\rangle=\tfrac14\big(\|x+y\|^2-\|x-y\|^2
-i\|x+iy\|^2+i\|x-iy\|^2\big).
\]
The parallelogram identity is \(\|x+y\|^2+\|x-y\|^2=2\|x\|^2+2\|y\|^2\).

**Lean bridge.** The source `ForTauCeti/Analysis/InnerProductSpace/VectorAngle.lean` develops vector angles over either real or complex scalars and uses the real part of the inner product:

```lean
noncomputable def vectorAngle (x y : E) : ℝ :=
  Real.arccos (RCLike.re (inner 𝕜 y x) / (‖x‖ * ‖y‖))
```

The surrounding declarations assume `[RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]`. Thus `𝕜` is a real-or-complex scalar type; `inner 𝕜 y x` is the scalar-valued inner product; `RCLike.re` extracts its real part; and the norm is inherited from the inner-product-space structure. Later lectures will distinguish vector angle from angle between one-dimensional *subspaces*, which is a different normalization over the complex field.

**Source and provenance.** The source header identifies this construction as DKPS-origin mathematical infrastructure for Davis–Kahan Proposition 3.5, now situated in the `ForTauCeti` tree. The formula and declaration were checked against the uploaded snapshot, not independently compiled here. The polarization identities in this appendix are standard mathematical derivations, not claimed to be declarations in that file.
