# Norms, distances, and convergence

<!-- BEGIN SPOKEN LECTURE -->

A vector can have a direction and a size. In elementary geometry, we usually measure its size by the square root of the sum of the squares of its coordinates. But that is not the only useful measure of size. And if we want to study spaces of functions, sequences, and eventually operators, we need an idea of size that does not depend on drawing an arrow in two or three dimensions.

The mathematical device is called a norm. A norm gives a nonnegative number to each vector. In this lesson we will work out what properties a norm needs, compare different norms on the very same space, and discover how a norm lets us talk about vectors approaching one another. By the end we will be able to say exactly what convergence means and why different notions of size may or may not describe the same limiting behavior.

## Three ways to measure the same vector

Take the vector whose two coordinates are three and four. Its ordinary Euclidean length is five. We can picture a right triangle with sides three and four, and its hypotenuse has length five.

Another way to measure this vector is to add the absolute values of its coordinates. Three plus four is seven. This is often called the one-norm.

A third way is to look only at the largest absolute coordinate. The larger of three and four is four. This is the infinity-norm, or maximum norm, in this finite-dimensional example.

So the same vector has length five under one convention, size seven under another, and size four under a third.

At first that may seem arbitrary. But different questions care about different kinds of cost. Suppose you are walking on a city grid and cannot cross a block diagonally. The total distance traveled from the origin to the point three blocks east and four blocks north is seven blocks, not five. The one-norm captures that restriction. Suppose instead you have two independent motors moving horizontally and vertically at once, each with a speed limit of one unit per second. The minimum time is four seconds, because the slower-to-finish coordinate determines the time. The maximum norm captures that kind of cost.

Neither measurement is a mistake. They describe different features of the same space. The goal is to identify the properties they share, so we can reason about them together.

## The rules for a norm

A norm must satisfy three requirements.

First, it gives a nonnegative size, and the only vector with size zero is the zero vector. We cannot call a nonzero vector genuinely length zero.

Second, scaling a vector scales its size in the expected way. If we double a vector, its norm doubles. If we reverse its direction, its norm stays the same. More generally, scaling by a number multiplies the norm by that number's absolute value. Over the complex numbers, we use the complex modulus.

Third, a norm must obey the triangle inequality. The size of the sum of two vectors is no more than the sum of their separate sizes. If you travel from one point to another by making a detour, that detour cannot be shorter than the direct distance under the same norm.

These rules are strong enough to support a great deal of analysis, yet flexible enough to include all three measurements we just tried.

Let us verify one of them, so the definition does some real work. For the one-norm, add the absolute values of all coordinates. The absolute value of the sum of two real numbers is at most the sum of their absolute values. Apply that scalar inequality to each coordinate and add the results. We obtain the triangle inequality for the one-norm.

For the maximum norm, look at any one coordinate of a sum. Its absolute value is at most the absolute value of the first coordinate plus the absolute value of the second. Each of those is bounded by the maximum absolute coordinate in its own vector. Therefore every coordinate of the sum is bounded by the sum of the two maximum norms. The largest coordinate is bounded too.

For Euclidean length, the proof uses the dot product. When we square the length of a sum, we obtain the squared length of the first vector, plus twice their dot product, plus the squared length of the second. The absolute dot product is no larger than the product of the lengths; that is the Cauchy–Schwarz inequality from linear algebra. So the squared length of the sum is no larger than the square of the sum of the two lengths. Both sides are nonnegative, and taking square roots gives the triangle inequality.

These are different proofs of the same structural property. The norm axioms allow us to use that property without repeating the coordinate calculation every time.

## Distances come from differences

Once we can measure a vector, we can measure the separation between two vectors. Subtract one from the other and take the norm of the difference.

The difference vector tells us what displacement would carry the first point to the second. Its norm tells us the cost or length of that displacement.

For example, take the points with coordinates one, two and four, six. Their difference is the vector three, four. The Euclidean distance is five, the one-norm distance is seven, and the maximum-norm distance is four.

The essential feature is that distance depends on a difference. If we shift both points by the same vector, their difference is unchanged and so is their distance. This is called translation invariance. We will use it constantly when comparing an approximation to the object it approximates.

The triangle inequality for vectors becomes the triangle inequality for distance. To travel from x to z by way of y, the displacement from x to z is the sum of the displacement from x to y and the displacement from y to z. Taking norms gives the corresponding bound on distances.

There is another consequence that is easy to overlook. The norm cannot change faster than the distance between its inputs. The difference between the sizes of two vectors is at most the size of their difference. To see why, the triangle inequality says that the size of x is at most the size of y plus the size of x minus y. Reverse the roles of x and y, and combine the two inequalities. This is sometimes called the reverse triangle inequality.

It tells us that a small change in the vector causes a small change in its measured size. That observation is one of the first bridges from geometry to continuity.

## Convergence is a statement about distance

Now imagine a sequence of vectors. A sequence is simply a list: first vector, second vector, third vector, and so on.

We say the sequence converges to a vector v when the distance from its terms to v eventually becomes smaller than any positive tolerance we choose.

Suppose we work in the plane and take the vector whose first coordinate is one divided by n and whose second coordinate is zero, where n runs through the positive integers. As n increases, the vector approaches the zero vector. Under Euclidean length its size is one divided by n. Under the one-norm and the maximum norm, its size is also one divided by n. In every case it approaches zero.

The important words are 'any positive tolerance.' If you demand a distance below one tenth, eventually the sequence meets it. If you demand one millionth, it eventually meets that too. There must be some stage after which every remaining term meets the chosen tolerance. Getting close once is not enough.

We do not require the sequence ever to equal its limit. One divided by n never becomes exactly zero at a finite positive integer n. Convergence describes the long-run behavior, not an eventual exact equality.

Because distance is defined using a norm, we can discuss limits in spaces of ordinary vectors, in spaces of continuous functions, and later in spaces of linear operators. We have enlarged the reach of the ideas from calculus without changing the fundamental meaning of a limit.

## Different norms in a fixed finite dimension

We have seen three norms assign different sizes to the same vector. Do they also disagree about which sequences converge?

On the plane, the answer is no for these three norms. In fact, there is a general theorem: on any fixed finite-dimensional real or complex vector space, all norms define the same convergent sequences and the same notion of continuity.

That statement does not mean the norms give equal numerical values. It means each norm can be bounded above and below by a positive constant multiple of another norm. Such bounds are called norm equivalence.

Let us prove some simple inequalities in an n-dimensional coordinate space. The largest absolute coordinate of a vector is at most its Euclidean length, because the square of that coordinate is one of the nonnegative terms in the sum of squared coordinates.

In the other direction, every coordinate has absolute value at most the maximum norm. Adding n squared upper bounds and taking a square root shows that Euclidean length is at most the square root of n times the maximum norm.

These two inequalities trap Euclidean length between the maximum norm and a constant multiple of it.

We can now prove that a sequence approaches zero under one of these norms exactly when it approaches zero under the other. If Euclidean lengths tend to zero, the smaller maximum norms do too. If maximum norms tend to zero, their multiples by the fixed number square root of n tend to zero, and Euclidean lengths are bounded by them.

The fact that n is fixed is essential. The constant square root of n grows when the dimension grows. We cannot quietly reuse this argument with one uniform constant across spaces of arbitrarily large dimension.

What about an arbitrary norm on the plane, not just one of our three examples? We can prove the same conclusion, but the argument needs one compactness fact from multivariable calculus.

Write a vector as a combination of the usual basis vectors. The triangle inequality shows that any norm of the vector is at most a fixed constant times the sum of the absolute coordinate values. That proves the norm is continuous as a function of ordinary Euclidean coordinates.

Now restrict this norm to the Euclidean unit sphere: all vectors whose Euclidean length is one. In a fixed finite dimension, that sphere is closed and bounded, hence compact. One meaning of compactness here is that every sequence of points on the sphere has a subsequence converging to another point on the sphere. To see why that is reasonable, use the elementary real-number fact that a bounded sequence has a convergent subsequence. Apply it to the first coordinate, then to the second along the chosen subsequence, and continue through the finitely many coordinates. The closed condition keeps the resulting limit on the sphere. A continuous real-valued function on a compact set attains a minimum; otherwise, points with values approaching its infimum would have a convergent subsequence, forcing that infimum to be attained. The minimum of our norm on that sphere must be strictly positive, because every point on the sphere is nonzero and norms vanish only at zero. Scaling any nonzero vector down to the unit sphere gives a positive constant lower bound for the arbitrary norm in terms of Euclidean length.

Together with the earlier upper bound, this proves that every norm in a fixed finite-dimensional space is equivalent to Euclidean length. We have not merely observed the result in a few examples; we have reconstructed the reason it is true.

## Why infinite dimension is different

Now comes an important boundary. The equivalence theorem is about a fixed finite-dimensional space. In infinite dimensions, two norms on the same underlying vector space can have different convergent sequences.

Consider the vector space of sequences of real numbers with only finitely many nonzero entries. Each vector is a finite list followed by zeros forever, so all sums we discuss are finite.

For each positive integer n, make a vector whose first n entries are one divided by n, with all later entries zero.

The one-norm adds the absolute entries. There are n of them, each one divided by n, so the one-norm is exactly one, for every n. Under that norm, these vectors do not converge to zero.

Under the Euclidean-style two-norm, we square the entries, add them, and take the square root. There are n nonzero entries. Each has square one divided by n squared. Adding those squares gives one divided by n. The square root is one divided by the square root of n. That tends to zero.

The vectors therefore converge to zero under one norm but not the other. We have not changed the underlying vectors, only how their size is measured.

This is one reason operator theory spends effort specifying which norm is in use. It is also why a claim about convergence or smallness in an infinite-dimensional space cannot be understood without identifying its topology. That word, topology, refers here to the collection of sets we regard as neighborhoods and therefore to the notion of approaching a point. A norm produces one such notion through its distances.

## A reconstruction exercise

Suppose a vector in a five-dimensional coordinate space has maximum norm at most one hundredth. How large can its Euclidean norm be? Each coordinate has absolute value at most one hundredth. The sum of five coordinate squares is at most five ten-thousandths, so Euclidean norm is at most the square root of five times one hundredth. You do not need the exact decimal. The critical point is that the factor depends on the dimension, but does not depend on the particular vector.

Now reverse the direction. If the Euclidean norm is at most one hundredth, every individual coordinate is at most one hundredth in absolute value, and so the maximum norm is at most one hundredth.

For a more conceptual exercise, see whether you can reconstruct the reverse triangle inequality. The steps are: express x as y plus the difference x minus y; use the triangle inequality; repeat with x and y exchanged; then combine the two one-sided bounds. The final claim is that the absolute difference between the two norms is at most the norm of their difference.

## The point to carry forward

A norm is a consistent notion of vector size: it is positive except at zero, scales correctly, and satisfies the triangle inequality. It defines distance by measuring differences, and distance defines convergence. In a fixed finite-dimensional space, all norms agree about convergence even when they disagree about exact sizes. In infinite dimensions, that agreement can fail.

Our next question is whether a sequence that gets progressively closer to itself must approach some vector that belongs to our space. That question leads to Cauchy sequences, completeness, and Banach spaces. It will also explain why infinite sums of vectors or operators sometimes exist and sometimes do not.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (not TTS narration)

For a normed vector space \(E\), the norm satisfies
\[
\|x\|\ge 0,\quad \|x\|=0\iff x=0,\quad
\|a x\|=|a|\|x\|,\quad \|x+y\|\le \|x\|+\|y\|.
\]
The reverse triangle inequality is \(|\|x\|-\|y\||\le\|x-y\|\). The induced metric is \(d(x,y)=\|x-y\|\). For the coordinate norms on \(\mathbb R^n\), \(\|x\|_\infty\le\|x\|_2\le\sqrt n\|x\|_\infty\).

**Exact source anchors.** The foundational `NormedAddCommGroup E` hypothesis occurs throughout the supplied DKPS/ForTauCeti formalization. The following declaration is copied from `DavisKahan/BoundedOperator/Problem.lean`:

```lean
@[expose]
def IsometricEmbedding (X : F →L[𝕜] E) : Prop := ∀ x, ‖X x‖ = ‖x‖
```

`‖x‖` represents the norm, and `∀ x` means the equality must hold for every input. The type `F →L[𝕜] E` describes a **continuous linear** map; its construction is a later lesson. This predicate says that such a map preserves norm exactly, a stronger property than mere continuity or boundedness. It is used when expressing approximate invariant pairs in the maintained Davis–Kahan code.

A separate preexisting Mathlib theorem is used in `visualizations/lectures/000010_basics/facts.lean`:

```lean
example (x : E) :
    ⟪x, x⟫_ℝ = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x
```

Here `⟪x, x⟫_ℝ` denotes the real inner product, and the equation identifies Euclidean-style squared length with self-pairing. This statement requires the real inner-product-space context present in the source file. We will develop that extra structure in lectures `009000` onward.

These are source-verified correspondences, not newly compiled companion files. The spoken script ends before this appendix.
