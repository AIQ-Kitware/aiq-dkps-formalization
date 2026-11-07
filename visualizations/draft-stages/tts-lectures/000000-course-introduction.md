# Course introduction: What survives when a matrix changes?

## The problem

Suppose we have a mathematical model that tells us something important about a system. Maybe it describes the ways a structure can vibrate. Maybe it describes the dominant patterns in a cloud of measurements. Or maybe it represents the interactions of a network. We analyze the model, find some special directions, and use those directions to understand what the system is doing.

Then the model changes. We collect a new batch of measurements, or improve an approximation, or account for a small physical effect we had ignored. The new matrix is close to the old one. Should we expect those special directions to be close as well?

That question sounds as though it ought to have a simple answer. Small change in, small change out. But for eigenvectors, it is false without additional assumptions. A matrix can change by an arbitrarily small amount while an eigenvector selected by its eigenvalue turns through a right angle.

That does not mean eigenvectors are hopelessly unstable. It means we need to understand what makes a direction identifiable in the first place. Often the answer involves a gap between eigenvalues. Just as importantly, it involves deciding whether we really care about an individual eigenvector or about an entire subspace, a collection of directions considered together.

By the end of this introduction, three claims should make sense. Eigenvalues can remain stable while selected eigenvectors do not. Separation from competing eigenvalues can protect a direction or a subspace. And the right mathematical measure of movement depends on what we are trying to preserve.

The rest of the course will turn those observations into precise statements, proofs, and useful methods. But we can already see the essential problem with a matrix small enough to describe without drawing it.

## A tiny change and a ninety-degree turn

First, a quick reminder of what an eigenvector is. A matrix acts on a vector and produces another vector. An eigenvector is a nonzero vector whose image points along the same line as the original. The matrix may stretch it, shrink it, or reverse it, but it does not send it off that line. The number describing the stretching is the eigenvalue.

Consider a two-by-two diagonal matrix. Its top-left entry is one. Its bottom-right entry is one plus a small positive number, which we will call delta. Its other two entries are zero.

Because the matrix is diagonal, we can read off its eigenvectors. The horizontal coordinate direction has eigenvalue one. The vertical coordinate direction has eigenvalue one plus delta. The smaller eigenvalue belongs to the horizontal direction.

Now make another diagonal matrix by exchanging those two diagonal entries. The top-left entry is one plus delta, and the bottom-right entry is one. Again, the other entries are zero.

The second matrix has exactly the same two eigenvalues as the first. Not approximately the same; exactly the same. But the direction associated with the smaller eigenvalue has switched. It was horizontal. Now it is vertical. Those directions meet at ninety degrees.

How different are the two matrices? Their difference is another diagonal matrix, with delta in one diagonal position and negative delta in the other. If we measure a matrix by the greatest amount it can stretch a vector of length one, the size of that difference is delta.

And delta can be as small as we like.

So here are two matrices, as close as we please in that measurement, with identical eigenvalue lists, whose smallest-eigenvalue directions are perpendicular.

There is no contradiction. Notice what we had to do to make this example work. The two original eigenvalues were separated by only delta. As the matrix change became smaller, the distinction between the two eigenvalues became smaller too. We were asking the matrix to tell us which of two nearly tied directions should come first. A perturbation large enough to reverse that near tie changes the answer completely.

This is the first principle of the course: the absolute size of a perturbation is not enough. It has to be compared with the separation that protects the information we care about.

## The significance of a gap

Let's call that separation a spectral gap. For now, think of it as the distance between the eigenvalue associated with a direction of interest and the competing eigenvalues. Later we will need more careful definitions, because different theorems require different kinds of spectral separation.

Imagine a second two-by-two diagonal matrix. This time its diagonal entries are zero and ten. The horizontal direction has eigenvalue zero. The vertical direction has eigenvalue ten. There is a substantial difference between what the matrix does along those two directions.

Suppose we add a small interaction that mixes the horizontal and vertical coordinates. To be concrete, put a small positive number, epsilon, in both off-diagonal positions. The resulting matrix remains symmetric: the amount by which the horizontal coordinate influences the vertical one is the same as the amount by which the vertical coordinate influences the horizontal one.

The eigenvectors will usually rotate. But how much?

If epsilon is tiny compared with ten, the rotation is small. The original matrix treats the two coordinate directions very differently, so a weak coupling has difficulty mixing them. If, instead, the diagonal entries are zero and a very small positive number, the same coupling can cause a much larger rotation. The two directions were already almost indistinguishable as far as the original matrix was concerned.

In this particular symmetric two-by-two example, the angle of the lower-eigenvalue direction away from the horizontal has a clean formula. Twice the magnitude of that angle has tangent equal to two epsilon divided by the diagonal gap. The angle is chosen between zero and forty-five degrees when epsilon and the gap are positive.

We do not need to memorize that formula now. What matters is the ratio. Epsilon measures how hard we mix the directions. The gap measures how firmly the original matrix distinguishes them. A weak interaction relative to the gap gives a small rotation. An interaction large relative to the gap can give a substantial rotation.

There is a useful analogy with two musical notes. When their frequencies are far apart, a weak coupling has one kind of effect. When they are nearly in tune, that same coupling can make their modes strongly mix. The analogy is not a proof, but it points to the right structural question: how far apart are the modes we are trying to tell apart?

We will spend much of the course making this comparison rigorous. The exact constant, the meaning of separation, and even the appropriate function of the angle will depend on the assumptions. Those distinctions are mathematical substance, not bookkeeping.

## Why eigenvalues tell only part of the story

We should distinguish two kinds of stability that are easy to conflate.

For real symmetric matrices, the eigenvalues can be arranged from smallest to largest. A fundamental result tells us that changing the matrix by a small amount, measured in the operator norm, changes each eigenvalue in that ordered list by no more than that amount. Eigenvalue stability is a remarkably robust fact in this setting.

But knowing that the numerical eigenvalues have changed little does not tell us which direction belongs to which one. Our first example made the distinction as stark as possible. The eigenvalue lists did not change at all, while the direction of the smallest eigenvalue switched from horizontal to vertical.

This matters when eigenvectors have an interpretation. In data analysis, a leading eigenvector of a covariance matrix may represent a dominant direction of variation. In a mechanical model, an eigenvector may describe a vibration mode. In a numerical computation, an eigenvector may be part of a representation that later algorithms use.

If two eigenvalues are nearly equal, the model may not support a reliable distinction between their individual eigenvectors. It may still support a reliable distinction between the space they span and everything outside that space.

That is why the next object we need is not a more elaborate formula for individual vectors. It is the idea of a subspace.

## A subspace can be stable when its basis is not

A subspace is a collection of vectors closed under addition and scalar multiplication. In familiar three-dimensional space, a line through the origin is a one-dimensional subspace. A plane through the origin is a two-dimensional subspace.

Now consider a diagonal three-by-three matrix with diagonal entries one, one, and four. It has two independent eigenvectors with eigenvalue one: the first and second coordinate directions. But those two directions are not individually special. Every direction in the plane they span is also an eigenvector with eigenvalue one.

For instance, we could replace the horizontal and vertical coordinate axes by two axes rotated forty degrees within that plane. They would still be perpendicular eigenvectors, and they would still describe the very same matrix. We could make that change of basis without perturbing the matrix at all.

If someone tells us that one of those eigenvectors has rotated, have we observed a physical change? Not necessarily. We may only have changed the way we describe an unchanged plane.

The plane itself is more meaningful. It is the collection of all vectors with third coordinate zero. It is also the full eigenspace associated with eigenvalue one. Its separation from the remaining eigenvalue, four, is three.

A perturbation that rearranges directions within the plane need not move the plane itself. A perturbation that mixes the plane with the third coordinate may move it, but then the separation between the cluster near one and the value near four becomes important. Under appropriate small-perturbation and spectral-selection assumptions, we can bound the movement of the plane even when its internal eigenvectors are poorly determined.

This suggests a general strategy. If individual directions are too sensitive, group together the directions that cannot reliably be distinguished. Then ask whether the whole group remains separated from the rest.

To do that carefully, we need a way to represent a subspace without choosing a particular basis. An orthogonal projection does exactly that. It keeps the component of a vector lying in the subspace and removes the perpendicular component. Two different orthonormal bases for the same plane produce the same orthogonal projection onto that plane.

So a projection lets us compare geometric objects rather than arbitrary labels on axes.

## Measuring the movement of a whole space

For two lines, the angle between them is a natural measure of how different they are. With two planes, the situation is richer. One direction in the first plane might line up closely with the second plane, while another might be farther away.

The mathematical answer is a collection of principal angles. They tell us, in a systematic way, how the directions in one subspace can be aligned with directions in another. In simple cases, the geometry decomposes into a collection of two-dimensional rotations. Each rotation has its own angle.

We can summarize these angles in several ways. We might ask for the largest one, because we care about the worst-aligned direction. We might combine them to measure a total squared error. Or we might use a different cost that assigns a different weight to how each direction moves.

These measurements are related, but they are not interchangeable. If one theorem controls the largest deviation and another controls an aggregate cost, we should not silently treat them as the same statement. Similarly, the best transformation under one cost need not be the best under another.

Another subtle point is that an eigenvector can be multiplied by negative one without changing its eigendirection. The vectors point in opposite orientations, but the line they span has not moved. Over complex numbers, multiplying by a complex number of magnitude one creates another version of the same ambiguity. Working with subspaces and projections keeps us focused on geometry rather than arbitrary choices of sign or phase.

This will eventually lead to a canonical way of rotating one subspace toward another, called the direct rotation. It will also lead to questions about what it means for such a rotation to be optimal. Those questions sound similar but require distinct mathematics.

## From approximate equations to an angle bound

There is another thread in the story: approximate eigenvectors.

In a real computation, we rarely obtain a perfect eigenvector. Instead, we obtain a candidate vector and a candidate eigenvalue. We can test how well they satisfy the eigenvector equation. Apply the matrix to the candidate vector, then subtract what the candidate eigenvalue says the output should have been. The result is called the residual.

A small residual means the proposed eigenvector equation is nearly satisfied. But what does that tell us about the direction of the candidate vector?

Return to a diagonal two-by-two matrix with diagonal entries zero and a positive number, g. The exact eigenvector for eigenvalue zero is the horizontal direction. Consider a candidate unit vector tilted by an angle theta away from that direction. Its horizontal coordinate is cosine theta, and its vertical coordinate is sine theta.

Apply the matrix. Its horizontal coordinate becomes zero; its vertical coordinate becomes g times sine theta. Because the proposed eigenvalue is zero, subtracting the proposed eigenvalue times the vector changes nothing. The residual therefore has length g times the absolute value of sine theta.

We have reached an exact equation in this simple setting: the sine of the angle, in magnitude, is the residual length divided by g.

This equation is worth lingering over. The residual tells us how badly the candidate satisfies the eigenvector equation. The gap converts that algebraic error into a geometric error. If g is large, the same residual forces the candidate to be close to the desired direction. If g is small, the same residual provides a much weaker guarantee.

This is not yet the general Davis–Kahan sine-theta theorem. We chose the correct target eigenvalue, used a diagonal two-dimensional matrix, and made the residual especially easy to compute. In a general problem we must say which part of the spectrum is wanted, which is unwanted, which approximate spectral values are being used, and how they are separated from one another. If we choose the wrong eigenvalue, even a zero residual could identify a perfectly valid eigenvector of the wrong eigenspace.

Nevertheless, this little calculation contains the central mechanism of a large family of results. A residual measures an error in an equation. Spectral separation lets us turn that error into control over an angle.

The rest is the hard, beautiful business of proving exactly how far that idea extends.

## What the course will build

The course begins by developing the geometry we have been borrowing in words. We will learn how projections encode subspaces, why a higher-dimensional comparison needs principal angles, and how matrix norms measure different kinds of errors.

We will then study the spectral theory that makes those comparisons quantitative. Rayleigh quotients and min-max principles explain why eigenvalues behave well. Rayleigh–Ritz approximation introduces computed trial subspaces. Residuals tell us what an approximation fails to satisfy. Sylvester equations reveal how separation between spectral values controls the solution of certain operator equations.

With these tools in place, we can understand the Davis–Kahan angle bounds. We will encounter the sine-theta and tangent-theta theorems, and two related families involving twice an angle: sine-two-theta and tangent-two-theta. They are not four names for an identical inequality. The different expressions encode different geometric information, and the theorems can require different spectral, structural, and norm assumptions. We will learn both what each theorem says and when it is legitimate to use it.

We will also ask a question that goes beyond bounding how far a subspace has moved. Suppose we want to construct an orthogonal or unitary transformation that carries one subspace to another. Which transformation should we prefer? Is there a canonical choice? Does that choice minimize how far points move, and under what measurement? The answers lead from direct rotation to optimization problems, counterexamples, and matching.

So far, our examples have used small real matrices. But the original perturbation theory reaches much further. Hilbert spaces can have infinitely many independent directions. Some operators are not defined on every vector. Spectra need not consist only of isolated eigenvalues. We will extend the picture carefully rather than pretending every matrix argument survives unchanged.

Finally, we will see why these questions matter outside the development of operator theory. Statistical estimators produce matrices from finite data. Their eigenspaces are used in principal component analysis, multidimensional scaling, spectral embeddings, and related methods. If we can control the error in an estimated matrix, spectral perturbation bounds can help us understand the error in a learned representation. That is often the bridge between an abstract theorem and a useful guarantee about a computational method.

There will be proofs along the way, because the hypotheses are part of the result. But the guiding order will be to understand the problem, discover why a construction helps, and only then derive the most general statement we are ready to justify.

## Where we begin

Let's return to the two diagonal matrices from the beginning. Their eigenvalue lists were identical. Their smallest-eigenvalue eigenvectors were perpendicular. The matrices themselves differed by only delta.

We now know why that example was possible. The distinguishing gap was also delta. There was no strong spectral separation protecting the selected direction. We also know two ways to improve the question. One is to demand enough separation to identify the desired direction reliably. The other is to ask whether a larger invariant subspace remains meaningful even when individual directions within it do not.

And we have seen the basic promise of the theory. In the right setting, the error in an approximate equation, divided by an appropriate separation, controls a geometric angle.

These are not merely technical details about matrices. They are answers to a recurring question in mathematical modeling: when our representation is imperfect, which conclusions are robust enough to trust?

That is the question we will carry into the first full lesson.
