# Before the series: a mathematics refresher

A short review for someone who has previously met elementary linear algebra,
trigonometry, and single-variable calculus. This is also a map of what to revisit
before studying the later lectures. Reading simple algebraic expressions is
assumed. Matrix exponentials, singular values, projections, and the optimization
argument are developed later, rather than assumed here.

Historical context: Arthur Cayley, [A Memoir on the Theory of Matrices (1858)](https://doi.org/10.1098/rstl.1858.0002).
The [Royal Society's contemporary referee report](https://makingscience.royalsociety.org/items/rr_3_55/referees-report-by-george-boole-on-three-papers-a-memoir-on-the-theory-of-matrices-a-memoir-on-the-automorphic-linar-transformation-of-a-bipartite-quadric-function-on-certain-formulae-for-differentiation-by-arthur-cayley)
provides a primary historical record. This is context for matrix algebra, not a
priority claim for the other concepts in this review.

## BaTitle: A mathematics refresher

Why: Refresh the language needed to understand the lectures that follow.
Recall: This is a review, not a first course.

A mathematics refresher.

## BaSetup: What to recognize before continuing

Why: Know what this review covers and how to use it.
Recall: School algebra is enough to read the examples; familiarity is the goal.

The later lectures connect linear algebra, geometry, and calculus. This review recalls the language those connections use. Matrix algebra has a long history: Cayley's 1858 memoir is one landmark. Today the same notation lets us describe motion, approximation, and optimization. We will review vectors and matrices, lengths and angles, eigenvectors, and elementary calculus. If these ideas are familiar, this should reactivate them. If they are new, treat the review as a map of topics to study first. Recognizing a formula here is different from being comfortable using it.

## BaNumbers: Real numbers, complex numbers, and vectors

Why: Distinguish a coordinate from the collection of coordinates it belongs to.
Recall: A scalar is one number; a vector can have several coordinates.

Real numbers lie on a number line. A complex number has the form a plus b times i, where i squared is minus one. We can draw it as the point with coordinates a and b. Its conjugate changes b to minus b; its squared magnitude is a squared plus b squared. A scalar means one number from the chosen number system. A vector is a collection of coordinates, often written as a column. The notation R to the n means n real coordinates; C to the n means n complex coordinates. A complex scalar and a vector of complex coordinates are different objects.

## BaMatrices: A matrix is a rule for transforming vectors

Why: Read matrix multiplication as an action, not just a table of entries.
Recall: A matrix with m rows and n columns takes n input coordinates to m outputs.

A matrix is a rectangular array of numbers. As a linear map, it turns an input column into an output column. Each output adds the row's entries times the matching input coordinates. Equivalently, combine the columns using the input coordinates as coefficients. In this example, the input is one, two. Multiply the first column by one and the second by two.

<!-- beat -->

Their sum is four, two: the blue output. Linearity means that scaling and adding inputs has the same effect as scaling and adding their outputs. Matrix products describe composition. A B x means apply B to x first, then apply A. Dimensions must fit, and reversing the order generally changes the result. The identity matrix leaves every input unchanged. When an inverse exists, it undoes the map.

## BaSpaces: Combinations, subspaces, bases, and dimension

Why: Describe a whole space without listing every point in it.
Recall: Coefficients multiply vectors; their sums are linear combinations.

The two columns from the previous example point in independent directions. Their span consists of every linear combination of those columns. Here their span is the entire plane. They form a basis: each vector in the plane has a unique pair of coefficients in that basis. The number of basis vectors is the dimension. A subspace contains zero and stays closed under addition and scalar multiplication. A line through the origin is an example. The kernel of a map consists of inputs sent to zero; its range consists of outputs it can produce. Neither depends on choosing a particular basis.

## BaInner: Inner products give alignment, length, and perpendicularity

Why: Turn the geometric idea of a right angle into a calculation.
Recall: Multiplying matching coordinates and adding gives the real dot product.

For real coordinate vectors, the usual inner product is the sum of the products of matching coordinates. For one, one and minus one, one, the sum is zero. These vectors are perpendicular, or orthogonal. Pairing a vector with itself gives its squared length, so taking the nonnegative square root gives its norm. Dividing a nonzero vector by its length makes a unit vector. An orthonormal collection has perpendicular members of length one. For complex coordinates we conjugate the first coordinate before multiplying. This makes the self-pairing a nonnegative real number. More general inner products obey the same geometric rules, although their coordinate formulas can differ.

## BaAdjoints: Transpose, adjoint, and length-preserving maps

Why: Distinguish properties that otherwise sound confusingly similar.
Recall: Transpose exchanges rows and columns; conjugation changes a plus bi to a minus bi.

The adjoint moves a map from one side of an inner product to the other. In standard real coordinates it is the transpose. In standard complex coordinates it is the conjugate transpose, written A star. A map equal to its adjoint is self-adjoint: symmetric over the reals, Hermitian over the complex numbers. A different condition says that Q star times Q is identity. For square matrices this means length and inner-product preservation. Such a matrix is called orthogonal over the reals and unitary over the complex numbers. A symmetric matrix need not preserve length. Orthogonal vectors and an orthogonal matrix also name different, related ideas.

## BaTrig: Read sine and cosine from a circle

Why: Connect the angle symbols used later to familiar geometry.
Recall: The radius is one; the coordinates are cosine theta and sine theta.

On a unit circle, cosine is the horizontal coordinate and sine is the vertical coordinate. Squaring and adding gives one by Pythagoras. Angles in formulas usually use radians: a half turn is pi radians, or one hundred eighty degrees. Tangent is sine divided by cosine wherever cosine is nonzero.

<!-- beat -->

As the radius turns, watch both coordinates change. The same trigonometry describes the angle between two nonzero real vectors: divide their inner product by the product of their lengths to obtain the cosine of that angle. Perpendicular vectors give cosine zero. This formula is stated for real vectors; we are not defining an angle by treating a complex-valued inner product as a real cosine.

## BaEigen: An eigenvector stays on its own line

Why: Recognize the equation behind the word spectrum.
Recall: The eigenvector must be nonzero.

An eigenvector v satisfies A v equals lambda times v. The matrix changes its size, and possibly its sign or complex phase, without leaving the one-dimensional space it spans. Lambda is the eigenvalue. In this real diagonal example, the horizontal direction is multiplied by two. The vertical direction is multiplied by one.

<!-- beat -->

Turn the input between those directions. In between, its image generally points along a different line. The coordinate directions are special. The spectrum of a finite square matrix is its set of eigenvalues. A real symmetric matrix has real eigenvalues and admits an orthonormal eigenbasis. We will use that theorem later. A general matrix need not have such a basis, and a real rotation can lack real eigenvectors altogether.

## BaMeasurements: Norms and trace measure different things

Why: Know whether a formula measures a vector, a map, or a diagonal sum.
Recall: The usual vector norm is geometric length.

The vector three, four has length five. For a matrix, the operator norm asks for the largest output length among unit inputs. The diagonal matrix with entries two and one has operator norm two. Trace is something else: add the diagonal entries, giving three in this example. Trace is not a norm; signed entries can cancel. Later we will meet the trace norm, which is different from ordinary trace. When reading an inequality, first identify the object and the measurement being used. Double bars around a vector and double bars around a linear map have related but different meanings.

## BaLimits: Limits and infinite sums

Why: Make sense of formulas that describe an infinite process.
Recall: The index n counts steps; an arrow indicates an approached value.

A limit describes what values approach as a parameter changes. The sequence one, one half, one quarter, and so on approaches zero, although no finite term is zero. An infinite sum is defined through its finite partial sums. Adding those same geometric terms gives partial sums approaching two. Not every sequence or series converges. These ideas recur when a derivative takes a limit of difference quotients, when a power series defines a function, and when an integral has an infinite endpoint. The matrix-exponential lecture develops its particular series; that construction is not assumed in this refresher.

## BaDerivative: A derivative measures local change

Why: Read both motion equations and necessary conditions for optimization.
Recall: A difference quotient is change in output divided by change in input.

The derivative takes the limit of that quotient as the input increment approaches zero. Geometrically it is tangent slope; for a trajectory it is instantaneous velocity. For t squared the derivative is two t. For differentiable functions, the chain rule differentiates a function of another function by multiplying the two appropriate derivatives.

<!-- beat -->

Watch the tangent change along the parabola. At its minimum the slope is zero. A differentiable real function has zero derivative at an interior local minimum. The converse fails: t cubed has derivative zero at zero without a local minimum there. Later we differentiate curves of matrices by a scalar parameter. This is used for matrix exponentials as well as for optimization. A constrained minimum needs a curve that stays within the constraints.

## BaIntegral: An integral accumulates contributions

Why: Understand how a derivative can recover a total change.
Recall: For a nonnegative scalar function, the integral measures area under its graph.

The area under t squared from zero to one is one third. More generally, integration accumulates contributions over an interval, allowing signed contributions too. If F has a continuous derivative, integrating that derivative from a to b gives F of b minus F of a. This is the fundamental theorem of calculus. An integral to infinity means a limit of integrals over finite intervals, and that limit must converge. Later, a Sylvester-equation argument integrates a derivative of an operator-valued function. This review recalls the scalar idea; the later lecture explains that particular use.

## BaRecap: What to revisit before moving on

Why: Decide whether the assumed background feels usable rather than merely recognizable.
Recall: This review supplies a map, not a replacement for learning the basics.

Can you multiply a small matrix by a vector and interpret its columns? Can you compute a dot product and decide whether two vectors are perpendicular? Can you explain the eigenvector equation and connect sine and cosine to a circle? Can you differentiate t squared and interpret a simple definite integral? If these are rusty, refresh them before relying on the later arguments. If they are unfamiliar, an introductory linear algebra or calculus course will give this review its meaning. The series itself develops projections, singular values, matrix exponentials, and feasible variations. Those are destinations, not extra entrance requirements.

## BaFacts: Two reusable facts to carry forward

Why: Connect the informal review to precise statements used in proofs.
Recall: The first fact uses a real inner product; the second concerns a real function.

Two simple facts illustrate how the reviewed ideas become proof steps. Pairing a vector with itself gives its squared norm. At an interior local minimum of a differentiable real function, the derivative is zero. Both statements include their setting and hypotheses. The next two cards express these exact facts in Lean, the language used to check proofs. They do not require learning Lean before watching the mathematical lectures.

## BaLean: Squared length in Lean

Why: Recognize the same mathematical fact in formal notation.
Recall: E is a real inner product space, and x is one of its vectors.

The symbolic formula on the left says that the self-pairing is squared length. The Lean statement on the right says the same thing. Its shared context specifies a real inner product space. The green line applies the existing Mathlib theorem. The code is included as a correspondence to recognize, not another topic to master before continuing.

## BaLeanMinimum: Zero slope at a minimum in Lean

Why: See which hypotheses justify the zero-derivative conclusion.
Recall: f is a real function; d is its derivative at zero.

IsLocalMin says that f has a local minimum at zero. HasDerivAt says that its derivative there is d. Together they imply d equals zero. The green line invokes Mathlib's existing theorem. Removing the minimum hypothesis would change the statement. Removing differentiability would allow a corner, where no derivative exists.

## BaComputation: Bonus: numerical zero is not an exact equation

Why: Keep approximate calculations distinct from the identities they illustrate.
Recall: Numerical software commonly uses finite-precision numbers.

As an optional numerical bonus, a computed dot product near zero is not automatically an exact orthogonality statement. Even familiar trigonometric inputs can introduce rounding error. A useful tolerance depends on scale and numerical error. Similarly, check the residual A v minus lambda v for a computed eigenpair. A small residual is evidence of an approximate equation, not a machine-checked proof of an exact one. The later lectures distinguish exact mathematical claims from the computations that illustrate them.
