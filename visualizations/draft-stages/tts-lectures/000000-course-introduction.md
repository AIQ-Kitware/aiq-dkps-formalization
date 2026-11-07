# Course introduction: The spaces, operators, and spectra we will study

## Before the big theorems

A matrix is a way to describe a linear transformation. If we know basic linear algebra, we can multiply a matrix by a vector, solve systems of equations, compute determinants, and sometimes find eigenvalues and eigenvectors. But there is a difference between knowing those operations and understanding why spectral theory is organized around them.

What information about a linear transformation belongs to the transformation itself, rather than to the coordinates in which we write its matrix? How can a small list of numbers tell us what a matrix does? Why do certain subspaces matter even when there is no preferred basis for them? And how can we take the square root, absolute value, or exponential of a matrix without simply applying the familiar scalar function to every entry?

These are the questions I want us to understand first.

This course will eventually develop the Davis–Kahan theory of spectral subspaces, including the mathematics behind a formalization described in our companion journal paper. But we are not going to start with a perturbation theorem. Before spectra, we will learn about the spaces that operators act on: normed spaces, Banach spaces, Hilbert spaces, and the geometry of inner products. Then we will build isometries, coordinate frames, Gram operators, eigenvalues, spectra, and operator constructions. Only after those objects make sense will we ask what happens when an operator changes.

We can start with a simple matrix and let it teach us why the subject exists.

## A matrix has an action, not just entries

Imagine a point in the plane, represented by two coordinates. A two-by-two matrix takes those coordinates and produces two new coordinates. We can think of this as moving every point in the plane by the same linear rule.

Consider a diagonal matrix whose first diagonal entry is two and whose second diagonal entry is three. Its off-diagonal entries are zero. Feed this matrix the vector pointing one unit to the right. The output points two units to the right. Feed it the vector pointing one unit upward. The output points three units upward.

So the matrix stretches the horizontal axis by a factor of two, and the vertical axis by a factor of three. Every other vector is a combination of those two directions, and linearity tells us what happens to it. A vector with horizontal component one and vertical component one becomes a vector with horizontal component two and vertical component three.

We can describe this matrix by listing its four entries. But the entries hide a more useful description. There are two special directions, and each of those directions is simply scaled. Once we know the scales and the directions, we know the whole transformation.

Those scales are the eigenvalues. Those directions are eigenvector directions. More precisely, an eigenvector is a nonzero vector that the transformation sends to a scalar multiple of itself. The scalar is its eigenvalue. Saying that the vector does not change direction is slightly informal, because multiplying by a negative scalar reverses its orientation. What matters is that the line through the vector is preserved.

This already explains why eigenvectors are interesting. They give us directions on which a possibly complicated transformation has a simple action: scalar multiplication.

But they raise another question. What if we use different coordinates? The same transformation might no longer have a diagonal matrix. It might have several nonzero off-diagonal entries. Yet the transformation, as a geometric action, has not changed. So we would like our most important descriptions to survive a change of coordinates.

Under a change of basis, the matrix changes by a similarity transformation, but the eigenvalues remain the same. The individual coordinate columns used to represent an eigenvector change, yet the invariant direction in the underlying space is the same geometric object. That separation between a mathematical object and a chosen description will run throughout this course.

## What kind of space can an operator act on?

The plane from our example is a convenient place to begin, but an operator is not required to act on two-dimensional coordinate vectors. It can act on a space of functions, a space of sequences, or another mathematical collection on which addition and scalar multiplication make sense.

To study such maps, we need ways to measure vectors and talk about limits. A norm assigns a nonnegative size to a vector. From it we get a distance: the distance between two vectors is the norm of their difference. Once there is a distance, we can talk about a sequence of vectors getting closer and closer to one another.

Here a question appears that finite-dimensional linear algebra tends to conceal. Suppose the terms of a sequence become arbitrarily close to each other. Must they approach a vector that belongs to the space we started with? Not necessarily. A normed space is called complete when every Cauchy sequence, meaning a sequence whose sufficiently late terms are arbitrarily close together, actually converges to an element of that space. A complete normed vector space is called a Banach space.

Why does completeness matter? Because many mathematical constructions are defined by limits. We will define operator inverses, infinite series, and continuous transformations. It matters whether the limit remains inside the space on which the operator is supposed to act. Every finite-dimensional real or complex normed space is complete, which is one reason many of these issues were invisible in our earlier linear algebra courses.

Now imagine that the space also has an inner product. An inner product gives us not just lengths but angles and orthogonality. A complete inner-product space is called a Hilbert space. Euclidean space is a Hilbert space. So is the space of square-summable sequences, where vectors can have infinitely many coordinates while retaining finite squared length.

Every Hilbert space is a Banach space, but a Banach space need not have an inner product whose norm is its given norm. This distinction matters: orthogonal projections, self-adjoint operators, and the adjoints we use in spectral geometry rely on inner-product structure. We will build them rather than assume they work in every normed space.

A linear operator between normed spaces is bounded if some fixed multiple of the input norm bounds the output norm. For linear operators, this is equivalent to continuity. Every matrix between finite-dimensional normed spaces is bounded. In infinite dimensions, continuity becomes a real restriction, and later we will also encounter important operators that are unbounded and therefore require careful domain conditions.

## Isometries, coordinate frames, and Gram operators

An isometry preserves distances. For a linear map between inner-product spaces, preserving norms also means preserving the inner product. An orthogonal matrix or a unitary matrix is a familiar example: it preserves lengths and angles, and it maps the entire space onto itself. But an isometry does not have to be onto. It can place a small coordinate space inside a larger ambient space without changing any geometry.

Imagine choosing two orthonormal vectors in three-dimensional space. Using them as columns of a matrix gives an isometric map from a two-dimensional coordinate plane into three-dimensional space. If we call the map V, multiplying its adjoint by V gives the two-dimensional identity: V star V equals I. But multiplying V by its adjoint in the opposite order gives the projection onto the selected two-dimensional plane. V V star is not the identity on the entire three-dimensional space. That distinction will matter throughout this course.

What if the chosen vectors are not perpendicular? We can still use them to construct a linear map from coefficient vectors to their linear combinations. This is called a synthesis map. Its adjoint is the analysis map: it records inner products with the chosen vectors.

The Gram matrix collects all the pairwise inner products of the selected vectors. If the synthesis map is S, the Gram operator on coefficient space is S star S. For a concrete example, choose the plane vectors one comma zero and one comma one. Their Gram matrix has entries one and one in the first row, and one and two in the second. Its diagonal entries tell us the squared lengths of the vectors; its off-diagonal entries tell us their overlap. More generally, if c is a vector of coefficients, the squared length of the linear combination S c is exactly the inner product of c with G c.

That immediately shows the Gram matrix is positive semidefinite: squared length cannot be negative. It also explains why a Gram matrix is meaningful even if our chosen vectors are not an orthonormal basis.

The reverse product, S S star, acts on the ambient space rather than on coefficient space. It is called a frame operator. Both are built from the same map, but they answer different questions. Keeping track of the spaces on which they act will prevent many later confusions.

A particularly useful generalization is A star A for an arbitrary operator A. It is positive, it records squared output lengths, and its positive square root will become the operator modulus. So the Gram construction is not a detour. It is one of the main routes from familiar vector geometry into the algebra of operators.

## From eigenvalues to the spectrum

The word 'spectrum' might sound like it must refer to something visible, like the colors of light. In spectral theory, we use it for the set of scalar values associated with an operator in a particular way.

In finite-dimensional linear algebra, the spectrum of a square matrix is exactly the set of its eigenvalues. So for our diagonal matrix, its spectrum consists of two numbers: two and three.

There is a definition of spectrum, however, that works more generally, and understanding that definition is worth the effort. Pick a number, which mathematicians often call lambda. Subtract lambda times the identity matrix from our operator. Ask whether the resulting matrix has an inverse.

If it does, lambda is outside the spectrum. If it does not, lambda is in the spectrum.

Let's see why this agrees with the eigenvector definition for matrices. If lambda is an eigenvalue, there is a nonzero vector that the original matrix sends to lambda times that vector. Subtract lambda times the identity, and that vector gets sent to zero. A matrix that sends a nonzero vector to zero cannot be invertible. So every eigenvalue belongs to the spectrum.

Conversely, for a square matrix, failure to be invertible means there is some nonzero vector in its kernel. If the matrix we are examining is the original matrix minus lambda times the identity, that kernel equation says exactly that the original matrix sends our vector to lambda times itself. So every spectral value is an eigenvalue. In finite dimensions, the two descriptions agree.

Why use the definition involving invertibility, then? Because the definition continues to make sense when we leave finite matrices behind. Some operators act on spaces of functions, where the notion of a vector is broader than a short coordinate list. In those settings, an operator can have spectral values even when no nonzero vector is an eigenvector for that value.

We are not going to prove the infinite-dimensional theory on day one. We will revisit it carefully later. For now, the important point is that 'spectrum' is a precise mathematical term, not merely a synonym for a list returned by an eigenvalue routine. In matrices the two agree; in general operators there is more to understand.

## Why we care about self-adjoint operators

Not every matrix has a complete set of eigenvectors that form a basis. Some have complex eigenvalues. Others cannot be diagonalized at all. So the two-axis description we used is not a universal privilege of arbitrary matrices.

There is, however, a very important class for which a remarkably clean description is available. Over the real numbers these matrices are called symmetric. Over the complex numbers they are called Hermitian, or self-adjoint. If we think of matrices as operators on an inner-product space, being self-adjoint means the operator equals its adjoint.

An adjoint is defined by how an operator interacts with the inner product. The inner product measures lengths and angles. Taking the adjoint is the operation that moves a linear transformation from one side of that pairing to the other, in a way that leaves the resulting scalar unchanged. We will derive that more carefully in the first unit, rather than rely on a slogan.

For a real symmetric matrix, the spectral theorem says we can find an orthonormal basis consisting entirely of eigenvectors. Orthonormal means the basis vectors all have length one and meet at right angles. For complex self-adjoint matrices the analogous statement holds with a unitary change of basis.

This is an extraordinary amount of structure. It says that a self-adjoint matrix, however complicated its entries look, can be understood as a collection of perpendicular directions, each with a real scale factor. We can change coordinates so that the matrix becomes diagonal, without distorting lengths or angles.

Think of a mechanical system with several vibration modes, or of a quadratic form measuring energy in different directions. Orthogonal spectral directions provide a way to discuss distinct modes of behavior without having to treat every coordinate interaction separately.

But there is a complication that will turn out to be equally instructive. Sometimes several eigenvectors share the same eigenvalue.

## Why a subspace is not the same thing as a chosen basis

Consider a three-by-three diagonal matrix with diagonal entries one, one, and four. The first two coordinate axes are eigenvector directions with eigenvalue one, while the third coordinate axis has eigenvalue four.

Are the first two coordinate axes the only eigenvector directions with eigenvalue one? No. Any nonzero vector in the plane spanned by those axes is also an eigenvector with eigenvalue one. The matrix acts on that entire plane by simply multiplying every vector by one.

We might choose one pair of perpendicular axes within the plane. Or we might rotate that pair by thirty degrees and choose another. Both pairs are equally valid eigenvector bases for the same plane. The operator has not changed; only our description has.

This is why an eigenspace is often more fundamental than an individual eigenvector. The eigenspace is the collection of all vectors belonging to a particular eigenvalue, together with zero. More broadly, we may care about the sum of the eigenspaces whose eigenvalues belong to some chosen part of the spectrum. We call that a spectral subspace.

How can we describe a subspace without committing ourselves to one convenient basis? One answer is with an orthogonal projection. A projection onto a plane keeps the part of a vector that lies in the plane and discards the perpendicular part. The result depends on the plane, not on which pair of axes we happen to draw inside it.

For our three-by-three example, the projection onto the first two coordinates is a matrix whose first two diagonal entries are one and whose third is zero. Apply it to any vector, and it removes the third coordinate. We get a canonical algebraic representation of the plane.

If the eigenvalues of a self-adjoint matrix are known, and we have the projections onto each of its eigenspaces, then we can reconstruct the operator. Multiply each spectral projection by its eigenvalue, and add them. This is the finite-dimensional spectral decomposition. Later we will use this idea to define functions of operators and to select a group of spectral values without referring to an arbitrary eigenbasis.

Notice what we have accomplished before asking any question about approximation. We now have several distinct objects: an operator, its spectrum, an eigenspace, a spectral subspace, and an orthogonal projection onto that subspace. Each has a mathematical role. They are not interchangeable.

## Taking functions of matrices

Let's return to our first two-by-two diagonal matrix, with diagonal entries two and three. Squaring this matrix gives a diagonal matrix with entries four and nine. Applying the square twice gives a fourth power with entries sixteen and eighty-one. Because multiplication acts independently on the two eigenvector directions, these calculations are simple when expressed in the eigenbasis.

What if we want to apply a different function, such as a square root or an exponential? For a diagonalizable self-adjoint matrix, the spectral theorem suggests a direct method: apply the scalar function to each eigenvalue, and keep the corresponding spectral directions. A function of the operator is built from the same spectral projections, but with the original eigenvalue replaced by the value of the chosen function at that eigenvalue.

For instance, the positive square root of the diagonal matrix with entries four and nine has diagonal entries two and three. The square of that new matrix is the original one. The word 'positive' matters: a square root is not necessarily unique without specifying which one we mean. We will investigate positive operators and positive square roots before relying on this construction.

This leads to an operator that the journal manuscript uses repeatedly: the modulus of an operator. For an ordinary real number, absolute value measures its magnitude without keeping its sign. For a matrix, the analogous object is not obtained by taking the absolute value of every entry.

Instead, one first multiplies the adjoint of the operator by the operator itself. That product is positive semidefinite. Then one takes its unique positive square root. The result is called the operator modulus, and it is written as the absolute value of the operator.

Why would we do that? Because the operator modulus captures how much the transformation stretches different directions. Its eigenvalues are the singular values of the original matrix. Singular values lead to the operator norm, the Frobenius norm, and many other ways to measure the size or displacement of a transformation. From the modulus we can also build a polar decomposition, which separates the magnitude of a map from an appropriate orientation factor.

We will not treat these as disconnected vocabulary words. We will work through examples until the sequence makes sense: adjoint, positive product, positive square root, modulus, singular values, and polar decomposition.

There is another function of a matrix that deserves its own careful development: the exponential.

## Why a matrix exponential describes motion

You already know the scalar exponential function. Its derivative equals itself, and it turns addition in the exponent into multiplication of values. We can define a matrix exponential by a similar infinite series: the identity, plus the matrix, plus half its square, plus one sixth of its cube, and so on.

This is not the same as exponentiating the entries one by one. Matrix multiplication couples those terms, and the exponential describes a new linear transformation.

In a simple planar example, take a matrix that sends a rightward-pointing vector upward and sends an upward-pointing vector leftward. The matrix is skew-symmetric: its transpose equals its negative. The exponential of time times this matrix rotates every vector counterclockwise by that time, measured in radians.

You can understand the connection even before carrying out the full power-series calculation. At any instant, a vector's velocity points perpendicular to the vector, with the orientation specified by the generator. Perpendicular motion changes direction while preserving length. The exponential packages that continuous motion into a transformation at a chosen time.

When we derive this properly, we will show that exponentiating a skew-adjoint operator produces an orthogonal or unitary transformation. Those transformations preserve inner products. And that gives us a rigorous language for rotating an entire space, not just drawing an arrow that turns in a plane.

There will be a reason to care about this later. Once we know how to describe two subspaces and measure the angles between them, we can ask for a canonical rotation carrying one to the other. The matrix exponential provides one way to understand continuous rotations, while polar decomposition provides another way to construct the appropriate transformation. Both will have been built before we need them.

## The course ahead

Our route begins with Banach and Hilbert spaces, then linear operators, adjoints, isometries, Gram operators, and orthogonal projections. That groundwork will lead us to eigenvalues, spectra, the spectral theorem, and its geometric consequences. We will spend time understanding functions of operators and the constructions behind matrix absolute value and matrix exponential. We will then learn how to compare subspaces using principal angles and direct rotations.

At that point we can ask the question that motivated Davis and Kahan: if an operator, trial space, or numerical representation changes, how much of its spectral structure follows that change? We will no longer be forced to begin by asking, 'Stability of what?' We will have objects whose meaning is already clear.

The mathematical answer is not one theorem. It is a family of sine, tangent, sine-of-double-angle, and tangent-of-double-angle bounds, with distinct assumptions. There is also a geometry of direct rotations and the question of what they optimize. The original nineteen-seventy paper develops more than the four famous estimates; it includes generalizations, subtle issues of spectral selection, a numerical example, and research questions. This course is intended to explain all of that material, and then the related real trace-norm matching theorem described in the companion journal paper.

We will start with matrices, but the story eventually reaches operators on infinite-dimensional Hilbert spaces. There the spectrum need not be a list of eigenvalues, and some operators are not defined on every vector in the space. We will take those issues seriously when the foundations have prepared us for them.

The companion journal paper records formal proofs and also a correction to one printed optimality claim in the original source. It gives us a precise mathematical reference, but it does not dictate how a listener should learn. Our spoken course will begin with intuition, derive the needed language, and then build the proofs at the right level of abstraction. At the end of each mathematical lecture, we will also connect the symbols to their actual Lean representations. That is part of understanding the mathematics, not a separate programming afterthought. Diagrams and animations will come later, in service of explanations that already work when heard aloud.

## Where we begin

In the first full lesson, we will look at linear maps as geometric actions. We will then build norms, convergence, completeness, inner products, and the structure of Hilbert spaces. Along the way we will see how maps become matrices after we choose coordinates, and which properties belong to the map rather than its matrix representation.

Once we understand what an operator acts on, how it preserves geometry, and how a family of vectors gives a Gram operator, we will be ready for the spectrum. Only after we know what a spectrum is and how it determines spectral subspaces will we ask how those subspaces behave under a change.

## Connecting the mathematical symbols to Lean

There is one last piece of the learning process I want to establish at the outset. As we study each construction, we will end the lesson by looking at how the same mathematical objects appear in the Lean formalization. We will not ask you to learn a proof assistant before you can understand an inner product or a spectral theorem. Instead, we will use the code to make the assumptions and the shapes of the objects precise.

In mathematical speech, I might say that E is a Hilbert space and A is a bounded linear operator on E. Lean expresses the normed additive structure, inner product, and completeness as separate assumptions. This makes it harder to silently use a Hilbert-space property in a theorem that only assumes a normed space. A mathematical map from E to F can be written as a linear map in one setting, and as a continuous linear map in another. The distinction reflects an actual mathematical hypothesis.

When we introduce a coordinate frame, Lean can make the direction of the map explicit: are we sending coefficients into the ambient space, or extracting coefficients from a vector? In the repo's finite-frame development, the synthesis and analysis maps are separate definitions. Their composition on coefficient space is called the finite Gram operator, and the same file proves that it is positive. This is exactly the relationship we just saw: an inner-product matrix built from a family of vectors must yield a nonnegative quadratic form.

The source excerpt displayed below is from the existing project, not new Lean code written for this introduction. The first definition says that the Gram operator goes from Euclidean coefficient space back to that same coefficient space. The equation composes analysis after synthesis. The positivity theorem records the algebraic consequence. It sits under assumptions that the coefficient indices are finite and that the ambient vector space is finite-dimensional with an inner product.

```lean
-- Source: ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean
-- Namespace: TauCeti; excerpt, requires the source file's context.
noncomputable def finiteGramOperator (v : ι → E) :
    EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (finiteAnalysis 𝕜 v).comp (finiteSynthesis 𝕜 v)

theorem finiteGramOperator_isPositive (v : ι → E) :
    (finiteGramOperator 𝕜 v).IsPositive := by
  rw [finiteGramOperator_eq_selfCompAdjoint]
  exact (finiteAnalysis 𝕜 v).isPositive_self_comp_adjoint
```

Notice three connections. The arrow marked with the subscript ell describes a linear map. The notation EuclideanSpace specifies where the coefficients live. And IsPositive is a proposition about the resulting operator, not a numerical approximation to it. Later, when we reach projections, we will see the orthogonal decomposition directly in Lean; when we reach polar decomposition, we will see a theorem reconstructing the operator from its polar factor and modulus; and when we reach Davis–Kahan, we will see the full residual and spectral-gap hypotheses.

The code will be displayed rather than read symbol by symbol by the speech synthesizer. The spoken explanation is part of the lecture, and the exact snippet is available for learners who want to connect the mathematics to a checked formulation. This course should develop mathematical intuition and formal precision together.
