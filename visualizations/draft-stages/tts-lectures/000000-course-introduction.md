# Course introduction: Learning the mathematics behind Davis–Kahan theory

Suppose you have taken a linear algebra course. You can multiply matrices, compute eigenvalues in simple examples, take derivatives, and evaluate integrals. You know that matrices represent linear transformations, and you have seen at least a few ways to factor them.

That is enough background to begin this course. But it is not the same as knowing spectral theory.

For example, what is a spectrum? You may remember that the eigenvalues of a square matrix form a collection of special numbers. Why those numbers? What do they tell us about how the transformation acts? And what happens when we replace an ordinary matrix with an operator acting on an entire space of functions?

Or consider a subspace. We know how to describe a plane by giving two spanning vectors. But the plane itself does not depend on which pair of vectors we chose. If we rotate those two vectors within the same plane, we have changed the coordinates, not the object. How can we express the geometry of the plane without depending on the particular basis?

These sound like questions from different chapters. In the mathematics we will study, they become connected. The spectrum lets us distinguish parts of the action of an operator. Spectral subspaces describe where those parts live. Orthogonal projections describe subspaces without needing arbitrary coordinates. And operators built from those projections let us compare different subspaces and construct precise rotations between them.

There is a great deal of interesting mathematics to learn before we ask whether any of those objects are stable.

## A course built around understanding and proof

This course accompanies our journal manuscript on the formalization of Davis and Kahan's theory. The familiar summary is that Davis–Kahan gives bounds on how eigenspaces change. That summary is important, but it leaves out most of the mathematical story.

The complete story involves geometry, spectral theory, operator equations, variational principles, and functional analysis. The original work studies several different ways to measure angles, different assumptions about spectral gaps, canonical rotations of Hilbert spaces, and the behavior of operators that need not be finite matrices. There is also a subtle distinction between a rotation that is naturally defined and a rotation that minimizes a particular notion of displacement. One printed claim about that distinction turns out to be false.

Our goal is not merely to memorize the four famous angle estimates. By the end of this course, you should be able to reconstruct the arguments that establish them, identify their precise hypotheses, and understand the analytical tools that make those proofs possible.

That is why we will take the foundations seriously. We will learn the mathematics required by the proofs, including results that may not have the Davis–Kahan name attached to them. Some of those results were developed as part of this formalization and later became part of broader operator-theory libraries. Their mathematical role remains essential even when their code has moved.

We assume basic linear algebra and calculus, but we will not assume prior familiarity with Banach spaces, Hilbert spaces, measure theory, or functional calculus. We will construct that understanding as we go, using small examples before moving to general theorems.

## The spaces and maps

We will begin by distinguishing a linear transformation from the matrix used to represent it. A change of basis can change every entry of a matrix without changing the underlying transformation. Keeping this distinction clear will make the later theory less mysterious.

Next we will ask what it means to measure the size of a vector, or the size of a linear operator. A norm gives us a notion of length and therefore of distance. That makes limits possible, and limits introduce the question of completeness. A Banach space is a normed vector space complete under its norm. A Hilbert space adds the familiar geometry of inner products and perpendicularity, together with completeness.

Why introduce infinite-dimensional spaces when matrices are easier to calculate? Because the original theory is not confined to finite-dimensional matrices. Operators on function spaces appear in differential equations, numerical approximations and spectral problems. A proof that works only for diagonal matrices is an excellent place to start, but it is not yet the full theorem.

Hilbert spaces also give us projections and adjoints. We will see why a linear isometry preserves lengths, why its adjoint need not be its inverse on the entire ambient space, and how a collection of vectors defines a Gram matrix. We will carefully distinguish a Gram operator on coefficient space from a frame operator on the larger space. These are not vocabulary exercises. We will prove identities with them that recur throughout the course.

## The spectrum and the functions we apply to operators

After those preparations, we will learn spectral theory itself. We will begin with eigenvalues and eigenvectors, then explain why eigenspaces and spectral projections often matter more than an individually chosen eigenvector.

In an infinite-dimensional space, the spectrum is not always a list of eigenvalues. We will see examples where that familiar picture fails, and we will learn how the definition in terms of invertibility takes its place. For self-adjoint operators, the spectral theorem provides a remarkably powerful description of the operator's action. Instead of thinking only about a collection of eigenvectors, we will learn to think in terms of spectral projections and, eventually, spectral measures.

One benefit of the spectral theorem is that it tells us how to apply functions to operators. A square root, an absolute value, or an exponential of a matrix is not generally obtained by applying the scalar function separately to its entries.

Take the operator modulus, written as the absolute value of an operator. We will derive it by forming the operator's adjoint times the operator, and then taking the positive square root. We will see why this construction describes stretching and why it leads to singular values and polar decomposition.

Or take the matrix exponential. We will derive the exponential from its power series, understand how it solves differential equations, and see why exponentials of skew-adjoint operators describe continuous length-preserving motions. This will prepare us to understand canonical rotations of subspaces rather than merely drawing rotations in a diagram.

## Beyond the finite-dimensional picture

A second layer of foundations will take us from matrices into serious operator analysis. We will study the min–max principle, singular-value inequalities, and ways of comparing entire lists of singular values. The operator norm is only one measure of size. Davis and Kahan worked with more general unitarily invariant norms, so we need to understand where those norms come from and when an operator actually belongs to the class on which such a norm is finite.

We will also study an equation called the Sylvester equation. Its basic form is this: multiply an unknown operator by one known operator on the left, subtract its product with another operator on the right, and obtain a known residual. Even the scalar version involves division by a difference of numbers. The operator version explains why separating pieces of a spectrum is so important. We will solve finite examples, then learn the analytic estimates needed for the general case.

In infinite dimensions, the analysis becomes more delicate. Some operators are not defined on every vector in their Hilbert space. We must understand their domains, what it means for them to be closed and self-adjoint, and what we are actually allowed to write when manipulating their products. We will build spectral measures, functional calculus, resolvents, spectral cutoffs and the relevant operator ideals with enough care to support the final theorems.

This is the part of the course that is easy to omit when the goal is merely an appealing presentation of a result. We will not omit it. A full proof is only as sound as its foundations.

## Finally, the Davis–Kahan questions

Only after we understand the objects and the tools will we ask how they behave when an operator or a trial subspace changes.

The central estimates then become natural questions rather than formulas arriving without preparation. What does the residual of an approximate invariant subspace tell us? How does it connect to the part of that subspace that lies outside an exact spectral subspace? Why do certain spectral gaps allow us to convert a residual bound into an angle bound? Under which assumptions can we control the sine of an angle, its tangent, or the sine or tangent of twice that angle?

We will examine the four principal angle-theorem families, their generalizations, the problem of selecting the correct spectral branch, and the direct-rotation theorems. We will work through the source paper's numerical example and take its open questions seriously. We will also study the corrected rotation-optimality picture and related results from our companion formalizations.

Most of all, the course will demand more than recognizing the final inequality. You should understand why each step is legal, what fails when an assumption is removed, and how to build the proof again without having the finished result in front of you.

## How we will learn

The spoken explanation is the primary material. Every lesson will be written to make sense when listened to on its own. When a picture or animation helps, it will be built to clarify an explanation that already works, not to dictate the order of the lesson.

In most mathematical lessons, we will also end by connecting the notation to the corresponding Lean formalization. These connections matter because they make implicit assumptions visible and show how the mathematical structures and arguments can be made precise. We will not use the proof assistant as a substitute for learning the proof, and we do not need a code demonstration in this introductory conversation about what the course is for. When we reach the actual mathematical constructions, those links will become concrete, with code that can be checked against the maintained sources.

We begin next with linear maps. You already know how to multiply matrices. We will use that familiarity to understand what a linear map really is, how coordinates describe it, and which properties survive when our description changes.
