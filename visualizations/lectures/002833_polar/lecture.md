# Operator absolute value and polar decomposition

Scope and formal companion sources: [operator lecture notes](../../dkvis/learning/operators/README.md).
Numerical reference: https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.polar.html

## PoTitle: Operator absolute value and polar decomposition

Why: Separate length change from the remaining motion.
Recall: Inner products, adjoints, and perpendicular subspaces.

Operator absolute value and polar decomposition.

## PoOutcomes: The three facts we will explain

Why: See the destination before constructing the factors.
Recall: Work in finite real or complex inner product spaces.

A linear map can stretch different directions by different amounts, and also turn them. Three facts organize this lecture. The modulus gives every input the same output length as A. A factors into a positive stretch followed by length-preserving motion on the part that survives. Collapsed inputs require a partial isometry: the remaining factor need not preserve lengths everywhere. We will see these facts geometrically first, then explain why the formula and the remaining motion actually exist. No invertibility assumption is needed.

## PoQuestion: Same lengths, different final directions

Why: Give operator absolute value a geometric meaning before its formula.
Recall: This is a planar example; the general claim concerns every input vector.

What should the magnitude of a linear map remember? A single number cannot describe its directional stretching. In this example, the input circle becomes an amber ellipse: the horizontal direction stretches by two and the vertical direction by zero point eight. That positive stretch is the modulus. Positive means that in perpendicular eigenvector directions it scales by non-negative amounts. It can still change the direction of a general vector. It is not a uniform enlargement, and not a smoothing of the matrix entries.
<!-- beat -->
The blue ellipse is the actual output of A. Here A performs the positive stretch and then rotates through zero point six radians. The amber horizontal output arrow and its blue rotated counterpart have the same length. That agreement holds for every corresponding input, not merely for these arrows or for the outline of the ellipse. The modulus remembers how long every output is; the remaining factor supplies its final direction. The next question is how to extract this positive length effect from A itself.

## PoSetup: The objects in the construction

Why: Name the pieces after seeing what they must accomplish.
Recall: A star denotes the adjoint; the Foundations lecture fixes this convention.

A is our linear map, and A star is its adjoint. We write vertical bars around A for its modulus, an operator rather than an entrywise absolute value. Its formula is the positive square root of A star A; we will justify that choice next. The kernel means all inputs that A sends to zero. Its perpendicular complement contains the surviving input directions. We will construct U to preserve lengths there and to be zero on the kernel. A map with this behavior is called a partial isometry. The desired factorization applies the modulus first and U second.

## PoModulus: Squared lengths explain the square root

Why: Derive the formula from the geometric requirement.
Recall: The adjoint transfers A across the inner product.

The modulus must reproduce the length of A x for every input x. Squaring that length gives the inner product of A star A x with x. Thus A star A encodes squared output lengths. Its quadratic form is non-negative, so it has a unique positive square root in our finite-dimensional setting. Define that root to be the modulus. Because the root is self-adjoint, the squared output norm of the modulus is the same quadratic form. Both output norms are non-negative, so their squares being equal proves the desired equality of lengths.
<!-- beat -->
The square root recovers the length scale from the squared length scale. For a stretch by two, A star A has scale four, and the modulus restores two. In general we diagonalize the positive operator A star A and take the non-negative square root of each eigenvalue. This is an operator construction, not a square root of each matrix entry. Positivity chooses a particular length-reproducing map: it removes sign reversals and phase rotations in its eigen-directions. The modulus need not send a general input to its final output direction. That is the job of U.

## PoKernel: Construct the remaining motion

Why: Show that the proposed factor exists, rather than assuming it.
Recall: The modulus and A have equal output norms for every input.

After the modulus sends x to its intermediate output, U must send that intermediate output to A x. This specifies a rule, but we must check that it is consistent. Two different inputs might give the same intermediate output. Their difference then has modulus output zero. The equal-length identity makes its A output zero too. So both inputs demand the same final output, and our rule is well-defined. It is linear, since both original maps are linear. The equal-length identity also proves that this rule preserves lengths on the image of the modulus.
<!-- beat -->
Where else do we need to define U? In finite dimensions, the image of the positive modulus is the perpendicular complement of its kernel. The equal-length identity says its kernel equals the kernel of A. Every input therefore splits into a surviving component and a collapsed component. Our rule already defines U on the surviving component; define it to be zero on the collapsed component. This constructs U on the whole space and proves A equals U times the modulus. The zero choice makes this the canonical partial factor. It need not be a unitary map.

## PoExample: A collapsed direction

Why: See exactly why the remaining factor can fail to be unitary.
Recall: The displayed R is a planar rotation.

The first example stretched both coordinate directions. Now the second direction is collapsed instead. A stretches the first direction by two, sends the second to zero, and then rotates. The modulus gives the amber horizontal arrow. Applying U gives the blue arrow of the same length. On that surviving line U acts as a length-preserving rotation. No direction for a vanished output needs to be recovered.
<!-- beat -->
The canonical convention sets U to zero on the collapsed input line. That is why U is a partial isometry rather than an orthogonal matrix on the whole plane. An orthogonal matrix would have to preserve the length of the second basis vector too. We can extend the rotation to do that in this square example, but this changes U on the kernel. Both choices give the same product with the modulus because the modulus already annihilates that line. Factorization alone does not determine the kernel action; the canonical convention does.

## PoSummary: The same three facts, now justified

Why: Reinforce the geometric meaning and the construction that makes it valid.
Recall: The canonical factor is zero on the kernel.

The modulus gives every input the same output length as A. We obtained it by recovering length scales from the squared-length operator A star A. The remaining motion exists because identical intermediate outputs demand identical final outputs; this gave a consistent length-preserving map on the surviving inputs. Finally, collapsed inputs explain why the canonical factor is only a partial isometry. It sends them to zero. These are the same three claims from the opening, now connected by the equal-length identity rather than just a factorization formula.
<!-- beat -->
For bounded operators between Hilbert spaces, the same idea needs one extra step: the image of the modulus may not be closed. The length-preserving map extends continuously to its closure, and is zero on the perpendicular complement. The finite picture captures the construction; the closure handles limits of surviving outputs. Next we record the reusable finite-dimensional statements and their Lean versions. The computational bonus then explains how singular values recover these factors and why numerical routines may choose a different action on collapsed inputs.

## PoFacts: Two reusable polar facts

Why: Record what holds even when the map is singular.
Recall: Finite real inner product spaces; A is any linear map.

The first fact is factorization: canonical polar factor composed with operator absolute value equals A. The second says the factor preserves norms on the orthogonal complement of A's kernel. Neither fact requires A to be invertible. The zero-on-kernel convention is part of which factor we are naming. These facts explain why the singular example was a legitimate polar decomposition rather than an exception.

## PoLean: Polar factorization in Lean

Why: Read the canonical factorization without an invertibility assumption.
Recall: $U|A|=A$.

A is an arbitrary linear map between finite real inner product spaces. OperatorAbs names its positive modulus and polarFactor its canonical partial isometry. The composition applies the modulus first and then the factor. The blue proof invokes the accepted factorization theorem. Invertibility is not assumed. The canonical factor is already defined with its zero-on-kernel convention, so the factorization statement includes singular maps.

## PoLeanSupport: Support isometry in Lean

Why: Identify where the canonical factor preserves norms.
Recall: $x\in(\ker A)^\perp\Longrightarrow\|Ux\|=\|x\|$.

The hypothesis h x places the input in the orthogonal complement of the kernel of A. On this surviving input space, the canonical polar factor preserves its length. The blue proof applies the accepted norm theorem. Without the support hypothesis the statement would fail for a nonzero kernel vector, because the canonical factor sends that vector to zero. This is why a canonical partial isometry must be distinguished from a chosen unitary extension.

## PoComputation: Bonus: Compute the factors with an SVD

Why: Connect singular-value algorithms to the exact kernel convention.
Recall: A equals L times Sigma times V adjoint.

As an optional numerical bonus, here is how this mathematical tool is used in computation. An SVD computes the modulus as V Sigma V adjoint. To get the canonical partial factor, put one on every strictly positive singular direction and zero on every zero singular direction, then multiply by L and V adjoint. Numerical software needs a tolerance to decide effective rank; the exact formula uses strict positivity. Be careful with the name polar decomposition in numerical libraries. For square matrices, SciPy's polar routine returns a unitary factor even at singular inputs. That is a unitary extension, and may differ on the kernel from the canonical factor shown here. Check the convention before comparing numerical output with a formal theorem.
