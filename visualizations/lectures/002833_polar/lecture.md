# Operator absolute value and polar decomposition

See [operator lecture provenance](../../dkvis/learning/operators/README.md) for accepted source modules and scope.
Numerical reference: https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.polar.html

## PoTitle: Operator absolute value and polar decomposition

Why: Separate length change from the remaining motion.
Recall: Know adjoints and orthogonal complements.

Operator absolute value and polar decomposition.

## PoSetup: Modulus, support, and the canonical factor

Why: Fix the kernel convention before stating polar decomposition.
Recall: $A^*$: adjoint; $|A|$: modulus; $U$: canonical partial isometry.

A is a linear map between finite-dimensional inner product spaces. Real coordinates use transpose; complex coordinates use conjugate transpose. We write either adjoint as A star. A star A is positive, and absolute value A denotes its unique positive square root. This absolute value is an operator, not entrywise absolute values. The kernel of A consists of directions collapsed to zero. Its orthogonal complement is the surviving input space, also called the support here. The canonical polar factor U preserves lengths on that support and is zero on the kernel. We will construct it and prove A equals U times absolute value A. An arbitrary unitary extension is a separate object.

## PoQuestion: what part of a map changes lengths?

Why: Extend scalar magnitude to operators.
Recall: For a scalar z, absolute value squared is conjugate z times z.

A complex number splits into magnitude and a unit-length phase. For an operator, the magnitude must itself be an operator, because different input directions can stretch by different amounts. The positive square root of A adjoint A is called its modulus or operator absolute value. Polar decomposition asks whether A can be written as that positive length-changing map followed by an isometric motion on the part that survives.
<!-- beat -->
Watch the unit circle stretch into an ellipse. This is an example of a positive map's length effect. The remaining polar factor sends that intermediate image to the actual output without changing its lengths. Singular maps need care: a direction that collapses has no output direction to recover. The canonical remaining factor is then a partial isometry, not necessarily a unitary map. Polar decomposition is classical; this lecture connects that geometry to accepted Tau Ceti APIs.

## PoModulus: Why this square root is the right magnitude

Why: Prove that modulus and original map have the same length effect.
Recall: The adjoint transfers a map across an inner product.

Define absolute value of A as the positive square root of A adjoint A. Squaring gives A adjoint A. Therefore the squared norm of absolute value A applied to x equals the inner product of A adjoint A x with x, which equals the squared norm of A x. This is the crucial identity: modulus and original map give exactly the same output length for every input. Positivity selects the unique positive square root. Entrywise absolute values of a matrix do not generally satisfy this identity and are a different operation.

## PoKernel: Define the remaining motion

Why: Derive the factor instead of assuming it exists.
Recall: The modulus and A give equal output norms.

Define U on the image of the modulus by sending absolute value A applied to x to A x. Why is this well-defined? If two inputs give the same modulus output, their difference has modulus norm zero, hence A norm zero, so they also give the same A output. The same length identity says this map preserves lengths on that image. In finite dimensions this image is the orthogonal complement of the kernel. Define U to be zero on the kernel. We have now constructed a partial isometry with A equal to U times absolute value A. The zero-on-kernel convention makes this factor canonical.

## PoExample: a collapsed direction

Why: Distinguish the canonical factor from a unitary extension.
Recall: R theta denotes an ordinary planar rotation.

Let A stretch the first coordinate by two, collapse the second coordinate, then rotate. Its modulus is diagonal with entries two and zero. Its canonical polar factor rotates the first coordinate direction and sends the second to zero. The two drawn arrows have the same length: one is the modulus output, the other the A output. The factor U carries the first to the second. It preserves lengths only on the surviving line. It is not an orthogonal matrix on the whole plane. One can choose an orthogonal extension in this example, but that would make a different choice on the kernel.

## PoSummary: The scope of the construction

Why: Connect the finite picture to the accepted Hilbert-space theory.
Recall: A partial isometry is isometric on its initial space.

We separated A into a positive modulus and a canonical partial isometry. The equal-norm identity made the construction possible. In Hilbert spaces the image of the modulus need not be closed, so the isometry is first extended to its closure. Accepted Tau Ceti modules cover both finite maps and bounded Hilbert-space operators. These are accepted independent implementations; their presence in our operator roadmap does not mean their proofs were all adapted from DKPS. The census distinguishes their provenance. Keep the canonical partial factor distinct from any further unitary extension.

## PoFacts: Two reusable polar facts

Why: Record what holds even when the map is singular.
Recall: Finite real inner product spaces; A is any linear map.

The first fact is factorization: canonical polar factor composed with operator absolute value equals A. The second says the factor preserves norms on the orthogonal complement of A's kernel. Neither fact requires A to be invertible. The zero-on-kernel convention is part of which factor we are naming. These facts explain why the singular example was a legitimate polar decomposition rather than an exception.

## PoLean: Polar factorization in Lean

Why: Read the canonical factorization without an invertibility assumption.
Recall: $U|A|=A$.

A is an arbitrary linear map between finite real inner product spaces. OperatorAbs names its positive modulus and polarFactor its canonical partial isometry. The composition applies the modulus first and then the factor. The green proof invokes the accepted factorization theorem. Invertibility is not assumed. The canonical factor is already defined with its zero-on-kernel convention, so the factorization statement includes singular maps.

## PoLeanSupport: Support isometry in Lean

Why: Identify where the canonical factor preserves norms.
Recall: $x\in(\ker A)^\perp\Longrightarrow\|Ux\|=\|x\|$.

The hypothesis h x places the input in the orthogonal complement of the kernel of A. On this surviving input space, the canonical polar factor preserves its length. The green proof applies the accepted norm theorem. Without the support hypothesis the statement would fail for a nonzero kernel vector, because the canonical factor sends that vector to zero. This is why a canonical partial isometry must be distinguished from a chosen unitary extension.

## PoComputation: Bonus: Compute the factors with an SVD

Why: Connect singular-value algorithms to the exact kernel convention.
Recall: A equals L times Sigma times V adjoint.

As an optional numerical bonus, here is how this mathematical tool is used in computation. An SVD computes the modulus as V Sigma V adjoint. To get the canonical partial factor, put one on every strictly positive singular direction and zero on every zero singular direction, then multiply by L and V adjoint. Numerical software needs a tolerance to decide effective rank; the exact formula uses strict positivity. Be careful with the name polar decomposition in numerical libraries. For square matrices, SciPy's polar routine returns a unitary factor even at singular inputs. That is a unitary extension, and may differ on the kernel from the canonical factor shown here. Check the convention before comparing numerical output with a formal theorem.
