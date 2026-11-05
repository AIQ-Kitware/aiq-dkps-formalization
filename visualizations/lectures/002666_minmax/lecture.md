# Rayleigh quotients and min-max

See [operator lecture provenance](../../dkvis/learning/operators/README.md) for accepted source modules and scope.
Numerical reference: https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.eigh.html

## MmTitle: Rayleigh quotients and min-max

Why: Connect geometry to eigenvalue stability.
Recall: Symmetric matrices have orthonormal eigenbases.

Rayleigh quotients, min-max, and eigenvalue stability.

## MmSetup: The ordering and the directional measurement

Why: Fix the spectral convention locally.
Recall: $\lambda_0\ge\cdots\ge\lambda_{n-1}$; $\rho_A(x)=x^TAx$ for unit $x$.

We work with real symmetric matrices of size n. The spectral theorem gives an orthonormal eigenbasis. List the eigenvalues in decreasing order, beginning with index zero; repeated eigenvalues are allowed. For a unit vector x, its Rayleigh quotient is x transpose A x. For a nonunit vector the usual quotient divides this expression by squared length, but every vector in our optimization will be normalized. The operator norm of a perturbation H is its largest output length on unit inputs. V names a candidate subspace, and dimension V equals k plus one will be the key constraint. These definitions are all we need to formulate the variational problem.

## MmQuestion: Which eigenvalue facts survive a perturbation?

Why: Control eigenvalues without following individual eigenvectors.
Recall: A is symmetric; its eigenvalues are real.

An eigenvector can change dramatically when two eigenvalues are close. Can we still control the eigenvalues themselves? Yes. Instead of following vectors, measure the quadratic form along every unit direction. The Courant–Fischer variational principle reconstructs each ordered eigenvalue from those measurements. Weyl's perturbation inequality then follows from a uniform bound on the change in those measurements. These are classical results, now available as accepted Tau Ceti theorems. This lecture explains the two inferences behind that connection.

## MmRayleigh: a directional measurement

Why: See the Rayleigh quotient as an average, before optimizing it.
Recall: The vector x has length one.

Take the diagonal matrix with entries five and two. On the unit circle write x as cosine t, sine t. The quadratic form is five times cosine squared plus two times sine squared. The two squared coefficients are nonnegative and add to one, so the result is a weighted average. At the first coordinate direction it is five.
<!-- beat -->
Now turn toward the second coordinate direction. The moving arrow is the input direction, and the displayed number is its Rayleigh quotient. At a right angle the value becomes two. Every intermediate value lies between the two eigenvalues. The general tool is this weighted-average interpretation in an orthonormal eigenbasis; the particular two-dimensional picture is an example.

## MmMinMax: Why the variational formula holds

Why: Prove the upper and lower bounds separately.
Recall: Eigenvalues are decreasing and indexed from zero.

Fix index k. We claim that the k-th eigenvalue equals the best possible minimum Rayleigh quotient over subspaces of dimension k plus one. First take any such candidate subspace V. The span of eigenvectors from index k through the final index has dimension n minus k. These dimensions add to n plus one, so the two subspaces must intersect in a nonzero vector. Normalize that vector. Its Rayleigh quotient uses only eigenvalues at most lambda k. Therefore the minimum on V is at most lambda k. This holds for every candidate, so the outer maximum is at most lambda k.
<!-- beat -->
For the reverse inequality choose the span of the first k plus one eigenvectors. Every unit vector in this particular subspace has quotient at least lambda k, by the weighted-average argument. The k-th eigenvector attains equality. Thus this candidate's minimum is exactly lambda k. It attains the upper bound we just proved, establishing the formula.

## MmWeyl: Pass a uniform bound through both extrema

Why: Turn the characterization into a perturbation theorem.
Recall: Use the same ordering for both symmetric matrices.

Let the perturbation H have operator norm epsilon. Cauchy–Schwarz gives absolute value of x transpose H x at most epsilon for every unit vector x. Thus every directional measurement changes by at most epsilon. Taking a minimum over the same unit vectors preserves both inequalities. Taking a maximum over the same candidate subspaces preserves them again. Courant–Fischer identifies the resulting extrema as the equally ordered eigenvalues. Each eigenvalue therefore changes by at most epsilon. Notice what we did not need: a spectral gap. A gap becomes essential when the object to control is an eigenspace rather than an eigenvalue.

## MmSummary: What the argument used

Why: Retain the proof mechanism, not only the formula.
Recall: The spectral theorem supplies an orthonormal eigenbasis.

The chain was directional measurement, weighted average, dimension-forced intersection, and an attaining leading eigenspace. That established the variational characterization. A uniform perturbation bound then passed through its two extrema to give Weyl stability. Courant and Fischer's principle and Weyl's inequality are classical mathematics. The accepted Tau Ceti CourantFischer file includes a proof adaptation from this project's development; the provenance census records that connection precisely.

## MmFacts: The two reusable facts

Why: Record exact hypotheses alongside the conclusions.
Recall: Finite-dimensional real inner product spaces; symmetric operators.

Here are the facts to carry into another proof. First, the k-th decreasing eigenvalue is the supremum, over subspaces of dimension k plus one, of the infimum Rayleigh quotient on their unit vectors. In finite dimensions these extrema are attained. Second, equally ordered eigenvalues of two symmetric operators differ by at most the operator norm of their difference. The field, finite dimension, symmetry, and indexing convention belong to the statement.

## MmLean: Courant–Fischer in Lean

Why: Match the candidate dimensions and unit-vector restrictions.
Recall: $\lambda_k=\sup_{\dim V=k+1}\inf_{\|x\|=1,x\in V}\langle Tx,x\rangle$.

The assumptions fix a finite real inner product space, symmetric T, and its dimension n. Fin n indexes zero through n minus one. The first supremum ranges over subspaces whose dimension is k plus one. The inner infimum ranges over unit vectors lying in that subspace. These subtype conditions are the exact restrictions in the symbolic formula. The green line applies the accepted Courant–Fischer theorem. The second operator S is part of the shared companion context; it is needed only on the next Weyl card.

## MmLeanWeyl: Weyl stability in Lean

Why: Use the same ordering for the two symmetric operators.
Recall: $|\lambda_k(T)-\lambda_k(S)|\le\|T-S\|$.

Both T and S are symmetric on the same finite real inner product space. Their eigenvalues use the same dimension witness and decreasing index k. The norm on the difference of bounded linear maps is the operator norm. The displayed conclusion is exactly the eigenvalue stability bound. The green line applies the accepted Tau Ceti theorem. There is no eigengap assumption in this statement; controlling eigenspaces is a different problem.

## MmComputation: Bonus: How to compute the spectrum

Why: Separate the proof of stability from a numerical algorithm.
Recall: The variational formula characterizes exact eigenvalues.

As an optional numerical bonus, here is how this mathematical tool is used in computation. For a dense symmetric or Hermitian matrix, use a routine designed for that structure, such as SciPy's eigh. Its implementations reduce the structured problem before solving it; the variational formula is a proof tool, not a prescription to search through all subspaces. Check normalization and the residual of any computed eigenpair. Also check ordering. This lecture and the Lean theorem use decreasing, zero-based eigenvalues. SciPy returns increasing eigenvalues. Reverse the list when comparing corresponding indices. A small residual supports an approximate eigenpair; selecting a particular eigenspace still requires separation information.
