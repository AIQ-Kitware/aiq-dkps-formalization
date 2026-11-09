# Course introduction: Why spectral subspaces move

<!-- BEGIN SPOKEN LECTURE -->

Suppose a symmetric matrix describes a system with two distinct modes. One mode has an eigenvalue of zero, the other an eigenvalue of four, and the two eigenvectors point along perpendicular coordinate axes. What happens if we change the matrix slightly? Will the eigenvalues remain close? Will the eigendirections remain close? And how much separation between the two modes is needed to make either prediction reliable?

Those questions lead to the Davis–Kahan theory of spectral subspaces. They also open a path through geometry, linear algebra, and functional analysis. This course develops that path far enough to explain the central perturbation estimates from their hypotheses, rather than treating them as formulas to be remembered.

## A small change in a matrix

Begin with a two-by-two diagonal matrix whose diagonal entries are zero and four. Its lower eigenspace is the horizontal axis, and its upper eigenspace is the vertical axis. Now put a one in each of the two off-diagonal positions. The new matrix is still symmetric, but it mixes the two coordinate directions.

Its eigenvalues are two minus the square root of five and two plus the square root of five. Each has moved by approximately zero point two three six from its original value. Meanwhile, the lower eigenline has rotated by about thirteen point three degrees. To calculate that angle, diagonalize the new matrix: the magnitude of the tangent of twice the rotation angle is one half.

Two different things have happened. The eigenvalues have moved along the number line, and the eigenvectors have changed direction. We can estimate the first movement without knowing much about the eigendirections. The second depends critically on the gap separating the spectral values. If the two original eigenvalues were almost equal, the same off-diagonal coupling could produce a much larger rotation.

Now imagine two eigenvalues that are exactly equal. There is no distinguished pair of eigenvectors inside their joint eigenspace. We can rotate an orthonormal basis within that space while leaving the underlying operator and the space itself unchanged. This is why the theory asks about subspaces rather than attempting to track every eigenvector individually. A subspace is an intrinsic geometric object; a basis is one way to describe it.

Davis and Kahan developed methods for controlling how spectral subspaces move when the underlying operator is perturbed. Their work asks for quantitative estimates that depend on the size of a perturbation, a residual, and the relevant separation of spectra. Our task is to understand where those estimates come from and when their hypotheses hold.

## How to measure a moving subspace

For two lines through the origin, an angle is easy to picture. For two planes in a much larger space, a single angle may not describe the comparison. One direction may agree almost perfectly while another is far apart. Principal angles describe these different degrees of alignment.

Orthogonal projections provide a way to study subspaces without choosing particular coordinates inside them. A projection keeps the component in a chosen subspace and removes the perpendicular component. From a pair of projections, we can recover the sines and cosines of the principal angles, understand when two subspaces meet at a right angle, and build a canonical rotation that carries one subspace toward the other.

This geometry will have several forms. An orthonormal frame gives coordinates for a subspace; a Gram operator records how its vectors overlap; a graph represents a tilted subspace as a map from one component to its perpendicular complement. Those representations are useful for different proofs. They describe the same underlying geometry, but the choice of representation can make a difficult estimate almost immediate.

The course develops these ideas from linear maps, inner products, adjoints, and orthogonal projections. We begin with familiar finite-dimensional calculations and prove the identities that later let us work without relying on a particular matrix basis.

## Why the foundations go beyond matrices

The starting background is ordinary linear algebra and calculus: matrix multiplication, elementary eigenvalue calculations, derivatives, and integrals. Prior knowledge of Banach spaces, spectral measures, or unbounded operators is not required.

A norm tells us how large a vector or an operator is. Completeness tells us when Cauchy approximations actually converge inside the space under study. Banach spaces package these analytic ideas; Hilbert spaces add inner products and orthogonality. Together they provide a setting in which projections, adjoints, limits, and operator equations can be handled rigorously.

Spectral theory begins with eigenvalues but cannot end there. An operator acting on functions may have spectral values without any corresponding eigenvector. A multiplication operator, for example, can have a continuous range of spectral values even when individual points are not eigenvalues. Spectral projections and spectral measures replace the idea that every operator can be diagonalized using a list of eigenvectors.

Functional calculus then lets us apply functions to self-adjoint operators. It explains positive square roots, operator absolute values, and spectral restrictions. From these constructions come singular values and polar decomposition, which separate how an operator stretches from how it moves directions. Matrix exponentials and skew-adjoint generators provide another description of rotations and continuous motions.

The infinite-dimensional case brings a further complication: some important self-adjoint operators are defined only on a dense domain, rather than on every vector. Differential operators are common examples. Multiplying such operators, restricting them to subspaces, or passing to limits requires domain conditions. The course establishes the spectral cutoffs, resolvent arguments, and closed-operator facts needed to carry the finite-dimensional reasoning into this setting.

## The mechanism behind an angle estimate

Here is the central proof idea. Suppose a self-adjoint operator has an exact invariant subspace, and we have an approximate subspace obtained from a computation or an experiment. The approximate subspace is represented by an orthonormal frame. Apply the operator to that frame, then subtract the part predicted by the operator compressed to the trial subspace. What remains is called the residual.

If the residual vanishes, the trial subspace is invariant. If it is small, the trial subspace is approximately invariant. But a small residual alone does not tell us which exact spectral subspace it approximates. We also need spectral separation from the unwanted part of the operator.

Projecting the residual into the orthogonal complement of the target subspace produces an operator equation. The unknown in that equation measures how far the trial frame leaks into the complementary space. The equation has the form of a Sylvester equation: one operator multiplied by the unknown, minus the unknown multiplied by a second operator, equals a known residual.

In a diagonal matrix, solving the equation amounts to dividing by differences of eigenvalues. The general theory makes that division precise. Under the right spectral-gap hypotheses, a bound for the inverse Sylvester operator becomes a bound for the sine of a subspace angle.

Different spectral gaps support different estimates. If one spectral set lies entirely above another, we have an ordered separation. If the sets are merely a positive distance apart, without an ordering, some of the same arguments require a different norm or a different constant. Knowing exactly which gap is being used is part of constructing a correct proof.

There is also more than one way to measure an operator. The operator norm measures its largest stretching factor; the Frobenius or Hilbert–Schmidt norm combines the squares of all singular values. Ky Fan sums and majorization compare entire singular-value lists. Davis and Kahan also studied unitarily invariant norms, whose value is unchanged by unitary changes of coordinates. In infinite dimensions, an estimate in an ideal norm must also account for which operators actually belong to that ideal.

## Four angle families, with different hypotheses

The principal perturbation results control the sine of an angle, the tangent of an angle, the sine of twice an angle, and the tangent of twice an angle. They are related, but they are not interchangeable.

Sine bounds measure how much a trial subspace enters the unwanted orthogonal complement. Tangent bounds become natural when a nearby subspace can be written as a graph over the exact one. A reflection across a subspace can turn an ordinary angle into a doubled-angle problem, especially for off-diagonal perturbations. For a tangent-of-twice-the-angle estimate, the choice of angular branch is essential: a small value of the sine of twice an angle, by itself, does not tell us whether the original angle is close to zero or close to ninety degrees.

The proofs therefore develop both the estimates and the geometric conditions that allow us to use them. We will distinguish results for a single largest angle from results controlling a whole singular-value list, and finite-dimensional arguments from those that require spectral measures or operator ideals. Real and complex Hilbert spaces also deserve explicit attention, because complex spectral methods sometimes need to be transferred back to the real setting.

## What happens after the angle estimates

Subspace geometry leads to a second question: when many rotations or unitary maps carry one subspace to another, which one moves the ambient space the least? A canonical direct rotation arises naturally from the geometry of two projections. Its existence and its optimality depend on the setting and on what displacement is being measured.

The original 1970 paper contains a broad claim about unsquared whole-space displacement that is false. A concrete four-dimensional real counterexample separates that claim from valid optimality results for restricted displacement and squared whole-space displacement. Studying the counterexample is part of understanding the geometry, not an aside about historical wording.

The theory also meets concrete calculations. A free-beam problem uses a fourth-order differential operator, trial functions, a Rayleigh–Ritz matrix, and residual estimates to study approximate modes. Other applications connect the same subspace ideas to singular-vector perturbations, spectral statistics, and the alignment of numerical embeddings. These settings show which aspects of a proof remain the same when the objects and norms change.

Section ten of the 1970 paper raises questions that reach beyond the estimates established there. We will examine the proved results, the counterexamples, and the questions left open by the arguments themselves.

## What understanding the theory should mean

By the end, you should be able to take a proposed angle estimate and identify the exact and trial subspaces, the residual, the relevant spectral gap, and the norm in which the estimate is supposed to hold. You should be able to derive the operator equation behind the bound, explain how its inverse is controlled, and recognize when domains, norm-class membership, or angular branch selection require an additional argument.

The course is built from proofs, worked examples, and counterexamples so that these decisions become intelligible. The two-by-two matrix at the beginning is a small instance of the larger problem: spectral information can move under perturbation, and geometry plus spectral separation tells us how much. The goal is to understand that mechanism well enough to reconstruct it in settings where a picture of two rotating lines is no longer sufficient.

<!-- END SPOKEN LECTURE -->
