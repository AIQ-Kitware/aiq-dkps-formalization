# Spoken companion to *Formalizing Davis–Kahan Perturbation Theory in Lean 4*

**Purpose and maintenance.** This is a read-aloud transcript of the paper, intended for text-to-speech playback while the listener follows the manuscript. It follows the uploaded 28-page version dated October 28, 2026, including its three figures, theorem numbering, and section order. The spoken text is a faithful guided reading rather than a verbatim pronunciation of every symbol. It converts mathematical displays into spoken English, omits bibliography entries and administrative details, and sometimes explains a step as an instructor would. Horizontal rules separate brief instructor interjections from the main reading. When the paper changes, update the corresponding transcript sections, page cues, theorem statements, formulas, figure descriptions, and appendix coverage together; do not carry forward claims from an older paper version. The accompanying PDF is the authoritative source for precise symbols.

# Formalizing Davis–Kahan Perturbation Theory in Lean 4: a classroom reading

## Abstract — manuscript page 1

We begin with the abstract.

This paper formalizes the theory of spectral-subspace perturbations developed by Chandler Davis and William Kahan in their 1970 paper, using the Lean 4 proof assistant.

The authors identify twenty-nine results to formalize. Twenty-eight are proved under the assumptions of the original source. The remaining result, Proposition four point four, is refuted by an explicit counterexample.

The work reaches beyond finite-dimensional matrix perturbation. It covers the sine and tangent theorems, direct rotations, principal angles, estimates for Sylvester equations, unitarily invariant operator-ideal norms, and unbounded self-adjoint operators.

A substantial part of the contribution is the mathematical infrastructure required to express those results. Some of this infrastructure was subsequently adapted into the Tau Ceti library, while other foundations were adapted from Mathlib and the Spectra project.

Examining the original displacement claim leads to a counterexample in four-dimensional real space. The counterexample works even when the principal angles are arbitrarily small and positive. The paper identifies a failed comparison involving singular values, and establishes an optimality statement for the narrower class called Q-norms.

Finally, the development enables a separate optimization result: in real finite-dimensional spaces, the minimum trace-norm cost of transporting one subspace onto another can be computed by a weighted matching problem on the principal angles.

The central theme is that formalizing classical mathematics can produce reusable foundations, expose a mistake in a published argument, and support further mathematical results.

---

Before continuing, keep two kinds of achievement separate. One is formalizing the Davis–Kahan results themselves. The other is investigating a new question made accessible by the resulting library. The matching theorem is not being presented as a logical consequence of the sine-theta theorem. It is a subsequent result using related foundations.

---

## Section 1. Introduction — manuscript pages 1 through 3

Suppose we have a linear operator and a vector that we think is approximately an eigenvector. An exact eigenvector has a defining property: applying the operator changes its magnitude, but not its direction. The output equals the input multiplied by the corresponding eigenvalue.

For an approximate eigenvector, that equation does not hold exactly. We can measure the discrepancy. Apply the operator to the candidate vector. Subtract the candidate vector multiplied by the proposed eigenvalue. The difference is called the residual.

A small residual tells us that the candidate nearly satisfies the eigenvector equation. But there is a complication. When eigenvalues are equal, or very close together, individual eigenvectors can be a poor way to identify what has remained stable. Different choices of eigenvectors may span exactly the same invariant subspace. This makes the subspace itself the more meaningful object to compare.

Davis–Kahan theory controls the angle between an approximate subspace and an exact spectral subspace. The bound depends on the size of the residual, or of the perturbation producing it, and on the separation between the relevant parts of the spectrum.

For example, imagine that we have a Hermitian matrix A and a nearby matrix, called A hat, obtained by adding a perturbation H. If we know an eigenspace of A hat, then the norm of H can control its residual relative to A. This can give a bound on the angle between the computed eigenspace and the desired spectral subspace of A, even without explicitly evaluating that residual.

The project began with a form of this estimate needed in the data kernel perspective space, abbreviated D K P S. From there, the work expanded to formalizing the results in the original 1970 paper.

Importantly, the original paper is not restricted to small Hermitian matrices. It treats real and complex Hilbert spaces, possibly unbounded self-adjoint operators, and broad classes of operator norms. Its spectral-gap conditions also include intervals extending indefinitely in one direction. Such hypotheses cannot be represented adequately by specializing everything to finite matrices.

The completed source inventory covers the four headline theorems in Section 2 of Davis and Kahan, together with every named theorem, proposition, lemma, and corollary they established. There are twenty-nine targets. Twenty-eight are formalized; one printed assertion, Proposition four point four, is false.

That proposition concerns the canonical direct rotation between two real subspaces. It claims a form of minimum displacement when the largest principal angle is at most sixty degrees. The project gives a counterexample involving two planes in real four-dimensional space. The counterexample has two equal principal angles, and can be made to work at arbitrarily small positive angles. Its competing transporter also attains the true global minimum trace-norm cost for the constructed pair.

The broader mathematical ingredients required by the formalization include principal-angle operators, direct rotations, approximation numbers, symmetric operator ideals, Borel functional calculus, and estimates for Sylvester equations involving unbounded operators. Existing mathematics from Mathlib and Spectra was adapted where appropriate. Some results developed here, including Courant–Fischer and Weyl results, rectangular unitarily invariant seminorms, and projection-valued measures, subsequently contributed to Tau Ceti.

The paper presents four contributions. First, the source-level Davis–Kahan formalization, including its unbounded sine-theta statement. Second, the reusable operator-theoretic foundations. Third, a counterexample and a corrected Q-norm conclusion for Proposition four point four. And fourth, the reduction of real trace-norm transport to weighted matching on principal angles.

---

Here is a useful distinction to keep in mind throughout the lecture. Eigenvalue perturbation asks how the numerical spectral values change. Eigenspace perturbation asks how the directions or subspaces associated with those values change. A perturbation may be small in absolute size and still change an eigenspace dramatically if the relevant spectral gap is just as small. The gap is therefore part of the theorem, not a technical decoration.

---

## Section 2. Mathematical background — manuscript pages 3 through 10

We are now entering the historical and mathematical background of the paper. The story brings together several lines of research that were originally motivated by different questions.

Principal angles tell us how to compare subspaces. Residuals tell us how badly a candidate subspace fails to respect an operator. Sylvester estimates connect those two measurements when suitable spectral separation is available. Operator ideals and symmetric norms allow the same theory to cover several different ways of measuring error.

The paper cites three historical surveys as guides to this lineage. Paige and Wei trace the history of the cosine–sine decomposition. Barry Simon explains important parts of Kato's operator theory and its relationship to Sz.-Nagy's constructions. Böttcher and Spitkovsky survey the theory of two orthogonal projections, including work of Dixmier, Davis, and Halmos.

On page three, Table 1 compresses this history into a map from mathematical predecessors to formalization needs. Jordan, Davis, and Halmos contribute the geometry of subspaces and projections. Rayleigh, Ritz, and Weyl contribute eigenvalue approximation and spectral comparison. Rellich, Sz.-Nagy, and Kato contribute perturbation of spectral subspaces and unitary transport. Sylvester and Rosenblum contribute separated operator equations. Von Neumann, Schatten, and Ky Fan contribute singular-value norms. Davis and Kahan bring those ideas together in spectral-subspace perturbation estimates.

We will now walk through that development one piece at a time.

### Section 2.1. Principal angles — manuscript pages 3 and 4

Camille Jordan studied the geometry of linear subspaces in higher dimensions in 1875. For two lines, one angle is enough to describe their relative position. For two larger subspaces, it is not. We need a sequence of principal angles.

Principal angles come from choosing directions in the first subspace and matching them with directions in the second subspace. We choose the pair that comes closest, then continue under orthogonality constraints. The important result is independent of which orthonormal bases we originally used.

The paper gives a matrix formulation. Let X and Y be matrices whose columns form orthonormal coordinates for two equally sized subspaces. Multiply the conjugate transpose of X by Y. This overlap matrix records the inner products between the two coordinate frames. Its singular values are the cosines of the principal angles.

In words, the singular value corresponding to angle theta number j equals the cosine of that angle. Principal angles lie between zero and ninety degrees.

If one principal angle is zero, the corresponding directions coincide. If it is ninety degrees, those directions are orthogonal. For an acute positive angle, the corresponding pair of principal vectors describes an ordinary two-dimensional rotation inside a principal plane.

The same ideas show up in other fields. Harold Hotelling's canonical correlation analysis asks for maximally correlated linear combinations of two sets of variables. After appropriate normalization, the canonical correlations are also singular values of an overlap map. In numerical linear algebra, Björck and Golub gave algorithms for computing principal angles and vectors using orthonormal matrix factorizations.

Another expression of the geometry is the cosine–sine decomposition of a partitioned orthogonal or unitary matrix. Its blocks contain matching cosine and sine factors. The paper traces its development through Davis and Kahan, Stewart, and Paige and Wei. In the formalization, finite-dimensional principal planes are useful for explicit calculations, while Hilbert-space statements use projections and functional calculus.

---

The distinction between a subspace and a particular basis is fundamental. A two-dimensional plane can be spanned by infinitely many different orthonormal pairs. A theorem about the plane should not depend on which pair we happened to choose. Principal angles are one way to describe precisely the basis-independent information.

---

### Section 2.2. Eigenvalue approximation — manuscript pages 4 and 5

The next historical thread begins with a different question. If an eigenvalue problem is too difficult to solve exactly, how can we approximate its eigenvalues and eigenvectors?

Lord Rayleigh used trial shapes and energy ratios to estimate vibration frequencies. Walter Ritz developed a systematic variational method in the early twentieth century. In a Rayleigh–Ritz method, we choose a smaller trial space and solve an approximate eigenvalue problem within it. This is how an infinite-dimensional problem can be approximated by finite-dimensional calculations.

The Rayleigh quotient expresses the average action of a self-adjoint operator along a chosen direction. Take a nonzero vector x. Apply the operator A. Form the inner product of A x with x, and divide by the squared length of x. For a unit vector v, the quotient is simply the inner product of A v with v.

When we use that number as an approximate eigenvalue, the residual is A v minus that number times v.

The Courant–Fischer min–max principle characterizes eigenvalues by extremizing Rayleigh quotients over subspaces. Weyl-type inequalities then control how ordered eigenvalues change under a Hermitian perturbation.

The paper gives the standard modern form of such an estimate. If A hat equals A plus H, and we arrange the eigenvalues of both matrices in the same order, the maximum absolute difference between corresponding eigenvalues is no greater than the operator norm of H.

But stable eigenvalues do not guarantee stable eigenvectors. Look at the two-by-two example on page five. The first diagonal matrix has zero in the upper-left position and epsilon in the lower-right position. The second matrix swaps those two diagonal entries. Both matrices have the same two eigenvalues, zero and epsilon. Their difference has operator norm epsilon. Yet the eigenvector for the lowest eigenvalue changes from one coordinate axis to the perpendicular axis.

The spectral gap in each matrix is also epsilon. The perturbation is small in absolute terms when epsilon is small, but it is not small relative to the gap.

Rellich developed rigorous perturbation methods for self-adjoint operators, and Kato later organized much of that theory. The Davis–Kahan residual bounds extend the approximation story from eigenvalues to subspaces. They answer whether an approximately invariant trial space is geometrically close to an exact spectral subspace.

### Section 2.3. Two orthogonal projections — manuscript pages 5 and 6

We now move from finite-dimensional coordinate frames to Hilbert spaces. A closed subspace of a Hilbert space has an orthogonal projection. That projection is a bounded operator, even if the subspace is infinite dimensional.

Let P and Q be the projections onto the two subspaces we want to compare. Consider the operator P Q P, restricted to the range of P. This is a compression: start in the first subspace, apply Q, and project back into the first subspace.

In finite dimensions, the eigenvalues of this compressed operator are the squared cosines of the principal angles. In infinite dimensions, it need not have a discrete list of eigenvalues. Nevertheless, functional calculus allows us to define square roots and functions of this operator. That gives an operator-valued version of cosine and sine, rather than only a finite angle list.

Dixmier studied relative positions of closed subspaces in 1948. Chandler Davis developed closeness and separation operators in his 1958 work. Paul Halmos, in 1969, gave a particularly useful structural description of a pair of subspaces.

Halmos's description first separates four intersection spaces: directions belonging to both subspaces, directions in the first but orthogonal to the second, directions in the second but orthogonal to the first, and directions orthogonal to both. On the remaining generic component, the pair of projections has a common two-by-two block form.

The first projection is identity in the first block and zero in the second. The other projection has cosine squared in its upper-left block, sine squared in its lower-right block, and cosine times sine in the two off-diagonal blocks. These cosine and sine operators commute, are positive contractions, and have squares adding to the identity.

This is the infinite-dimensional analogue of two-dimensional principal planes. The main difference is that the entries are operators, not scalar cosine and sine values.

The intersection spaces matter for another reason. Directions lying in the first subspace and orthogonal to the second, and vice versa, are right-angle defect spaces. These affect whether an operator with the required transport properties exists.

An operator T is called an intertwiner for P and Q if applying T after P gives the same result as applying Q after T. In symbolic terms, T P equals Q T. This means that T carries vectors from the source subspace into the target and behaves consistently on the complementary parts.

In finite dimensions, familiar principal-plane decompositions recover these structures. In general Hilbert spaces, one needs operator-valued angles, spectral calculus, and explicit treatment of the defect spaces.

### Section 2.4. Transport between nearby spectral subspaces — manuscript page 6

Now ask a constructive question. Given two nearby subspaces, can we find a unitary operator that carries one onto the other in a canonical way?

The history here runs through Sz.-Nagy and Kato. Sz.-Nagy developed a construction for nearby projections in the 1940s. Kato gave an especially useful algebraic expression and applied it to perturbation theory.

Take the two orthogonal projections P and Q. Define T as Q P plus the product of I minus Q and I minus P. The first term maps the source subspace toward the target. The second handles the complementary spaces. The key intertwining identity is that T P equals Q T.

There is also a decisive algebraic identity. The adjoint of T times T equals the identity minus the square of P minus Q.

If the operator norm of P minus Q is strictly smaller than one, that positive operator is invertible. We may take its inverse square root. Multiplying T by this inverse square root produces a unitary U. That unitary conjugates P into Q. In other words, U carries the range of P onto the range of Q and also maps the orthogonal complements correctly.

This is an application of polar decomposition. The original operator T factors into a unitary part times a positive stretching part. Extracting the unitary part gives the canonical direct rotation.

For two finite-dimensional acute subspaces, the direct rotation acts through the principal angles in their principal planes and fixes common directions. For a general Hilbert-space pair, the projection formula defines the same construction without choosing a basis.

The inequality that the norm of P minus Q is less than one is the acute condition. In equal-dimensional finite spaces it corresponds to the largest principal angle being less than ninety degrees.

Notice the source of the later optimality question. Many different unitaries can carry the first subspace onto the second. The polar construction selects a canonical one. But is this particular unitary the cheapest one according to every sensible notion of displacement? Davis and Kahan investigate precisely that question.

---

It is useful to separate the existence of a canonical transport from its optimality. The polar factor gives a mathematically distinguished unitary. That fact alone does not say it minimizes every norm of identity minus that unitary. The counterexample later in the paper depends on this distinction.

---

### Section 2.5. Spectral projections and residuals — manuscript pages 6 through 8

A spectral subspace is a subspace selected by the spectrum of a self-adjoint operator. In finite dimensions, we can think of choosing eigenvectors whose eigenvalues lie in some interval and taking their span. In Hilbert space, this is expressed more generally using the spectral theorem.

The spectral theorem associates a projection-valued measure with a self-adjoint operator. Given a suitable set of spectral values, the measure returns an orthogonal projection onto the corresponding spectral subspace.

This is important because an unbounded self-adjoint operator still has bounded spectral projections. The operator itself cannot be applied to every vector. Its domain must be specified. The Hellinger–Toeplitz theorem tells us that a symmetric operator defined everywhere on a Hilbert space must be bounded. Thus an unbounded self-adjoint operator necessarily has a proper domain.

For an isolated spectral cluster, spectral projections can also be expressed using a contour integral of the resolvent. The resolvent at a complex number z is the inverse of z times the identity minus the operator, when that inverse exists and is bounded. Integrating the resolvent around a contour enclosing an isolated spectral cluster produces the projection onto that cluster.

The paper uses this historical construction to explain the role of resolvents, but the formal development also needs Borel spectral projections for intervals that may extend indefinitely. An unbounded operator's spectrum cannot always be handled by choosing a finite list of eigenvectors or a small contour around an isolated group.

Now return to the perturbation problem. Davis's papers in 1963 and 1965 led toward the 1969 announcement with Kahan and their extended 1970 treatment.

We start with an ambient operator, called A hat in this manuscript. We also have a trial-coordinate space, embedded into the ambient space by an isometry E naught. An isometry preserves lengths and inner products. On the trial-coordinate space there is a self-adjoint trial operator A naught.

The residual measures the difference between two procedures. First, embed a trial vector and apply A hat. Second, apply A naught in trial coordinates and then embed. Subtract the second result from the first.

If the residual is zero, the trial coordinate representation intertwines with the ambient operator, and the trial subspace is invariant. If the residual is nonzero, it measures the failure of exact invariance.

Let P project onto the desired exact spectral subspace. Applying I minus P after E naught extracts the unwanted component of the trial vector. The positive modulus of this map is the sine of the angle operator on trial coordinates.

This last point will matter in the formal proof. The complementary map goes from trial coordinates into the ambient Hilbert space. Its modulus acts on the trial-coordinate space. The sine of the angle operator also acts on trial coordinates. Although the types are different for the rectangular map and the positive sine, they have the same singular-value norm whenever the norm is defined.

### Section 2.6. Sylvester estimates — manuscript page 8

The next ingredient is an operator equation associated historically with Sylvester and later Rosenblum.

Start with the scalar equation: b minus a, multiplied by x, equals y. If b and a are separated by at least a positive amount delta, then delta times the magnitude of x is at most the magnitude of y.

The Sylvester equation is the operator analogue. Instead of the scalar multiplication b x minus x a, we have B X minus X A. Under suitable spectral separation, the size of X is controlled by the size of B X minus X A, divided by the gap.

Davis and Kahan use this with a very particular X. Let F one provide isometric coordinates for the unwanted complementary spectral subspace. Take its adjoint and compose it with the trial embedding E naught. That gives X, the coordinates of the trial-space leakage into the unwanted subspace.

The residual identity becomes a Sylvester equation. Lambda one times X minus X times A naught equals the adjoint of F one applied to the residual R.

If the spectra satisfy the interval-versus-exterior or ordered-gap hypotheses of the theorem, we get the bound: delta times the norm of X is at most the norm of F one adjoint applied to R, and that is at most the norm of R itself.

This is the crucial bridge from the residual to the subspace angle. The geometry tells us that the norm of X equals the norm of the sine of the angle operator. The spectral separation tells us how to bound X by the residual.

The proof must handle domains carefully when the operators are unbounded. The equality of operators is initially asserted on an appropriate domain, with a bounded residual on the right. The finite-interval and ordered half-line gap assumptions are also mathematically different cases, so the formal theorem keeps them separate.

---

The full sine-theta proof is already visible in outline. There are three ingredients: the sine of the angle is the size of the unwanted component, the unwanted component satisfies a Sylvester equation, and the gap makes the Sylvester equation stable. The rest of the formalization work is making those three steps valid with the correct operator domains and norm assumptions.

---

### Section 2.7. Operator ideals and displacement norms — manuscript pages 8 and 9

We now need a language for measuring operators. The norm is not merely a cosmetic choice. Different norms can prefer different transformations.

Von Neumann's work on unitarily invariant matrix norms showed the importance of symmetric gauge functions of singular values. Schatten developed normed ideals of operators. Ky Fan developed partial-sum comparisons that are central to majorization arguments.

For a matrix, singular values are nonnegative numbers describing its stretching along principal directions. A unitarily invariant norm depends on these values, not on arbitrary choices of orthonormal coordinates.

The Schatten family illustrates the options. For exponent p, take the p-th powers of the singular values, add them, and take the p-th root. At p equal to one, this gives the trace norm, also called the nuclear norm: add all singular values. At p equal to two, it gives the Frobenius norm, or Hilbert–Schmidt norm: square the singular values, add them, and take the square root.

In infinite dimensions, a Schatten ideal consists of operators for which the corresponding infinite sum is finite. The norm need not be finite for every bounded operator. This is why the source's qualification that the norm is considered where defined matters in the Lean statement.

For displacement, the relevant operator is the identity minus a unitary transporter. The operator norm asks for its single largest singular value. The trace norm adds all its singular values. Thus one transformation that moves many directions slightly and another that moves fewer directions more substantially can have opposite rankings under the two norms.

Davis had established Hilbert–Schmidt and certain finite-dimensional Schatten optimality properties in 1958. Davis and Kahan later distinguished restricted displacement, squared full displacement, and unsquared full displacement. Restricted displacement tests how the transformation moves vectors in the source subspace. Full displacement tests the entire ambient space. Squared full displacement concerns the positive operator formed by taking the adjoint of identity minus W and multiplying it by identity minus W.

These are different optimization objectives. A valid inequality for one does not automatically give a valid inequality for another.

The authors themselves showed a complex-phase construction that could improve the trace norm of the unsquared full displacement. Their Proposition four point four nevertheless asserted a real, small-angle optimality claim. The paper will show why that assertion fails.

Bolotnikov, Li, and Rodman later studied related minimum-distortion problems, including Frobenius and Q-norm results and counterexamples below Schatten exponent two. Subsequent research also distinguishes distances along Grassmannian paths from the extrinsic displacement of an ambient unitary.

### Section 2.8. The Davis–Kahan angle estimates — manuscript pages 9 and 10

This subsection brings the ingredients together in one chain of inequalities. It is worth following on page nine.

Start with the residual R, the desired exact spectral projection P, and the unwanted component of the trial subspace. Use isometric coordinates F one for the unwanted spectral block, and let X be F one adjoint times E naught.

By the projection and modulus identities, the norm of X equals the norm of the positive sine of the principal-angle operator.

By the Sylvester estimate, delta times the norm of X is at most the norm of F one adjoint applied to R.

Because F one is an isometry, its adjoint is a contraction. Applying it cannot increase a supported unitarily invariant ideal norm. So that intermediate norm is at most the norm of R.

Put the statements together. Delta times the norm of sine theta naught equals delta times the norm of X. That is at most the norm of F one adjoint R. And that is at most the norm of R.

This is the sine-theta bound. The left side is the subspace error scaled by the spectral separation. The right side is the residual.

The related tangent and double-angle estimates use other projection blocks. In particular, the sine of twice an angle is small both near zero degrees and near ninety degrees. A small double-angle sine therefore does not determine which angular branch is present. The spectral branch-selection theorems resolve that ambiguity using additional spectral information.

### Section 2.9. Numerical and statistical applications — manuscript page 10

Davis–Kahan theory has important descendants in numerical linear algebra and statistics.

Wedin studied perturbations of singular subspaces for rectangular matrices. Björck and Golub developed ways to compute principal angles. Stewart and others studied sensitivity in pseudoinverses, projections, and least-squares problems. Paige and Wei later explained the history of the cosine–sine decomposition connecting these geometric and computational ideas.

In statistics, the exact covariance matrix of a population may be unknown, but an empirical covariance matrix is available from samples. Its principal eigenspaces can be compared with those of the population matrix. Statistical concentration results control the perturbation; Davis–Kahan-type inequalities then turn that perturbation control into an angle bound.

The paper mentions work by Yu, Wang, and Samworth, as well as a broad survey of spectral methods for data science. The Davis–Kahan estimate contributes a deterministic step to these statistical arguments. Probabilistic claims require additional concentration results.

### Section 2.10. Foundations used in the formalization — manuscript pages 10 and 11

The background section closes by connecting historical mathematics to the Lean development.

Principal-angle geometry and Halmos's two-projection picture require positive operator functions and angle operators rather than arbitrary chosen eigenbases.

The Sz.-Nagy–Kato construction requires polar decomposition, square roots, and the transfer of appropriate results between complex and real settings.

Spectral projections require Borel functional calculus, including in the presence of unbounded operators. Sylvester estimates require explicit operator domains and bounded approximations. Schatten and Ky Fan arguments require approximation numbers and symmetric operator ideals.

The authors formalized these ingredients in Lean 4 using Mathlib, with spectral-measure and Borel-calculus work also adapted from the Spectra project. Some of their work on Courant–Fischer, Weyl, rectangular unitarily invariant seminorms, and projection-valued measures was subsequently adapted into Tau Ceti. Other Tau Ceti work, including canonical polar decomposition, was developed independently upstream.

The final point of this subsection is a conceptual separation. The sine-theta theorem estimates how far a subspace moves under perturbation or approximation. The direct-rotation optimization problem asks which unitary or orthogonal map best transports one already-specified subspace onto another. These are different mathematical questions, sharing the underlying geometry and norm theory.

---

We have reached the end of the historical chapter. The unifying question was not simply who proved what first. It was which ideas must exist before one can even state and prove the full 1970 result. The answer includes subspace geometry, spectral calculus, residual equations, spectral separation, and normed operator ideals. Each of those becomes a concrete dependency in the formalization.

---
## Section 3. Davis–Kahan formalization and the sine-theta theorem — manuscript pages 11 through 14

We now arrive at the formalization itself.

The authors' source targets are the four headline theorems from Section 2 of Davis and Kahan's original paper, and every named theorem, proposition, lemma, and corollary proved in that work. The resulting twenty-nine statements cover sine and tangent inequalities, direct-rotation geometry, operator equations, generalized perturbation bounds, and spectral-selection results. Twenty-eight are proved, and the full-displacement claim of Proposition four point four is refuted.

The paper chooses the sine-theta theorem as a representative detailed example, because it displays the interaction among all the important formal prerequisites.

### Section 3.1.1. Trial and exact subspaces — manuscript page 11

First, we must identify the spaces and maps carefully. The paper uses A for the reference operator and A hat for the perturbed ambient operator, with A hat equal to A plus H. This notation is slightly different from the Lean declaration, which calls the perturbed ambient operator A.

The ambient Hilbert space is called E. The trial-coordinate Hilbert space is called F. We have an isometric map E naught from F into E. The range of that map is the trial subspace. This is how we give coordinates to the trial space while keeping its embedding into the ambient space explicit.

The trial operator A naught is self-adjoint on F. In a finite-dimensional Rayleigh–Ritz construction, we could choose A naught by first embedding into E, applying A hat, and then returning to trial coordinates with the adjoint of E naught. But the theorem also allows a different self-adjoint trial operator.

The residual R is the difference between A hat composed with E naught and E naught composed with A naught. Read that as: apply the ambient operator after embedding, minus embed after applying the trial operator.

If A hat or A naught is unbounded, that difference cannot be assumed to be defined everywhere. The formula is required on the domain of A naught, with a suitable inclusion into the domain of A hat. The theorem assumes a bounded residual operator agreeing with that expression on the required domain.

Next we need the exact spectral decomposition. F naught is an isometry from an exact-coordinate space into the ambient space. Its range is the desired spectral subspace. F one is an isometry from a complementary-coordinate space into the same ambient space. Its range is the orthogonal complement of the exact subspace.

Lambda one is a self-adjoint operator describing the action of A hat on that complementary subspace. The corresponding intertwining identity says that applying A hat after F one agrees with applying Lambda one before F one, on the appropriate domain.

The formal predicate named Is Exact Spectral Decomposition records this data, including the orthogonality of the two exact ranges and the fact that together they fill the ambient space.

---

A quick way to remember the map types is this. E naught and F naught are both arrows into the ambient Hilbert space, but they start from different coordinate spaces. E naught represents the trial space. F naught represents the desired exact space. F one represents the exact unwanted complement. The residual lives between trial coordinates and the ambient space. The sine of the angle operator lives entirely on trial coordinates. This distinction helps avoid many type confusions.

---

### Section 3.1.2. The sine operator and its rectangular representative — manuscript page 12

The source angle operator is defined on trial coordinates. Let P be the orthogonal projection onto the exact target subspace. In terms of F naught, this projection is F naught times F naught adjoint.

The cosine of the angle operator is the positive square root of E naught adjoint times P times E naught. The sine of the angle operator is the positive square root of the identity minus that same compressed projection.

These are positive operators acting on the trial-coordinate space.

Now define S to be I minus P, followed by E naught. In words, embed a trial vector and discard the component in the exact target subspace. The result is the unwanted component in the ambient space. S is a rectangular operator, from trial coordinates into the ambient space.

The adjoint of S times S equals I minus E naught adjoint P E naught. Therefore the positive modulus of S is exactly the sine of the trial-coordinate angle operator.

The paper writes this as Equation seventeen.

This identity is powerful because it relates two different-looking representations of the same geometric quantity. S directly produces the unwanted component as an ambient vector. The positive sine records its singular-value magnitude as an operator on trial coordinates.

Taking polar decomposition of S separates its positive modulus from a partial isometry. The unitarily invariant ideal norms of S and its modulus agree whenever they are finite. Thus the norm of S equals the norm of sine theta naught.

### Section 3.1.3. Gap geometry and the inequality — manuscript pages 12 through 14

The theorem now introduces a positive separation parameter, delta. There are three forms of the spectral-gap hypothesis.

The first is an interval-versus-exterior configuration. One spectrum lies inside a closed interval from beta to alpha. The other spectrum lies entirely outside a larger interval, at least delta below beta or at least delta above alpha. We can exchange which of the two operators is on the inside.

The other two are ordered configurations. In one, the trial operator lies above some threshold plus delta, while the unwanted exact block lies at or below the threshold. In the other, their order is reversed.

For unbounded self-adjoint operators, these ordered relationships are expressed using quadratic-form inequalities on the operators' domains. Saying that A naught is greater than or equal to a scalar multiple of the identity means that its quadratic form is bounded below accordingly for every vector in its domain.

The paper gives a simple infinite-dimensional example. On the square-summable sequence space, let A naught act diagonally by n plus delta, and let Lambda one act diagonally by negative n. Their spectral locations are ordered and separated, but neither is bounded. Their domains consist of the sequences for which the images remain square summable. This example shows why the ordered half-line case cannot be replaced by a theorem requiring a bounded spectral interval.

There is also a domain requirement for the trial embedding. The composition A hat followed after E naught and the composition E naught after A naught must agree on the relevant common domain in the precise way required to define the residual. The source's common-domain condition supplies this inclusion.

Now look at Figure 1 on page thirteen. The figure has two panels showing a one-dimensional trial space inside real two-dimensional space. In the left panel, a trial unit vector makes an angle theta with the desired exact line. Its perpendicular component has length sine theta. In the right panel, the vector obtained by applying A hat is compared with the trial scalar multiple of the original vector. The difference is the residual, drawn as a triangle. For the Rayleigh choice of the trial scalar, the residual is perpendicular to the trial line.

In this specific drawing, A hat is diagonal with entries one point nine and zero point seven, theta is forty degrees, and the chosen separation delta equals the trial scalar minus zero point seven. Projecting the residual onto the exact unwanted line gives a component whose length equals delta times sine theta. Its norm cannot exceed the norm of the full residual.

The figure illustrates the same inequality that the theorem proves in general, but with a single trial vector rather than an arbitrary trial-coordinate Hilbert space.

The theorem itself is now stated as Theorem 1, the sine-theta estimate.

Let the scalar field be either the real or complex numbers. Let the ambient Hilbert space be separable. Assume the ambient, trial, and unwanted complementary operators are self-adjoint, with the trial and exact coordinate maps, residual identity, and domain inclusions we have described. Assume one of the three spectral-gap configurations with a positive delta. Choose a supported normalized symmetric operator-ideal norm, and assume that both the sine operator and the residual have finite norm in that ideal.

Then delta times the norm of sine theta naught is at most the norm of the residual R.

This is Equation eighteen.

The manuscript displays the Lean theorem signature immediately afterward. We do not need to pronounce every line of the declaration. What matters when reading it is how its pieces correspond to the mathematical statement.

The Lean name begins with sine theta, followed by unbounded, form gap, where defined, unitarily invariant norm, and real-or-complex. The declaration takes the ideal norm, three operators, three isometries, and a residual; it then takes self-adjointness hypotheses, the trial residual predicate, the exact decomposition predicate, a positive delta, and the gap predicate. Finally it assumes ideal membership of the sine and the residual, and concludes the inequality.

One subtlety is that the name A in the Lean signature refers to the paper's A hat. Another is that the positive sine operator is represented by its own definition, rather than merely by the rectangular complementary block.

The theorem retains the full finite-interval and ordered half-infinite gap alternatives. In particular, the two ordered configurations allow both A naught and Lambda one to be unbounded.

---

At this point, ask yourself whether the result is really a theorem about two arbitrary nearby subspaces. It is not. The subspaces are tied to an operator, a residual, and a spectral separation. The gap tells us why small failure of invariance should imply small geometric error. Without that link, a trial subspace can be a poor approximation even if the perturbation appears small by itself.

---

### Section 3.1.4. Why the Sylvester estimate gives the angle bound — manuscript page 14

We now hear the short proof outline in the paper.

Set X equal to F one adjoint times E naught. This describes the projection of trial coordinates into the exact unwanted block. Since the exact subspaces form a complete orthogonal decomposition, S equals F one times X.

Because F one is an isometry, the corresponding ideal norms agree. The norms of X, S, and the positive sine of the angle operator are equal whenever defined.

Next, self-adjointness and the residual-domain hypotheses imply the Sylvester equation. Lambda one X minus X A naught equals F one adjoint R, on the domain of A naught.

Apply the gap estimate. Delta times the norm of X is at most the norm of F one adjoint R, and this is at most the norm of R.

Substitute the equality between the norm of X and the norm of sine theta naught. The theorem follows.

The paper concludes with a sharp equality example in two dimensions. Choose an ambient diagonal operator with eigenvalues zero and delta, let the trial operator be zero, and take a unit trial vector at angle theta from the exact zero-eigenvalue direction. Its complementary component has length sine theta, while the residual has length delta times sine theta. The two sides of the sine-theta inequality are equal.

This is a finite-dimensional illustration of sharpness. The theorem itself has the broader scope described above.

## Section 4. Formalized operator-theoretic foundations — manuscript pages 14 through 16

The paper now describes the mathematical library underlying the proofs. Rather than listing every helper theorem, it organizes the foundational results by the geometry of subspaces, operator ideals and majorization, Sylvester estimates, and scalar-field transfer.

### Section 4.1. Direct rotations and two-subspace geometry — manuscript page 15

Let P and Q be orthogonal projections onto two closed subspaces U and V. In the acute case, the norm of P minus Q is less than one.

Compressing Q to the range of P gives the positive cosine data for the angle operator. Its square root and complementary compression give the cosine and sine factors needed for direct rotation. Polar decomposition supplies the maps pairing the appropriate subspace directions.

The resulting direct rotation carries U onto V. In finite-dimensional principal-plane coordinates, it rotates each plane through the relevant principal angle and fixes any shared directions. In Hilbert space, the projection formula accomplishes the same construction without a discrete list of principal vectors.

The formalization proves existence and uniqueness in the acute case, a principal-square-root characterization, commutation with the angle operators, and reversal symmetry. Reversal symmetry means that swapping the source and target replaces the direct rotation by its adjoint.

For nonacute pairs, right-angle defects require separate existence criteria. When the angle operator is compact, the corresponding decomposition recovers a sequence of principal angles.

The double-angle results add another issue: knowing that sine of twice theta is small does not tell us whether theta is near zero or near ninety degrees. The branch-selection results from Section 8 of the original paper use spectral ordering and perturbation smallness to select the intended branch. Those claims are also included in the formalized development.

### Section 4.2. Approximation numbers and operator-ideal norms — manuscript page 15

The next set of foundations concerns singular values and symmetric norms.

In finite dimensions, a unitarily invariant norm is determined by a symmetric gauge of the singular values. Approximation numbers extend the required singular-value comparisons to bounded operators. For compact operators, they recover the familiar singular-value sequence.

The formalization develops symmetric norming functions and Ky Fan partial sums. These support majorization arguments: one can compare singular-value distributions and infer inequalities for whole classes of norms.

For direct rotation, this machinery proves a restricted-displacement minimality statement. It also proves the squared full-displacement comparison from Davis and Kahan's Proposition four point three.

But the singular values of a squared displacement operator are the squares of the singular values of the unsquared displacement. Changing the function of the singular values changes what an inequality means. The counterexample in the next section exposes the failure of a proposed inference from squared displacement to full trace-norm displacement.

The same operator-ideal machinery is used in the sine-theta proof. Both the sine operator and residual must belong to the supported ideal if their finite norm values are to be compared.

### Section 4.3. Sylvester estimates and unbounded operators — manuscript pages 15 and 16

The Sylvester map sends an operator X to B X minus X C, with B acting on the target side and C acting on the source side.

Under the specified spectral separation, delta times the norm of X is bounded by the norm of this Sylvester expression.

For the sine-theta theorem, B is Lambda one, C is A naught, and X is F one adjoint times E naught. For other theorems, different projection blocks are inserted into the same analytic pattern.

The unbounded case requires domain-carrying maps. A statement that B X minus X C equals the residual must specify which vectors lie in the domain of C and which images under X lie in the domain of B.

The formalization represents such operators as linear partial maps. Strong spectral cutoffs create bounded approximations. Convergence of approximation numbers then supports passing the estimates back to the unbounded setting.

The generalized sine and tangent theorems also require block-norm comparisons. One technique is reflection pinching. Conjugate a block operator by a reflection that is plus one on one coordinate subspace and minus one on the other. Average the original operator with its reflected version. This removes the off-diagonal blocks, and the operation contracts a unitarily invariant norm. Combined with direct-sum norm inequalities and Sylvester separation, this gives the generalized angle estimates.

### Section 4.4. Real and complex Hilbert spaces — manuscript page 16

Spectral constructions often work most naturally using complex functional calculus. But the original Davis–Kahan statements cover both real and complex Hilbert spaces.

The formalization develops the scalar-transfer results needed to establish the real statements using appropriate complexification arguments. That transfer must respect the operator domains and ideal-norm hypotheses, rather than merely changing the type of the scalar field in a finite-matrix calculation.

The section ends by identifying Mathlib as the main general foundation, with adapted Spectra work and Tau Ceti contributions as described in the historical chapter.

---

We have now covered the formalization paper's central technical result and its mathematical infrastructure. The next section changes the kind of question being asked. Instead of estimating the movement of spectral subspaces, we hold the two subspaces fixed and optimize over every allowable ambient transport map. That is where the false assertion in the original Davis–Kahan paper appears.

---
## Section 5. A counterexample to full-displacement optimality — manuscript pages 16 through 20

We have reached one of the central discoveries discussed in this paper: a counterexample to Davis and Kahan's Proposition four point four.

First, recall the distinction between two kinds of displacement. Suppose an orthogonal or unitary map W carries the source subspace U onto the target subspace V. The operator identity minus W measures how W moves the entire ambient space. If we first restrict to the source subspace by applying its projection P, we instead obtain restricted displacement.

The direct rotation is a canonical transporter obtained from the polar factor of Q P plus I minus Q times I minus P. But a canonical construction need not minimize every cost.

The published Proposition four point four claims that, for two real subspaces whose largest principal angle is no greater than sixty degrees, the direct rotation minimizes the norm of identity minus W among all allowed orthogonal transporters, for every unitarily invariant norm.

To refute a statement that claims optimality for every such norm, it is enough to find one norm and one admissible competitor that does better. The paper uses the trace norm, the sum of singular values.

### Section 5.1. The real four-dimensional counterexample — manuscript pages 16 through 18

Here is Theorem 2 in spoken form.

For every positive angle theta smaller than ninety degrees, there are two two-dimensional subspaces of real four-dimensional space, and an orthogonal transporter W from the first onto the second, such that both principal angles are theta. For those same subspaces, the canonical direct rotation has trace displacement equal to eight times sine of theta over two. The competitor has trace displacement equal to four times sine theta. The latter is strictly smaller.

This is an entire one-parameter family of counterexamples, not a failure at a specially selected large angle.

Let's follow the construction. The paper sets c equal to cosine theta and s equal to sine theta. It uses J for the standard real quarter-turn matrix, which rotates a two-dimensional vector through ninety degrees. It then defines C to be the two-dimensional rotation through twice theta. In terms of J, C is cosine of twice theta times the identity plus sine of twice theta times J.

The matrix H is a normalized four-by-four block mixing matrix: it has two-by-two identity blocks in the top row and a positive and a negative identity block in the bottom row, all scaled by one over the square root of two. It is orthogonal.

Now define W by conjugating the block-diagonal matrix with C in its first block and the identity in its second block by H. So we mix the two coordinate planes, rotate one of the resulting planes by twice theta, leave the other fixed, and transform back.

Because C and H are orthogonal, W is orthogonal.

Let U be the first coordinate plane in real four-dimensional space. Let V be the image of U under W. By factoring the first two columns of W, the paper constructs an orthonormal basis for V. The overlap between that basis and the original basis for U is cosine theta times the two-by-two identity. Therefore both singular values of the overlap are cosine theta, and both principal angles are theta.

This is the first thing we must verify. The competitor really transports the intended subspace pair with the intended principal angles.

The paper then calculates the projections P and Q onto U and V. From these it calculates the canonical intertwiner T, the same one used in the Sz.-Nagy–Kato construction. Its positive modulus is cosine theta times the four-by-four identity. Therefore the polar factor of T is exactly the direct rotation R displayed in the proof.

The direct rotation moves two real principal planes. Its four displacement singular values are all equal. Each one is two times sine of theta over two. There are four of them, so the trace norm is eight times sine of theta over two.

For W, only one of its invariant real two-planes is rotated, by twice theta; the other plane remains fixed. Its displacement singular values are two copies of two times sine theta, followed by two zeros. Adding them gives four times sine theta.

Why is this smaller? The double-angle identity says that sine theta equals two times sine of theta over two times cosine of theta over two. So four times sine theta equals eight times sine of theta over two, multiplied by cosine of theta over two. Since that cosine is strictly smaller than one for positive theta, the competitor wins.

The proof also gives Corollary 3. No strictly positive threshold on the largest principal angle can rescue the full trace-norm optimality claim. For any prescribed positive epsilon, choose theta small enough to lie below epsilon and no greater than the sixty-degree bound. The same construction works.

Now turn to Figure 2 on page eighteen. This is the picture to study while listening to the numerical example.

At theta equal to forty-five degrees, the left half shows the canonical direct rotation. It acts on two principal planes, rotating one through plus forty-five degrees and the other through minus forty-five degrees, with the sign depending on the chosen orientation of those planes. Both planes contribute nonzero displacement.

The right half shows W acting on a different pair of invariant planes. One is rotated through ninety degrees; the other is fixed. The figure is not claiming that W preserves the same principal-plane decomposition as R. That difference is essential.

The bar charts below show the four singular values of each displacement operator on the same vertical scale. For the direct rotation, each bar has height approximately zero point seven six five. There are four equal bars. Their sum is approximately three point zero six one.

For the competitor, the first two bars have height square root of two, approximately one point four one four, and the last two are zero. Their sum is approximately two point eight two eight.

Thus W has a larger maximum displacement singular value, but a smaller sum. The operator norm prefers the canonical direct rotation. The trace norm prefers W.

The figure also draws individual input vectors, their images, and the displacement arrows connecting them. These are representative vectors in the invariant planes, not additional assumptions needed for the proof.

The paper then establishes that W is not merely better than the direct rotation. It attains the global trace-norm minimum for this pair of subspaces. The trace norm of P minus Q is four times sine theta. For every orthogonal transporter, the trace norm of P minus Q is no larger than the trace norm of identity minus that transporter. Since the constructed W reaches exactly four times sine theta, no competitor can do better.

---

Notice the tradeoff. Direct rotation spreads modest motion across four singular directions. The alternative concentrates more motion into two directions and fixes the other two. The nuclear norm adds the costs linearly, so concentrating the displacement can reduce the total. The operator norm only sees the largest displacement, and therefore reaches the opposite conclusion. The geometric fact that both maps transport U onto V does not force their full displacement spectra to match.

---

### Section 5.2. Failure of the published proof — manuscript page 19

The next question is not just whether the old proposition is false, but where its argument fails.

The paper specializes the family to forty-five degrees and gives an explicit four-by-four real orthogonal matrix. Each entry is plus or minus one half. This is the concrete matrix displayed at the beginning of Section five point two.

The competitor's trace displacement is two times square root of two. The canonical direct rotation's trace displacement is four times the square root of two minus square root of two. Numerically these are approximately two point eight two eight and three point zero six one.

For the singular-value comparison, set K equal to identity minus W at this particular angle. Let Omega one and Omega two be the projections onto the two principal planes used in the construction.

The original paper's Equation four point three would require the Ky Fan four-norm of K to be at least the sum of the Ky Fan two-norm of K Omega one and the Ky Fan two-norm of K Omega two.

Recall that a Ky Fan j-norm is the sum of the j largest singular values. In the four-dimensional case, the Ky Fan four-norm of K is its entire trace norm.

The paper computes the left side as two times square root of two. Each restricted Ky Fan two-norm on the right is two. Adding them gives four.

Thus the published comparison would require two times square root of two to be at least four. It is not. The proposed inequality is false.

The failure comes from a subtle property of singular values. The domain principal planes are orthogonal, but K does not necessarily send them into orthogonal image spaces. Consequently, adding singular-value sums from the two restrictions can overcount what is available in the unrestricted full operator. Orthogonal domain blocks do not by themselves justify the claimed global lower bound.

This identifies the mathematical gap in the published proof.

### Section 5.3. A Q-norm repair from squared-displacement optimality — manuscript page 19

A failed statement can sometimes be repaired by identifying the precise hypotheses under which its proof mechanism works.

The paper introduces Q-norms. A unitarily invariant norm N is a Q-norm if there exists another unitarily invariant norm M such that the square of N applied to Z equals M applied to Z adjoint times Z, for every Z.

The Frobenius norm is an example. Squaring the Frobenius norm gives the sum of squared singular values. That is the trace norm of the positive matrix Z adjoint times Z. Therefore the Frobenius norm fits the definition with M equal to the trace norm.

The trace norm itself does not have the needed Q-norm property in this counterexample setting.

Now recall Davis and Kahan's valid Proposition four point three. It gives an optimality comparison for squared full displacement. The direct rotation minimizes M applied to the positive squared-displacement operator among the competing transporters.

If N is a Q-norm, that statement is exactly a comparison of the squares of the N displacement costs. Both costs are nonnegative. Taking square roots preserves their order.

The conclusion is Proposition 4 of the present paper. For an acute pair of finite-dimensional real or complex subspaces, and for any Q-norm, the direct rotation has no greater full displacement cost than any transporting orthogonal or unitary map. No sixty-degree restriction is needed.

This conclusion follows directly from the squared-displacement result. It does not restore the false claim for the trace norm.

### Section 5.4. Historical context — manuscript page 20

The paper returns briefly to the history of the counterexample.

Davis and Kahan already gave a complex two-dimensional example in which changing a phase reduces trace displacement. The real four-dimensional family is a realification of that complex construction.

When we treat a complex two-dimensional vector space as real, it becomes four-dimensional. Complex multiplication by the imaginary unit becomes a real ninety-degree rotation on each suitable real coordinate plane. The same complex phase modification can therefore be represented as an ordinary real orthogonal transformation, but it now couples two real principal planes.

Realification doubles the singular-value multiplicities. This is why the complex mechanism survives in real four-dimensional space. Merely restricting the field to real numbers and requiring the principal angles to be at most sixty degrees does not eliminate it.

Bolotnikov, Li, and Rodman studied the same general minimum-distortion question in 2001, including Q-norm optimality and counterexamples for Schatten exponents below two. Qiu, Zhang, and Li later repeated the sixty-degree assertion, while Zhang and Qiu discussed general trace-norm nonminimality.

The contribution of the present section is the explicit real family contradicting the printed small-angle statement, the precise failure of its singular-value inequality, and the corrected Q-norm conclusion.

---

The historical point is precise. The complex phase mechanism was already known. The formalization made it possible to examine the real statement, test the proposed comparison, and establish a parameterized contradiction with the exact canonical rotation. The next section investigates the unrestricted real optimization problem rather than stopping at a counterexample.

---

## Section 6. A follow-on theorem enabled by the formal development — manuscript pages 20 through 22

The section now asks a clean optimization question. Suppose two equal-dimensional real subspaces K and L are given. Among all orthogonal transformations of the ambient real space that carry K onto L, which one minimizes the trace norm of identity minus the transformation?

There are infinitely many candidate orthogonal transformations. They can move the orthogonal complements and mix coordinates in ways that do not change the image of the source subspace. The theorem reduces that continuous optimization problem to weighted matching on the principal angles.

Let the positive principal angles be theta one through theta m, counted with multiplicity. These can include right angles. We create one label for every positive angle.

A matching is a set of disjoint unordered pairs of labels. Each angle can be paired with at most one other angle. Angles not selected in any pair are called unmatched.

The paper defines two costs, shown in Equation twenty-six.

For an unmatched angle theta, the singleton cost is the smaller of four times sine theta over two and two. The first option is the trace-norm cost of independently rotating its real principal plane through theta. The second option is the cost of using a reflection to transport the same source line to the target. The singleton cost chooses the cheaper of those two possibilities.

For a pair of angles theta and psi, the paired cost is four times sine of half their sum. That cost is achieved by a four-dimensional orthogonal transporter that couples the two principal planes.

The central theorem, Theorem 5, says the following. Take every matching on the positive principal-angle labels. For each paired label, pay the paired cost. For each unmatched label, pay the singleton cost. Add these costs. Find the matching with the smallest total.

That minimum is exactly the minimum trace norm of identity minus W over every ambient orthogonal transporter W carrying K onto L. Both the continuous minimum and the discrete matching minimum are attained.

The theorem includes repeated angles, right angles, and common ambient directions. It does not impose a determinant restriction or require the competing transporter to preserve the canonical principal-plane decomposition.

---

This is the point where the result may look familiar to a computer scientist. Once the continuous problem has been reduced to independent singleton and paired costs, the remaining optimization is matching in a general undirected weighted graph, with unmatched vertices allowed. It is not inherently a bipartite linear assignment problem. The difficult mathematical part is proving that an arbitrary orthogonal transformation cannot beat the best such block matching.

---

The paper reformulates the matching problem using savings. Start with the total cost of leaving every angle unmatched. For a pair of labels i and j, calculate the savings from pairing them: the sum of their two singleton costs minus their paired cost. If this number is positive, pairing them helps. If it is negative, pairing them makes the solution more expensive.

A matching's total cost is the all-singleton cost minus the sum of the savings on its selected edges. Therefore minimizing cost is equivalent to maximizing total savings over disjoint pairs.

Turn to Figure 3 on page twenty-one. It uses three positive principal angles: thirty degrees, forty-five degrees, and seventy-five degrees.

Their singleton costs, rounded to four decimal places, are approximately one point zero three five three, one point five three zero seven, and two point zero zero zero zero. With no pairs, the total is about four point five six six zero.

There are three possible single edges to consider, since the matching can contain at most one edge when there are only three vertices.

Pair thirty and forty-five degrees, leaving seventy-five degrees unmatched. The total cost is approximately four point four three five zero, which is the best choice.

Pair thirty and seventy-five degrees, leaving forty-five degrees unmatched. The cost is approximately four point seven zero four one, worse than even leaving everything unmatched.

Pair forty-five and seventy-five degrees, leaving thirty degrees unmatched. The cost is approximately four point four nine nine four, which improves on no pairing but is not the best.

The figure shows these candidate matchings, their edge savings, and their total costs. The winning solution uses one coupled four-dimensional block for the thirty- and forty-five-degree planes, and a singleton reflection block for the seventy-five-degree plane.

The cost of that solution is four times sine of thirty-seven point five degrees, plus two, approximately four point four three five.

### Proof outline of the matching theorem — manuscript pages 21 and 22

The theorem is much stronger than showing that every matching can be implemented by an orthogonal transformation. That construction gives candidate upper bounds. The proof must also show that no more complicated full-space orthogonal map has a lower cost.

The paper outlines a proof that begins with strict Schatten exponents between one and two, before taking a limit to the trace-norm endpoint at one.

For a fixed exponent p strictly between one and two, define the displacement power cost by taking the singular values of identity minus W, raising each to the power p, and summing.

The set of orthogonal maps satisfying the transport constraint is nonempty and compact in finite dimensions. Therefore a global minimizer exists.

The proof then considers small feasible variations of a minimizer. These are curves of the form W multiplied by the exponential of a small skew-symmetric matrix. The derivative of the cost is represented by a skew-symmetric spectral gradient G. Because variations that commute with the source projection preserve feasibility, stationarity imposes an anticommutation condition involving G and the reflection J, where J equals two times the source projection minus the identity.

This condition is not just an algebraic curiosity. On each positive spectral level of negative G squared, the normalized gradient squares to minus the identity. It therefore acts as multiplication by the imaginary unit: a complex structure inside a real vector space. The reflection J acts there like complex conjugation.

The derivative of the scalar phase penalty has at most two roots at each such positive level. Consequently, within the resulting complex coordinates, the minimizing transporter has at most two relevant spectral phases. A real orthogonal block decomposition then organizes the candidate into blocks of real dimension two or four, together with fixed common directions.

The zero-gradient part is handled using reflection structure and the two-projection decomposition. A one-dimensional block with eigenvalue minus one can be replaced by a plus-one block without changing the transported subspace, so such a block cannot appear in a minimum when it would impose avoidable cost.

The next step is the global one. Replacing the transporter on one common invariant block preserves feasibility. Therefore a global minimizer must itself be optimal on each block. Every two-dimensional block contributes a singleton angle cost. Every four-dimensional block contributes either two independent singleton costs or a paired angle cost. Since principal-angle multisets and trace-like displacement costs add across these blocks, the whole minimizer induces a matching.

Conversely, every matching can be realized by taking an orthogonal direct sum of the corresponding two- and four-dimensional transport blocks.

So the unrestricted minimum agrees with the matching minimum for every strict Schatten exponent between one and two, using the appropriate exponent-dependent block costs.

Finally, the proof lets p decrease toward one. In a fixed finite dimension, the powered Schatten objective converges uniformly to the trace norm over the compact feasible set. The scalar block costs also converge, and there are only finitely many matchings. This allows passage to the endpoint. Compactness gives an actual attaining transporter.

That completes the proof outline for the nuclear, or trace-norm, matching formula.

The paper returns once more to the two equal thirty-degree angles from the original counterexample. The canonical direct rotation costs eight times sine of fifteen degrees, which is greater than two. Pairing the two principal angles costs four times sine of thirty degrees, which equals two. The matching theorem shows that this is globally optimal, not merely an improvement on direct rotation.

The section closes by attributing the earlier complex phase construction to Davis and Kahan and the general minimum-distortion formulation to Bolotnikov, Li, and Rodman. The exact real matching formula builds on that geometric and optimization setting.

---

The conceptual result of Section 6 is a reduction from continuous geometry to combinatorics. First, the principal angles encode the subspace pair. Then the analysis of unrestricted minimizers shows that two- and four-dimensional blocks suffice. Finally, choosing the cheapest arrangement of those blocks becomes a matching problem. Without the global block-reduction proof, the matching formula would only describe a family of candidate solutions, not the true optimum.

---

## Section 7. Discussion — manuscript page 22

The discussion returns to the paper's main objective: formalizing Davis–Kahan theory at the scope of the original source.

That scope includes real and complex Hilbert spaces, unbounded self-adjoint operators, and operator-ideal norms. Unbounded statements require explicit domain conditions and bounded residuals. Operator-ideal inequalities require the relevant norms to be finite. These details determine which mathematical applications the theorem genuinely covers.

The Proposition four point four correction separates two previously conflated extremal questions. Squared full displacement has a valid minimality theorem, and Q-norms can inherit its optimality conclusion. But unsquared full trace-norm displacement behaves differently. Even arbitrarily small positive principal angles admit real counterexamples in four dimensions.

The reason is visible in the displacement singular values. The direct rotation has four equal nonzero values. The competitor has two larger nonzero values and two zeros. Their sums favor the competitor, while their maximum values favor direct rotation.

The matching theorem gives an exact unrestricted solution to the resulting real trace-norm optimization problem. Its proof uses the same angle geometry, orthogonal decompositions, and singular-value norm ideas that were developed during the Davis–Kahan formalization, along with additional optimization arguments.

## Section 8. Conclusion — manuscript pages 22 and 23

The paper closes with three linked achievements.

First, twenty-eight of the twenty-nine selected Davis–Kahan results have been formalized. The treatment of the sine-theta theorem includes unbounded self-adjoint operators and symmetric operator-ideal norms with their stated domain and finiteness conditions.

Second, the remaining printed assertion, Proposition four point four, is refuted by an explicit real four-dimensional construction. The analysis identifies the invalid singular-value comparison and proves a valid Q-norm consequence of the earlier squared-displacement result.

Third, the project develops the operator-theoretic foundations required for the original formalization: principal angles, direct rotations, Borel spectral calculus, approximation numbers, symmetric ideals, and Sylvester separation. Some of these developments were adapted into Tau Ceti. Building on the same foundations, the authors establish a weighted-matching formula for real trace-norm transport.

The formalization is the primary accomplishment of this paper. The correction and matching theorem demonstrate two ways in which the developed mathematics led to further results.

The manuscript then provides an AI-assistance disclosure, repository availability information, acknowledgments, and a bibliography. We will not read those administrative details or the individual bibliography entries aloud.

---

Before moving to the appendices, notice how the paper's two mathematical tracks fit together. The perturbation theory uses the residual and spectral gap to bound the angle between subspaces. The transport theory assumes the subspaces are already given and asks how to move one onto the other with minimum ambient cost. They share the language of projections, principal angles, and operator norms. Their conclusions answer different questions.

---

## Appendix A. Symbols and conventions — manuscript pages 26 and 27

Appendix A is a reference table rather than a continuous argument. We will use it to review the important objects, without reading every row literally.

The reference operator is A. The perturbed ambient operator is A hat, obtained by adding H. The trial embedding is E naught, and the trial operator is A naught. The exact target embedding is F naught, while F one embeds the unwanted complementary spectral subspace. Lambda one describes the self-adjoint operator acting on that complement.

The target projection P in the sine-theta theorem is F naught times its adjoint. The positive sine operator acts on trial coordinates. The rectangular complementary block S is I minus P followed by E naught. Its modulus is the sine operator.

X is F one adjoint times E naught. It represents the unwanted part of the trial space in exact complementary coordinates. R is the bounded trial residual. Delta is the positive spectral separation.

In the transport sections, the letters U and V denote source and target subspaces. Their projections are P and Q. The direct rotation and an arbitrary competitor are written R and W. These local uses of R and P are different from those in the residual discussion.

The positive modulus of an operator records its singular-value magnitudes. The operator norm is the largest singular value. The Frobenius norm is the Euclidean norm of the singular-value vector. The trace norm sums the singular values. A Ky Fan norm sums the largest specified number of singular values. A Q-norm is characterized by the squared-norm identity used in Section 5.

The matching notation uses a collection of disjoint pairs of positive principal-angle labels, together with singleton and pair costs. Its edge savings compare the cost of two singletons with the cost of pairing them.

In the colored manuscript, colors help distinguish trial data, exact data, unwanted components, angles, residuals, and spectral separation. They are visual aids, not part of the mathematical definitions.

## Appendix B. Reading the Lean signatures — manuscript page 27

Appendix B gives a short guide to interpreting the Lean declaration shown earlier.

A Lean theorem begins with a name, followed by its parameters and hypotheses, then its conclusion and proof. Parameters specify the mathematical objects. Hypotheses assert facts such as self-adjointness, isometry, domain inclusion, and spectral separation. Bundled predicates collect several related assumptions into one named object.

The declaration uses Lean's real-or-complex scalar abstraction, called R C Like, to represent either field. Continuous linear maps are the bounded linear maps used for coordinate embeddings and residuals. Linear partial maps carry a linear domain, making them suitable for representing possibly unbounded operators.

The membership notation for the norm family says the operator has finite ideal norm. The real-valued gauge notation specifies the resulting norm value. The word real in that gauge's name describes the output value, not the scalar field of the Hilbert space.

The appendix is there to help a reader compare the paper's mathematical hypotheses with the actual formal theorem statement.

## Appendix C. Formalized Davis–Kahan results — manuscript page 28

The last appendix inventories the twenty-nine original source targets. Rather than reading each internal identifier, we can group the statements by the part of the 1970 paper they come from.

The four headline Section 2 results are the sine-theta, tangent-theta, sine-two-theta, and tangent-two-theta theorems.

The Section 3 results concern direct rotation: acute existence and uniqueness, nonacute existence conditions, square-root characterizations, classification of pairs of subspaces, the compact angle-eigenvalue classification, commutation with angle operators, and reversal symmetry.

The Section 4 results concern extremal properties of direct rotation. They include restricted-displacement optimality, basis-angle square sums, squared-displacement optimality, and the full-displacement claim of Proposition four point four. That last claim is the refuted one.

The Section 5 results cover Sylvester estimates, including a Banach-space lower bound, a semibounded self-adjoint version, and strong-cutoff convergence of singular values.

The Section 6 results cover generalized perturbation estimates and their supporting block-norm tools. They include direct-sum comparisons, reflection pinching, generalized sine and tangent theorems, a pairwise-gap square-norm result, and a finite-rank leakage estimate.

Finally, the Section 8 results concern spectral branch selection and spectral repulsion: deciding which side of a double-angle ambiguity corresponds to the desired spectral subspace, and when small perturbations force the acute branch.

One original source result may require multiple Lean declarations. Conversely, one general reusable lemma may support several source results. The inventory uses the original source statements as its units of comparison, not the number of files or theorem declarations in the implementation.

That completes our spoken reading of the paper.

---

A final way to remember the overall argument is as a sequence of questions. First, how do we measure the separation between subspaces? Principal angles and projections answer that. Second, how does a trial subspace fail to be invariant? The residual answers that. Third, how does spectral separation control that failure? A Sylvester estimate answers that, leading to the sine-theta theorem. Fourth, which unitary should carry one subspace onto another, and what does it mean for that motion to be minimal? Direct rotation and displacement norms raise that question. The counterexample shows that canonical motion is not always trace-norm optimal. The matching theorem then gives an exact optimization rule for real finite-dimensional transport.

The formalization connects those ingredients in a reusable mathematical development. The paper is both an account of that formalization and a study of what became possible when its foundations were available.

---
