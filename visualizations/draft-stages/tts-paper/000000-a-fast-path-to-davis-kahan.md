# 000000 — A fast path to Davis–Kahan

**Track:** G3 audio paper track. **Assumed background:** eigenvalues, inner products, basic singular values, and familiarity with limits and integrals. **Format:** standalone spoken lecture with display-only mathematical companion.

<!-- BEGIN SPOKEN LECTURE -->

# A fast path to Davis–Kahan

An eigenvector can change when a matrix changes. The natural question is how much it changes, and what information lets us predict that change before computing the new eigenvector. The Davis–Kahan theory answers this question in terms of spectral separation, residuals, and angles between subspaces. It also tells us which answers remain valid when one eigenvector is replaced by an entire cluster of eigenvectors, or when matrices are replaced by operators on infinite-dimensional spaces.

Start with a real symmetric two-by-two matrix. Its first diagonal entry is zero, its second is four, and its off-diagonal entries vanish. The coordinate axes are eigenvectors. The two eigenvalues are separated by four. Now put the same small number, call it t, into both off-diagonal entries. The new symmetric matrix has the same diagonal entries but couples its two coordinate directions. Its eigenvectors rotate.

How much do they rotate? If theta denotes the acute angle between the original first coordinate axis and the new eigenvector associated with the lower eigenvalue, elementary diagonalization gives tangent of twice theta equal to t divided by two. When t is small, theta is approximately t divided by four. The change is proportional to the perturbation divided by the original eigenvalue gap. If the gap were much smaller, the same perturbation could produce a much larger rotation.

This example contains most of the course's organizing ideas. We care about the angle, not about which coordinates happen to describe the eigenvector. We must measure the perturbation in a suitable norm. And we need to know that the spectral component we are following is separated from competing modes. An eigenvalue gap is not an optional decoration on the estimate. Without a meaningful separation, even tiny perturbations can exchange the directions of nearby eigenvectors.

The two-by-two picture becomes more interesting with a repeated eigenvalue. Inside a repeated eigenspace, an orthonormal eigenbasis can rotate arbitrarily without changing the underlying invariant subspace at all. Consequently the stable object is often the entire eigenspace or spectral subspace, represented by its orthogonal projection. Davis–Kahan estimates compare two such subspaces instead of insisting that their bases line up column by column.

For a pair of subspaces, principal angles generalize the ordinary angle between two lines. Their cosines are the singular values of the overlap between orthonormal bases. Their sines measure how much one subspace escapes the other. If the spaces have unequal dimensions, we must keep track of the direction of this comparison: projecting a larger space into a smaller one carries different information from the reverse projection. When the dimensions agree, the familiar symmetric picture becomes available.

A central proof technique begins with an approximate invariant subspace. Think of a numerical method that has produced a trial orthonormal frame. The frame maps a small coordinate space into the ambient Hilbert space. We also have a proposed small operator describing how the matrix should act within the trial space. Apply the full operator to the frame, subtract the frame followed by the proposed small operator, and call the difference the residual. A vanishing residual means exact invariance. A small residual indicates nearly invariant behavior, but the direction of the error still depends on the spectral gap.

To see the missing link, decompose the ambient space into the exact target subspace and its orthogonal complement. Compress the residual onto that complement. The resulting equation has the form A times X minus X times B equals C. This is the Sylvester equation. Here X measures overlap with the wrong spectral modes, while C is the compressed residual. If the spectra of A and B are separated in the right way, the equation constrains X by C divided by the gap. Identifying the singular values of X with the directed sines of the principal angles gives the sine-theta theorem.

The tangent-theta theorem uses a different geometric representative. When the subspace pair is in the appropriate graph position, one subspace can be written as the graph of a map over the other. The singular values of that graph map are the tangents of the principal angles. Its operator equation leads to a tangent bound, with the graph condition and the relevant spectral separation appearing explicitly among the hypotheses.

Why are there also sine-of-twice-theta and tangent-of-twice-theta theorems? Certain perturbations are off-diagonal relative to a preferred decomposition. They exchange the two blocks rather than perturbing each diagonal block independently. A block reflection changes the sign of this off-diagonal perturbation. Comparing the two reflected configurations produces doubled-angle expressions. These estimates are powerful, but the numerical size of a doubled-angle sine is not enough by itself to tell us whether the original angle is small. A branch or selection argument must identify which spectral subspace is being followed.

The four angle-theorem families are therefore related without being interchangeable. Their unknowns have different geometric meanings, and their gap hypotheses need not coincide. The operator norm and the Hilbert–Schmidt norm can behave differently under spectral configurations that look similar on a line. For a unitarily invariant norm, we must also know which majorization or operator-ideal argument carries the estimate. A phrase like positive spectral distance does not determine every one of these constants.

We will also need infinite-dimensional spectral theory, though we can keep its role sharply focused. For a bounded self-adjoint operator, spectral projections select measurable parts of the spectrum. For an unbounded self-adjoint operator, domains matter as well: one cannot multiply arbitrary vectors by an unbounded operator and expect the expressions to make sense. The operator-theoretic Sylvester argument has to respect these domains. Basic measure theory and Hilbert-space notions are enough to motivate this extension; the detailed functional calculus is available when the proof needs it.

The final topic is not an angle bound but a question of optimal movement. Given two subspaces, which orthogonal or unitary operator taking one to the other moves the ambient space the least? The canonical direct rotation is a natural candidate. Its displacement has explicit singular values determined by the principal angles. But a norm of displacement and a norm of squared displacement respond differently to how singular values are distributed. In particular, the original paper's broad Proposition four point four is false for an unsquared trace-norm objective. A concrete four-dimensional real orthogonal matrix provides a counterexample even when both principal angles are acute.

That failure leads to a constructive positive result. For a real finite-dimensional transport problem with Schatten exponent strictly between one and two, optimal transports can be classified through a finite matching problem. Positive principal-angle labels appear as singletons or disjoint pairs. The singletons and pairs carry costs obtained by optimizing their corresponding low-dimensional blocks. A global lower bound and an attainment construction show that the matching minimum gives the desired optimum. Its assumptions are part of the result, rather than an invitation to extrapolate to every norm or every dimension.

The mathematics ahead can be followed with a compact set of recurring objects: a self-adjoint operator, its spectral subspaces, the projections onto those subspaces, the singular values of overlap maps, a residual, and a spectral gap. We will use a few standard tools repeatedly—block matrices, the Sylvester equation, polar decomposition, and majorization—but each proof has a concrete job for them.

Return to the first two-by-two example. The perturbation t creates off-diagonal coupling, the original gap is four, and the spectral direction rotates by an angle controlled by their ratio. Davis–Kahan theory explains exactly how this observation survives in far more general settings, and it shows the additional hypotheses that those settings require. The objective is a quantitative understanding of when an invariant subspace is stable and when a proposed rotation is optimal.

<!-- END SPOKEN LECTURE -->

---

## Mathematical companion (display only)

For \(A=\left(\begin{smallmatrix}0&0\\0&4\end{smallmatrix}\right)\) and \(A_t=\left(\begin{smallmatrix}0&t\\t&4\end{smallmatrix}\right)\), the lower eigenspace rotates by an angle \(\theta\in[0,\pi/4)\) satisfying \(\tan(2\theta)=t/2\) when \(t\ge 0\). For \(t<0\), the unsigned principal angle satisfies \(\tan(2\theta)=|t|/2\). The first-order magnitude is \(\theta=|t|/4+O(t^3)\). The single-angle residual identity, graph tangent construction, and doubled-angle block reflection are developed in G2 lectures 107–120.

The six terminal G3 results use the theorem statements and original-source correspondence of G2 lectures 110000, 112000, 116000, 117000, 134000, and 145000.
