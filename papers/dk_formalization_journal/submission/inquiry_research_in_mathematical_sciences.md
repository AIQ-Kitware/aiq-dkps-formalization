# Presubmission inquiry: Research in the Mathematical Sciences

Draft for coauthor approval; not sent.

Route through the editorial contact requested via
https://link.springer.com/journal/40687/contact-the-journal.
The journal's contact page does not list a dedicated presubmission-inquiry
email address. Do not submit a manuscript merely to request a scope assessment.

**Subject:** Presubmission scope inquiry: exact spectral subspace transport and Davis--Kahan theory

Dear Editors,

My colleagues and I are preparing *Formalizing Davis--Kahan Perturbation
Theory and Exact Spectral Subspace Transport*. We would appreciate your
assessment of whether its results in operator theory and matrix optimization,
together with their formal verification, would suit *Research in the
Mathematical Sciences*.

The central problem is to minimize $\|I-W\|_{S_p}$ over all ambient orthogonal
or unitary maps $W$ taking one prescribed subspace onto another. For arbitrary
equal-rank subspaces of finite-dimensional **complex** Hilbert spaces and
$1<p<2$, we prove exact principal-angle formulas, sharp angle-dependent
transitions in the optimal transport, a classification of all global
minimizers, and that every constrained local minimum is global. Over the
**reals**, for $1\le p<2$, the unrestricted optimum is given by an exact
weighted-matching problem. At the nuclear endpoint $p=1$, the complex
minimum is $2\sum_j\sin\theta_j$; the real minimum equals it exactly when
each principal angle strictly between zero and $\pi/2$ has even multiplicity.
We also establish a sharp direct-rotation approximation bound for all
unitarily invariant norms, nearest subspace-preserving unitary results,
and exact optimization results for a smooth spectral penalty.

This work grew out of a Lean 4 formalization of Davis and Kahan's 1970
paper. Of 29 reviewed result-level statements, 28 are proved at their
reviewed source scope, including the unbounded self-adjoint setting;
the printed Proposition 4.4 is refuted by a real four-dimensional
counterexample at arbitrarily small positive principal angles. We identify
the error in its proof and distinguish our results from the earlier known
phase-based nonminimality examples and norm-minimization literature.

The finite-dimensional results described above are machine-checked. We are
currently pursuing infinite-dimensional extensions in Schatten operator
ideals; these are ongoing, not asserted as established. Extensive AI
assistance in the proof development and manuscript preparation will be
disclosed. The draft and proof artifact are available at
https://github.com/AIQ-Kitware/aiq-dkps-formalization.

Would this manuscript be of interest to the journal? We would be happy to
send the current draft for a preliminary scope assessment.

Best regards,

Jonathan Crall  
Kitware, Inc.  
jon.crall@kitware.com
