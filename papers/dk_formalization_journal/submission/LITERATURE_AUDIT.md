# Proposition 4.4: bounded literature claims

Date: 20 October 2026. This is a focused source comparison, not an exhaustive
priority search. DOI references and source locations are provided so another
reader can repeat the comparison.

## 1. Davis and Kahan (1970)

C. Davis and W. M. Kahan, The Rotation of Eigenvectors by a Perturbation. III,
SIAM Journal on Numerical Analysis 7(1), 1--46.
https://doi.org/10.1137/0707001

Proposition 4.4's real short-angle condition is largest principal angle at most
pi/3; its conclusion quantifies over unitarily invariant full-displacement
norms. The existing source-facing formalization and fixed-angle counterexample
are the basis for the new family. The failed inequality is source equation
(4.3), not Proposition 4.3. Proposition 4.3's squared-displacement statement
remains valid and yields the Q-norm consequence.

The new conventional proof constructs W = H diag(C(2 theta), I) H^T, computes
the target projection, proves the canonical intertwiner is cos(theta) R,
and obtains the two singular-value lists. This directly addresses the real
short-angle hypotheses. It does not dispute the sine-theta theorems.

## 2. Bolotnikov, Li, and Rodman (2001)

V. Bolotnikov, C.-K. Li, and L. Rodman, Minimal distortion problems for classes
of unitary matrices, Electronic Journal of Linear Algebra 8, 26--46.
https://doi.org/10.13001/1081-3810.1058
Primary PDF: https://journals.uwyo.edu/index.php/ela/article/download/117/117/117

Theorem 3.1 (printed p. 33) develops Q-norm minimization in a unitary-completion
problem. Lemma 3.3 (printed p. 36) analyzes a 2-by-2 example with complex unit
scalars and Schatten p-norms for 1 <= p < 2. The article cites Davis--Kahan
Section 4. These are direct antecedents for norm-class limitations and the
Q-norm repair. The particular right-angle/complex-scalar example does not
itself instantiate the real pi/3 condition in Proposition 4.4.

The primary PDF's extracted text was inspected. The web PDF screenshot service
failed on repeated requests, so this revision does not claim a successful
visual audit of those pages. The mathematical discussion uses the readable
primary text and source citations, not an uninspected figure.

## 3. Qiu, Zhang, and Li (2005; online 2006)

L. Qiu, Y. Zhang, and C.-K. Li, Unitarily invariant metrics on the Grassmann
space, SIAM Journal on Matrix Analysis and Applications 27(2), 507--531.
https://doi.org/10.1137/040607605
Author-uploaded article text:
https://www.researchgate.net/publication/220656718_Unitarily_Invariant_Metrics_on_the_Grassmann_Space
Author's publication list: https://myweb.cuhk.edu.cn/qiuli/Home/AcademicPublications

Section 5 lists three direct-rotation extremal properties attributed to Davis
and Kahan. Item 3 repeats full-displacement minimality for every unitarily
invariant norm under theta_1 <= pi/3. The new real family contradicts that
particular item. This is evidence that the assertion was repeated; it is not
a claim that the paper's main Grassmann-metric theorems fail. The cited
bibliographic year is 2005, with the online date recorded separately.

## 4. Zhang and Qiu (2010): checked direct-rotation norm comparison

Y. Zhang and L. Qiu, From subadditive inequalities of singular values to triangle
inequalities of canonical angles, SIAM Journal on Matrix Analysis and
Applications 31(4), 1606--1620.
https://doi.org/10.1137/09074841X

The published article was inspected directly (Section 4, printed p. 1615; PDF
page 10). The authors state that direct rotations minimize Frobenius-norm
displacement among unitary maps between two subspaces. They note explicitly
that trace-norm displacement is not generally minimized by direct rotations;
for spectral-norm displacement, additional minimizers may exist. The passage
attributes the underlying direct-rotation theory to Davis and Kahan [5],
but does not identify Proposition 4.4 as false or examine the specific real
pi/3 angle restriction. The passage establishes that the general trace-norm
limitation was known by 2010; it does not establish priority for the
short-angle refutation.

## Claims the manuscript makes

- A real 4-dimensional example refutes the particular printed Proposition 4.4.
- The parameterized construction fails for every 0 < theta < pi/2 and hence
  below every positive proposed angle threshold.
- The explicit singular-value calculation diagnoses why full-displacement
  trace norm differs from squared-displacement majorization.
- The Q-norm conclusion follows from established squared-displacement theory.
- The 2005 Section 5 item repeats the assertion contradicted by the family.

It does not claim first discovery of general trace-norm failure, a new Q-norm
principle, a global optimizer for the constructed trace-norm problem, failure
for every Schatten exponent below two at arbitrarily small angles, or an
exhaustive absence of earlier explicit corrections.
