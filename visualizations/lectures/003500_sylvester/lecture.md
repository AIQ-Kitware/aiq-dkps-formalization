# Sylvester equations and spectral separation

See [operator lecture provenance](../../dkvis/learning/operators/README.md) for accepted source modules and scope.
Numerical reference: https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.solve_sylvester.html

## SyTitle: Sylvester equations and spectral separation

Why: Turn residual equations into quantitative error bounds.
Recall: Know operator norms and matrix exponentials.

Sylvester equations and spectral separation.

## SyQuestion: Why a residual needs an inverse bound

Why: Relate the matrix equation to scalar division.
Recall: A and B are given operators; X is the unknown map.

A small residual alone does not certify a small error. Even in the scalar equation a minus b times x equals r, a small r can hide a large x when a and b nearly coincide. The Sylvester equation, A X minus X B equals R, is the operator version. It has appeared since nineteenth-century matrix theory, and Rosenblum's operator work connects spectral separation to its inversion. We will first solve diagonal examples, then explain why an ordered spectral gap gives an operator-norm estimate. This mechanism is one ingredient behind residual-based angle bounds.

## SyEntries: Solve in eigenbases

Why: See precisely where small denominators enter.
Recall: Assume A and B are diagonal in orthonormal coordinates.

The i j entry of A X minus X B is a i minus b j times x i j. If those two eigenvalues differ, divide the corresponding residual entry by their difference. This solves the equation entry by entry. For self-adjoint matrices, orthonormal eigenbases reduce the general equation to this form. But do not jump from this formula to an operator-norm bound with constant one. Entrywise division is an operation on matrices, and its operator-norm effect needs an argument. The next slide supplies that argument for an ordered gap.

## SyGap: Why the ordered gap gives constant one

Why: Use exponential decay to control every solution.
Recall: Bounded self-adjoint A and B lie on opposite sides of an ordered gap.

Assume A is at least c plus delta times the identity in quadratic forms, B is at most c times the identity, and delta is positive. Start with any solution X and define Y of t as exponential minus t A, times X, times exponential t B. Differentiate the product. The Sylvester equation gives Y prime equal to minus exponential minus t A, times R, times exponential t B. The spectral bounds give exponential decay of Y at rate delta, so Y tends to zero. This is where the ordered gap enters.
<!-- beat -->
Integrate the derivative from zero to infinity. Since Y starts at X and ends at zero, X equals the integral of the exponentially weighted residual. Take norms inside the integral. The product of the two exponential norm bounds is at most exponential minus delta t. Integrating that scalar decay gives one divided by delta. Thus norm X is at most norm R divided by delta. We started with an arbitrary solution, so this controls every solution. Applying the same bound to a zero residual also proves uniqueness. Convergence of this integral can separately construct a solution.

## SyExample: divide by the cross-gaps

Why: Check the formula and the hypotheses on concrete matrices.
Recall: The smallest ordered cross-gap here is two.

Take A diagonal with three and four, and B diagonal with zero and one. Their cross-differences are three, two, four, and three. Divide the four residual entries by those four numbers to obtain the displayed solution. Substituting verifies the equation. Because every A eigenvalue is at least three and every B eigenvalue is at most one, the ordered gap is two. Our theorem says twice the operator norm of this solution is at most the operator norm of the residual. The scalar calculation produces this example; the exponential argument justifies the uniform norm guarantee.

## SySummary: Which separation did we actually use?

Why: Prevent a matrix example from silently changing theorem scope.
Recall: An ordered form gap is stronger than pairwise noncoincidence.

We learned that the Sylvester map is linear in X. Different spectral configurations and different norms lead to different inverse bounds. The constant-one operator-norm estimate proved here uses an ordered quadratic-form gap. Do not replace that hypothesis by arbitrary noncoincident spectra. Accepted Tau Ceti has bounded-operator results and separate domain-aware partial-map results. The latter retain domain hypotheses for unbounded operators. Their accepted DKPS adaptation and the independently implemented bounded theory have distinct provenance in the census. This finite example is not a proof of all those unbounded claims.

## SyComputation: Solve without building a huge Kronecker matrix

Why: Use structure in the numerical linear equation.
Recall: Our convention has a minus sign before X B.

For dense matrices, Bartels–Stewart methods use Schur decompositions, solve the resulting triangular matrix equations, then transform back. This avoids explicitly forming the much larger Kronecker system. SciPy's solve_sylvester uses the convention A X plus X B equals Q. To solve our equation, pass minus B as its second argument. Afterwards measure A X minus X B minus R. A small computed residual becomes a solution-error estimate only after a valid inverse bound is available, just as in the motivation.

## SyFacts: The definition and the gap estimate

Why: Distinguish the operator being inverted from its inverse bound.
Recall: Use bounded real linear maps and quadratic-form inequalities.

The first reusable statement defines the Sylvester operator at X as A composed with X minus X composed with B. The second gives delta times norm X at most the norm of that result under the displayed ordered form bounds. The accepted bounded-operator lemma is broader than our motivation: it does not need finite dimension and does not require separate self-adjointness hypotheses when these real-part form bounds are supplied. In the lecture we used self-adjoint operators to explain the exponential decay geometrically.

## SyLean: Read the exact accepted form-bound theorem

Why: Connect each symbolic expression to its library statement.
Recall: The arrow with L denotes a bounded linear map.

The first code example expands the accepted Sylvester definition. The second names its two form hypotheses explicitly and applies the norm estimate. The scalar c positions the gap and delta is its width in our positive-gap application. The library inequality is multiplicative, so no division or positivity assumption is needed just to state that lemma. To divide by delta as we did earlier, require delta positive. These are applications of the accepted bounded API, not replacements for the separate domain-aware unbounded theorems.
