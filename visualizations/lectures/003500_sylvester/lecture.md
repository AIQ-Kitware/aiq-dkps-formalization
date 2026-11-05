# Sylvester equations and spectral separation

See [operator lecture provenance](../../dkvis/learning/operators/README.md) for accepted source modules and scope.
Numerical reference: https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.solve_sylvester.html

## SyTitle: Sylvester equations and spectral separation

Why: Turn residual equations into quantitative error bounds.
Recall: Know operator norms and matrix exponentials.

Sylvester equations and spectral separation.

## SySetup: The equation and the ordered gap

Why: State what is known, what is unknown, and which norm is used.
Recall: $AX-XB=R$; $A\ge(c+\delta)I$ and $B\le cI$; $\delta>0$.

A and B are known self-adjoint matrices, acting on possibly different spaces. X is the unknown map from the B space to the A space, and R is a known map of the same shape. The norm in this lecture is the operator norm: largest output length on unit inputs. An ordered gap means A is above c plus delta times identity in quadratic forms, while B is below c times identity; delta is positive. A quadratic-form inequality compares the inner products of the two sides with the same vector. Finally, exponential t A is defined by its matrix power series. We use that flow to derive an integral estimate, then explain which part extends to bounded Hilbert-space operators.

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

## SyFacts: The definition and the gap estimate

Why: Distinguish the operator being inverted from its inverse bound.
Recall: Use bounded real linear maps and quadratic-form inequalities.

The first reusable statement defines the Sylvester operator at X as A composed with X minus X composed with B. The second gives delta times norm X at most the norm of that result under the displayed ordered form bounds. The accepted bounded-operator lemma is broader than our motivation: it does not need finite dimension and does not require separate self-adjointness hypotheses when these real-part form bounds are supplied. In the lecture we used self-adjoint operators to explain the exponential decay geometrically.

## SyLean: The Sylvester definition in Lean

Why: Separate the map definition from the inverse estimate.
Recall: $\mathcal S_{A,B}(X)=AX-XB$.

A, B, and X are bounded real linear maps. This displayed specialization uses one space for compact notation, although the accepted API also allows two spaces. Sylvester A B is itself a bounded linear map acting on the unknown X. Expanding its definition gives A composed with X minus X composed with B. The green line applies the defining equality. The estimate requires additional form hypotheses, which appear on their own card next.

## SyLeanGap: The ordered-gap estimate in Lean

Why: Read the actual form hypotheses before using the bound.
Recall: $\delta\|X\|\le\|AX-XB\|$.

The assumptions h A and h B explicitly bound the real parts of the quadratic forms on every vector. Their endpoints are c plus delta and c. Under these conditions, the accepted theorem bounds delta times norm X by the norm of the Sylvester output. It does not require finite dimension or separate self-adjointness assumptions once these form bounds are given. The inequality is multiplicative. For our divided residual-over-gap estimate we additionally require delta positive. The long green theorem name is the library proof of this exact implication.

## SyComputation: Bonus: Solve without building a huge Kronecker matrix

Why: Use structure in the numerical linear equation.
Recall: Our convention has a minus sign before X B.

As an optional numerical bonus, here is how this mathematical tool is used in computation. For dense matrices, Bartels–Stewart methods use Schur decompositions, solve the resulting triangular matrix equations, then transform back. This avoids explicitly forming the much larger Kronecker system. SciPy's solve_sylvester uses the convention A X plus X B equals Q. To solve our equation, pass minus B as its second argument. Afterwards measure A X minus X B minus R. A small computed residual becomes a solution-error estimate only after a valid inverse bound is available, just as in the motivation.
