# Uniform approximation — what happens to a minimum?

## UmTitle: Uniform approximation and minima

Why: Justify optimizing before taking a limit.
Recall: Functions, inequalities, and limits.

Uniform approximation, and what happens to a minimum.

## LectureOutcomes: Three facts about approximate objectives

Why: Keep values and locations distinct.
Recall: Two real-valued costs on the same nonempty candidate set.

A uniform error bound controls every candidate with the same tolerance. Minimum values change by at most that tolerance. Close minimum values do not guarantee close minimizing points. The question is whether a convenient approximate cost can replace a harder one during optimization. We will prove a two-sided bound, then show exactly what it does not say about the optimizer.

## UmSetup: Values, points, and a shared tolerance

Why: Fix the local setting and explain the objects.
Recall: The opening conclusions describe what we will establish.

f is the original cost and g an approximation on the same candidate set. x star minimizes f and y star minimizes g. We assume these minima exist; uniqueness is not needed. Epsilon is a non-negative number bounding the absolute error between the costs at every candidate. A minimum value is a number such as f of x star. A minimizing point is the candidate x star itself. The distinction will matter when we take a limit.

## UmBand: One band for every candidate

Why: Give uniform a geometric meaning.
Recall: The example uses f of x equals x squared on a closed interval.

The blue curve is the true cost f. The amber curve g stays within a vertical band of height epsilon above or below it. Uniform means the same epsilon works at every x in the candidate set. We may inspect different candidates as the approximation changes; none escapes this bound.

<!-- beat -->

As epsilon shrinks, the entire amber curve is trapped in a thinner band. Pointwise convergence asks a weaker question: at each fixed x, does the error eventually become small? Its required stage may depend on x. Uniform convergence was developed in nineteenth-century analysis to control operations on whole functions. Optimization makes this distinction especially concrete because the best candidate can move.

## UmUpper: The approximate minimum cannot be too high

Why: Use an old minimizer as a test candidate.
Recall: x star minimizes f; y star minimizes g.

The destination is an absolute difference between the two minimum values of at most epsilon. For the upper bound, g of y star is at most g of x star because y star minimizes g. The uniform band says g of x star is at most f of x star plus epsilon. Combining the inequalities proves the upper half. We did not need to know where y star is. We only needed its minimizing property and a bound at one legitimate candidate.

## UmLower: The approximate minimum cannot be too low

Why: Use the true minimum to bound a moving candidate.
Recall: The same two minimizers and the same error band.

For the lower bound, g of y star is at least f of y star minus epsilon. Since x star minimizes f, this is at least f of x star minus epsilon. Both inequalities together put the approximate minimum in the interval from the true minimum minus epsilon to the true minimum plus epsilon. The argument works on any candidate set when these minima exist. For finite infima, analogous bounds can be proved using candidates arbitrarily close to the infimum; attainment is a separate issue.

## UmDip: Pointwise convergence can miss a moving cheap region

Why: Show why the uniform hypothesis matters.
Recall: Example: continuous costs on the interval zero to one.

Here the nth cost has a narrow triangular dip centered at one over n. Its minimum is always minus one. Every fixed positive x eventually lies to the right of the dip, so its cost eventually equals zero. At x equals zero the cost is already zero. Thus the functions converge pointwise to the zero function, whose minimum is zero.

<!-- beat -->

The dip moves toward zero and becomes narrower, but its depth never shrinks. This is why the convergence is not uniform. An optimizer can follow the dip even though a viewer staring at any fixed location eventually stops seeing it. Pointwise convergence alone therefore does not justify passing minimum values through the limit, even for continuous functions on a compact interval.

## UmLocations: Values can converge while minimizers move

Why: Limit the conclusion to what was proved.
Recall: Example: costs on the interval zero to one.

Let the nth cost be minus one to the n, times x divided by n. Its uniform distance from the zero function is at most one over n. The minimum values tend to zero, just as our theorem predicts. But the minimizing endpoint alternates between zero and one. The limiting function is flat and every point minimizes it. To control a unique optimizer’s location, we need further information about the shape or isolation of the minimum. Value convergence alone is insufficient.

## UmSummary: What may safely pass to the limit?

Why: Return to the three opening claims.
Recall: The candidate set is the same for all costs.

A uniform error bound controls every candidate with the same tolerance. Minimum values change by at most that tolerance. Close minimum values do not guarantee close minimizing points. In a smooth approximation argument, establish one bound over the entire feasible set, with its error tending to zero. Then the minimum values converge by the two comparisons just proved. Convergence of minimizing maps needs its own argument. The gap between these conclusions is important whenever an approximation makes differentiation possible but changes the shape of the objective.

## UmFacts: The two comparisons behind the absolute-value bound

Why: Pair elementary reasoning with Lean.
Recall: x minimizes f and y minimizes g.

The upper comparison uses g of y at most g of x at most f of x plus epsilon. The lower comparison uses f of x minus epsilon at most f of y minus epsilon at most g of y. These are the complete ingredients. Uniformity matters because y may depend on the approximation. Compactness can help prove a minimum exists, but it is not used in these comparisons once minimizers are supplied.

## UmLean: Lean: test the old minimizer

Why: Read the upper comparison as two inequalities.
Recall: The costs are functions from any type to the real numbers.

The hypothesis h min says y minimizes g over all candidates. The hypothesis h upper bounds g above by f plus epsilon at every candidate. Applying both at x and using order transitivity gives the upper bound on the approximate minimum. The type alpha records that no vector-space structure is needed.

## UmLeanLower: Lean: bound the new minimizer

Why: Read the second half of the sandwich.
Recall: The same candidate set and the same epsilon.

The hypothesis h min now states that x minimizes f. Subtracting epsilon preserves that inequality. The lower band bound at y then gives the result by transitivity. Together the two cards prove the absolute-value estimate from the symbolic slide. They prove value control and do not assert convergence of x or y.

## UmComputation: Bonus: a grid check is not a uniform certificate

Why: Distinguish sampled evidence from a bound on every input.
Recall: A finite grid tests only some candidates.

A moving narrow dip can fall between sampled points. Checking a small error on a grid therefore does not by itself establish a uniform bound. A known Lipschitz bound can control what happens between samples, or an analytic inequality can bound every input directly. In a matrix problem, a bound on each singular-value contribution plus a fixed dimension can sometimes provide the required uniform objective bound. The numerical pictures illustrate the claim; the inequality over all candidates is what proves it.
