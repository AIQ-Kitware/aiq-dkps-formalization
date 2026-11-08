# 069000 — Norm dependence of Sylvester bounds

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `052000–058000` singular values and operator ideals; `063000–068000` Sylvester equations and their integral/inverse estimates. **Next:** Hilbert–Schmidt Sylvester group estimates.

<!-- BEGIN SPOKEN LECTURE -->

# Which gap gives which constant?

The Sylvester equation A X minus X B equals C admits different estimates under different spectral-gap assumptions. An ordered gap yields a constant-one operator-norm estimate using decaying exponentials. Mere pairwise separation yields constant one in Hilbert-Schmidt norm; for the bounded self-adjoint operator-norm problem, a Fourier kernel gives a general factor of pi over two. These conclusions require distinct hypotheses.

It is easy to mix these results together. Today we will organize them by asking two questions every time: what spectral geometry is assumed, and which norm measures the unknown operator?

We will also work through a two-by-two example from the Davis–Kahan source that proves a constant-one operator-norm estimate cannot hold under pairwise spectral separation alone.

## Three operator norms to keep distinct

Start with a finite matrix X. Its operator norm is the largest length of X applied to a unit vector. By the singular-value decomposition, this is its largest singular value.

Its Frobenius norm is the square root of the sum of the squares of all singular values. In an orthonormal matrix coordinate system, it is also the square root of the sum of squared absolute entries.

Its nuclear norm is the sum of all singular values. More generally, the Schatten p norm takes the p-th powers of singular values, adds them, and takes the p-th root. Every Schatten norm and every symmetric-gauge norm is unitarily invariant in finite dimensions.

Although these norms are related, they answer different questions. The operator norm records the most amplified input direction. The Frobenius norm sums energy over orthogonal directions. The nuclear norm sums all singular values without squaring them.

A proof exploiting entrywise orthogonality may be sharp for Frobenius norm and insufficient for operator norm.

## Pairwise separation gives a sharp square-norm estimate

Suppose A and B are finite-dimensional self-adjoint matrices and every left-right eigenvalue difference has absolute value at least delta.

In orthonormal eigenbases, the Sylvester solution is obtained by dividing each entry of C by its spectral difference. Squaring and summing gives delta times the Frobenius norm of X at most the Frobenius norm of C.

This follows by diagonalizing the self-adjoint coefficients and estimating each squared matrix coefficient. No ordering of the spectra is required. The constant one is sharp in the scalar case.

Why does the argument work? Because the Frobenius norm sees the matrix entries as coordinates in an inner-product space of operators. The spectral blocks are orthogonal in this square norm, so we can estimate each block separately and add the resulting squared inequalities.

A comparable statement extends to Hilbert–Schmidt operators on infinite-dimensional Hilbert spaces. There, square-summability replaces finite sums, and the Sylvester group has a self-adjoint generator acting on the Hilbert space of Hilbert–Schmidt maps.

## From the square norm to the operator norm

Every finite matrix has operator norm at most its Frobenius norm. If C has rank r, its Frobenius norm is at most the square root of r times its operator norm, because it has at most r nonzero singular values and none exceeds the largest.

Combine those comparisons with the sharp square-norm Sylvester estimate. First, delta times the operator norm of X is at most delta times the Frobenius norm of X. Next, that is at most the Frobenius norm of C. Finally, it is at most square root of r times the operator norm of C.

Thus pairwise separation yields an operator-norm estimate with a rank factor. This is a valid consequence, but it is not usually the most effective general operator-norm estimate.

The rank enters because we changed norms. It is not part of the underlying square-norm theorem.

## The source's two-by-two obstruction

Now take A diagonal with entries one and negative one. Take B diagonal with entries zero and two. Their spectra are separated pairwise by at least one, so delta equals one.

Let X have first row three, negative three, and second row negative three, one. This is a symmetric two-by-two matrix.

Compute C as A X minus X B. Multiplying on the left by A preserves the first row and reverses the second. Multiplying on the right by B sets the first column to zero and doubles the second.

Subtract the results. C has first row three, three, and second row three, negative three.

The columns of C are orthogonal, each with length three times the square root of two. Therefore its operator norm is three times the square root of two, approximately four point two four.

For X, the trace is four and the determinant is negative six. Its characteristic polynomial is the scalar variable squared minus four times that variable minus six. The eigenvalues are two plus the square root of ten and two minus the square root of ten.

Since X is symmetric, its operator norm is the larger absolute eigenvalue, two plus the square root of ten, approximately five point one six.

The gap is one, so delta times the operator norm of X is about five point one six, strictly larger than the operator norm of C, about four point two four.

That disproves the claim that pairwise spectral separation always implies a constant-one estimate in operator norm. The example is not a numerical accident: the source formalizes the exact singular values, spectral gap, Sylvester equation, and strict inequality.

## What ordered separation restores

If every spectral value of A lies at least delta above every spectral value of B, our exponential semigroup formula gives the stronger estimate: delta times the operator norm of X is at most the operator norm of C.

The key is a single decay estimate for the entire transported operator. It does not depend on how different entries interact in the operator norm. The same argument works for compatible operator ideal norms whenever the integral is defined in that norm.

The interval-versus-exterior configuration also admits a constant-one conclusion under the bounded-inverse hypotheses of Theorem five point one. After a common scalar shift, one block has norm at most gamma, while the other has a bounded inverse with norm at most one over gamma plus delta.

The proof then uses a fixed-point inequality instead of semigroup decay.

Both configurations are more structured than arbitrary pairwise distance. In one, all spectral differences have a consistent sign. In the other, one block is trapped in a central interval and the other avoids a larger surrounding interval.

## What general separation gives instead

For arbitrary pairwise-separated bounded self-adjoint spectra, the Fourier multiplier representation from lecture sixty-six gives a uniform operator-norm bound. Delta times the operator norm of X is at most pi over two times the operator norm of C.

The pi-over-two factor is the exact integral of the absolute value of the chosen scalar multiplier, after scaling by delta. The proof works because unitary left and right multiplication preserve the operator norm.

Compatible symmetric-gauge norms also admit the same type of bound in finite-dimensional settings. Left and right unitary multiplications preserve singular values; multiplying by the scalar kernel scales every norm; the triangle inequality controls the integral.

This shows where norm compatibility enters. A quantity that can increase under left or right unitary transport, or that lacks the appropriate triangle inequality, cannot inherit the Fourier bound by this argument.

We should distinguish a valid universal upper bound from an assertion of optimality. The present construction proves the pi-over-two upper bound. Establishing best-possible constants in a particular norm and spectral class requires additional examples or extremal arguments.

## A compact hierarchy of conclusions

Let's organize the statements verbally.

First: for self-adjoint A and B with a positive pairwise gap, the Hilbert–Schmidt solution satisfies a constant-one estimate in the square norm.

Second: under the same pairwise gap, an operator-norm estimate with a square-root rank factor follows if the right-hand side has finite rank. An independent Fourier argument gives a dimension-free pi-over-two bound.

Third: under ordered spectral separation, a decaying semigroup gives the constant-one operator-norm bound, and similarly for compatible ideal norms.

Fourth: under the Banach-space bounded-inverse and compatible-norm hypotheses of Theorem five point one, the fixed-point proof also gives a constant-one estimate, without requiring an inner product.

None of these statements makes the others redundant. They cover different hypotheses and sometimes different operator classes.

## A test for any new Sylvester estimate

Whenever someone presents a perturbation inequality that contains a spectral gap in the denominator, ask what theorem supplies it.

Can we point to a common spectral cut? Can we center a small block and control the other block's inverse? Are we only given pairwise spectral distance? Are the operators self-adjoint or possibly nonnormal? Is the relevant norm operator, Frobenius, or another invariant ideal norm?

Each answer changes the proof that is permitted.

The Hilbert-Schmidt estimate is obtained by treating operators as vectors in a Hilbert space. The scalar cross-spectral differences then give constant-one control even when the spectra interlace, provided their distance is bounded below.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A,B\) be bounded self-adjoint operators and let \(AX-XB=C\). Comparison by hypothesis and norm:

| Gap geometry | Norm | Supported estimate |
|---|---|---|
| Pairwise \(|a-b|\ge\delta\) | Hilbert–Schmidt | \(\delta\|X\|_{S_2}\le\|C\|_{S_2}\) |
| Pairwise, \(\operatorname{rank}(C)\le r\) | Operator | \(\delta\|X\|\le\sqrt r\|C\|\) |
| Pairwise | Operator | \(\delta\|X\|\le\tfrac\pi2\|C\|\) via the Fourier kernel |
| Ordered | Operator, compatible ideals | \(\delta N(X)\le N(C)\) via semigroup decay |
| Bounded inverse \(\|A^{-1}\|\le(\gamma+\delta)^{-1}\), \(\|B\|\le\gamma\) | Compatible Banach cross-operator norm | \(\delta N(X)\le N(C)\) |

The real symmetric source witness has
\[
A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
B=\begin{pmatrix}0&0\\0&2\end{pmatrix},\quad
X=\begin{pmatrix}3&-3\\-3&1\end{pmatrix},\quad
C=\begin{pmatrix}3&3\\3&-3\end{pmatrix}.
\]
For \(\delta=1\), \(\|X\|=2+\sqrt{10}>3\sqrt2=\|C\|\), refuting a constant-one pairwise-gap operator-norm claim.

**Lean bridge (verbatim source excerpts).**

`DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean` — `opNorm_sylvester_le_of_pairwiseSpectrumGap`:

```lean
theorem opNorm_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    {r : ℕ} (hRank : C.rank ≤ (r : Cardinal)) :
    δ * ‖X‖ ≤ ‖C‖ * Real.sqrt r := by
```

The theorem derives the rank-dependent operator-norm bound from the Hilbert–Schmidt estimate. It applies to self-adjoint partial operators and a finite-rank right-hand side.

`DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean` — `sharp52_constant_one_too_small`:

```lean
theorem sharp52_constant_one_too_small :
    ‖sharpC52.toContinuousLinearMap‖ < 1 * ‖sharpX52.toContinuousLinearMap‖ := by
```

This is the exact counterexample showing that constant one fails for the operator norm under merely pairwise separation.

`DavisKahan/InfiniteDimensional/Sylvester/FourierSemigroup.lean` — `mul_l1_norm_separatedSylvesterMultiplier`:

```lean
theorem mul_l1_norm_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    d * (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) = Real.pi / 2 := by
```

The source proves the exact `π/2` mass of the reciprocal Fourier multiplier, which underwrites the corresponding universal operator-norm upper bound.

