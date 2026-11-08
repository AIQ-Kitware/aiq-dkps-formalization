# 138000 — Beam Rayleigh–Ritz calculation

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `027000–030000`, `107000`, `137000`. **Next:** `139000`.

<!-- BEGIN SPOKEN LECTURE -->

# Beam Rayleigh–Ritz calculation

Consider the free-beam operator A on square-integrable functions on the unit interval. It acts as the fourth derivative on the self-adjoint domain of functions with four weak derivatives in the square-integrable class, whose second and third derivatives vanish at both endpoints. Its kernel consists of affine functions, while the remaining spectrum lies above five hundred. Perturb A by the bounded multiplication operator H of u equal to epsilon times t times u, with real epsilon positive and smaller than one hundred. We will compute how this perturbation acts on the two-dimensional affine trial space and how much escapes that space.

This calculation is worth doing by hand. A perturbation estimate cannot tell us anything numerical until we supply a residual and a spectral gap. The beam example provides both using only elementary integrals.

## Orthonormal coordinates for the affine kernel

Put x equal to two t minus one. Then x ranges from minus one to one, symmetrically about zero. Averaging over the original unit interval gives mean x equal to zero and mean x squared equal to one third.

Choose our first trial function to be one over square root of two times one minus square root of three times x. Choose the second with a plus sign instead of a minus sign.

Let us verify normalization. Squaring either trial function gives one half times one plus three x squared, plus a mixed term whose average is zero. The mean is one half times one plus three times one third, which equals one. For their cross inner product, multiply the plus and minus expressions. The cross product is one half times one minus three x squared. Its mean is zero. So the two functions are orthonormal.

They span the affine functions because their sum is a nonzero constant and their difference is a nonzero multiple of x. Each belongs to the domain of the unperturbed beam operator, and A annihilates each.

We can therefore package them as an isometric map E from real two-space into our Hilbert space. The unperturbed compression E star A E is the zero two-by-two matrix.

## Compute the perturbed compression

The perturbation H multiplies by epsilon t. Hence the compressed operator is epsilon times the matrix whose entries are integrals of t times products of the trial functions.

Rather than multiply four polynomials independently, use centered moments. The average of t equals one half. The average of t times x equals one sixth. And the average of t times x squared equals one sixth. These follow immediately from t equals one half times x plus one and the first three centered moments.

Substitute the two trial functions. The off-diagonal compressed entry is the average of t times one half times one minus three x squared. This equals one half times one half minus three times one sixth, which is zero.

The diagonal entries are not equal. For the first trial function, the negative mixed term reduces the mean to one half times one minus one over square root of three. For the second, the positive mixed term gives one half times one plus one over square root of three.

Thus our Rayleigh–Ritz matrix is already diagonal in the chosen trial basis. Its lower Ritz value is epsilon over two times one minus one over square root of three. Its upper Ritz value is epsilon over two times one plus one over square root of three.

Their sum is epsilon. Their difference is epsilon divided by square root of three. Both are positive for epsilon positive, and the upper one is less than about point seven eight eight seven times epsilon.

This internal Ritz gap will later help us separate the individual low-frequency modes.

## First residual: comparing against zero

Davis and Kahan begin with a simpler comparison operator on the trial space: zero. Because A E equals zero, its residual is simply H E. Its two columns are epsilon t times the two trial functions.

Compute the Gram matrix of this residual. The entry in row i and column j is epsilon squared times the integral of t squared times the product of trial functions i and j.

The centered moments now needed are the mean of t squared, equal to one third; the mean of t squared times x, equal to one sixth; and the mean of t squared times x squared, equal to two fifteenths. They are simple polynomial integrals on the unit interval.

Carrying out the multiplication gives epsilon squared over thirty times a symmetric two-by-two matrix. Its first diagonal entry is eleven minus square root of seventy-five. Its second diagonal entry is eleven plus square root of seventy-five. Both off-diagonal entries are negative one.

A Gram matrix is positive semidefinite, and its eigenvalues are the squares of the residual's singular values. The trace of this particular matrix is eleven epsilon squared over fifteen. Its two eigenvalues are epsilon squared over thirty times eleven minus square root of seventy-six, and eleven plus square root of seventy-six.

Therefore the largest residual singular value is epsilon times the square root of eleven plus square root of seventy-six, divided by thirty. This coefficient is approximately point eight one one. The second coefficient is approximately point two seven six.

These are the exact pieces behind the paper's first sine-angle estimate and its Ky Fan two-term estimate. Their derivation involved neither numerical eigenvalue solvers nor approximations to free-beam eigenfunctions.

## Recenter at the Ritz matrix

We can do better by allowing the trial coordinates to evolve under their own compressed matrix. Let A hat be the diagonal Ritz matrix. Define the recentered residual R hat to be the perturbed operator applied to E, minus E followed by A hat.

Because A hat equals E star times the perturbed operator times E, the adjoint E star annihilates this new residual. This is Galerkin orthogonality. R hat takes values entirely in the orthogonal complement of the trial plane.

For its Gram matrix, use the identity R hat star R hat equals E star H squared E minus A hat squared. The first term can be integrated directly from the trial functions. Its upper-left entry is epsilon squared times eleven thirtieths minus one over twice the square root of three. Its lower-right entry has a plus sign in place of that minus sign. Its two off-diagonal entries are minus epsilon squared over thirty. Subtracting the square of the diagonal Ritz matrix cancels most of the diagonal energy.

The result is strikingly simple: epsilon squared over thirty times the matrix whose diagonal entries are one and whose off-diagonal entries are negative one.

That matrix has eigenvectors in the sum and difference directions. The sum direction has eigenvalue zero; the difference direction has eigenvalue two. Thus the recentered residual has singular values epsilon divided by square root of fifteen and zero.

It is rank one. Its operator norm and its two-term Ky Fan norm are the same: epsilon over square root of fifteen. And each of its two columns separately has norm epsilon over square root of thirty.

One might be surprised that two distinct trial functions yield a rank-one residual. The explanation is that multiplication by t sends the affine plane into polynomials of degree at most two. After removing the affine component, only the single quadratic direction remains. There is exactly one direction in which both residual columns can escape.

## A numerical consistency check

Take epsilon equal to ten, which lies in the parameter range zero less than epsilon less than one hundred. The Ritz values are approximately two point one one three and seven point eight eight seven. The recentered residual's only nonzero singular value is ten divided by square root of fifteen, about two point five eight two.

The high modes remain above five hundred. So the gap between our upper Ritz value and the high spectrum is greater than five hundred minus seven point eight eight seven, or approximately four hundred ninety-two point one one three.

An estimate that divides the recentered residual by that gap produces an angle of only about five thousandths in tangent units. This is why treating the Ritz matrix rather than the zero matrix improves the result.

## What the calculation does and does not prove

We have established exactly the compression and the residual. We have not yet proved that the Ritz vectors are individual eigenvectors of the perturbed beam. They generally are not. Nor have we identified the exact two-dimensional perturbed eigenspace; that requires the spectral theorem and the gap protecting the low cluster.

An operator-norm bound controls the largest principal angle, while a Ky Fan bound controls a sum of principal angles. A tangent estimate also uses stronger spectral placement and can improve on the initial sine estimate.

The broader method is reusable: choose trial functions in the operator domain; form their Gram and compressed matrices; orthonormalize; compute the residual Gram operator; and only then invoke a gap theorem. Nothing in this workflow depends on having closed-form eigenfunctions of the perturbed operator.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(x=2t-1\), \(e_{1,2}(t)=(1\mp\sqrt3 x)/\sqrt2\). With \(T=A+H\), \(Hf(t)=\varepsilon tf(t)\), and \(E=(e_1,e_2)\),
\[
E^*TE=\frac\varepsilon2\operatorname{diag}(1-1/\sqrt3,1+1/\sqrt3),
\]
\[
(HE)^*(HE)=\frac{\varepsilon^2}{30}
\begin{pmatrix}11-\sqrt{75}&-1\\-1&11+\sqrt{75}\end{pmatrix},\qquad
\widehat R^*\widehat R=\frac{\varepsilon^2}{30}
\begin{pmatrix}1&-1\\-1&1\end{pmatrix}.
\]
Here \(\widehat R=TE-E(E^*TE)=(I-EE^*)HE\). Thus \(s(\widehat R)=(\varepsilon/\sqrt{15},0)\) for \(\varepsilon>0\). The initial residual singular values follow from \(\frac{\varepsilon^2}{30}(11\pm\sqrt{76})\).

## Exact Lean declaration excerpts


**`ritz_matrix_from_affine_moments`.** Integrals of multiplication by `t` against the explicit orthonormal affine pair give the diagonal Ritz matrix.

`DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean` — `ritz_matrix_from_affine_moments` (exact declaration header; proof body omitted):

```lean
theorem ritz_matrix_from_affine_moments (ε : ℝ) :
    ε * CenteredAffine.tInner trialOne trialOne = ritzLow ε ∧
    ε * CenteredAffine.tInner trialOne trialTwo = 0 ∧
    ε * CenteredAffine.tInner trialTwo trialTwo = ritzHigh ε :=
```


**`initial_residual_gram_from_affine_moments`.** Second moments of `t` give the unrecentered residual Gram matrix; this result is an exact finite-moment identity.

`DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean` — `initial_residual_gram_from_affine_moments` (exact declaration header; proof body omitted):

```lean
theorem initial_residual_gram_from_affine_moments (ε : ℝ) :
    SymmetricTwoByTwo.mk
      (ε ^ 2 * CenteredAffine.tSqInner trialOne trialOne)
      (ε ^ 2 * CenteredAffine.tSqInner trialOne trialTwo)
      (ε ^ 2 * CenteredAffine.tSqInner trialTwo trialTwo) = residualGram ε :=
```


**`recentered_residual_gram_from_affine_moments`.** Subtracting the square of the Ritz compression gives the exact rank-one recentered residual Gram matrix.

`DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean` — `recentered_residual_gram_from_affine_moments` (exact declaration header; proof body omitted):

```lean
theorem recentered_residual_gram_from_affine_moments (ε : ℝ) :
    SymmetricTwoByTwo.mk
      (ε ^ 2 * (CenteredAffine.tSqInner trialOne trialOne -
        CenteredAffine.tInner trialOne trialOne ^ 2))
      (ε ^ 2 * (CenteredAffine.tSqInner trialOne trialTwo -
        CenteredAffine.tInner trialOne trialOne *
          CenteredAffine.tInner trialOne trialTwo))
      (ε ^ 2 * (CenteredAffine.tSqInner trialTwo trialTwo -
        CenteredAffine.tInner trialTwo trialTwo ^ 2)) =
      orthogonalResidualGram ε :=
```


**`orthogonalResidualGram_det`.** The determinant vanishes; together with its trace and nonnegativity, the Gram eigenvalues are zero and epsilon squared over fifteen.

`DavisKahan/Sources/DavisKahan1970/Section9/ExactData.lean` — `orthogonalResidualGram_det` (exact declaration header; proof body omitted):

```lean
lemma orthogonalResidualGram_det (ε : ℝ) :
    (orthogonalResidualGram ε).det = 0 :=
```
