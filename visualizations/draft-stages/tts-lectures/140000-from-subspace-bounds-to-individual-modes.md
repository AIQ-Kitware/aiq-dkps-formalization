# 140000 — From subspace bounds to individual modes

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `111000–113000`, `127000–129000`, `137000–139000`. **Next:** `141000`.

<!-- BEGIN SPOKEN LECTURE -->

# From subspace bounds to individual modes

The beam example has given us strong control of a two-dimensional spectral subspace. We know the perturbed low eigenspace stays close to the affine trial plane. But suppose an engineer asks a different question: how close is the lower Ritz vector to the lower true vibration mode? That question cannot be answered by a subspace-angle estimate alone.

To see why, consider two orthonormal bases of the same plane, one rotated forty-five degrees from the other. The planes are identical, so their largest principal angle is zero. Yet the corresponding basis vectors are far from identical. We need to track motion within the trial plane as well as motion out of it.

## Separate the two angle contributions

Take one normalized exact low eigenvector, call it f. Project it orthogonally onto the trial plane. If the projection is nonzero, normalize it to obtain g. Let eta be the angle from f to the trial plane, equivalently the angle from f to g.

Now choose the Ritz vector e that we expect to approximate f. Let psi be the angle between g and e, both of which lie in the trial plane. Finally, let omega be the total angle between e and f.

Because e lies in the plane, its inner product with f equals its inner product with the projection of f. The projection has length cosine eta and direction g. Thus the absolute inner product between e and f equals cosine eta times cosine psi.

In other words, cosine omega equals cosine eta times cosine psi, after choosing acute vector-angle conventions. This is an exact identity.

A useful consequence is that omega squared is bounded by eta squared plus psi squared in the relevant range. The geometry can be proved by comparing the cosine expressions, or by elementary trigonometric inequalities. It turns a two-stage rotation into a quantitative estimate for the individual vector.

We already control eta by a subspace perturbation theorem. We must now control psi, the in-plane rotation.

## Express the eigenproblem in blocks

Use the orthogonal decomposition of the Hilbert space into the trial plane and its perpendicular complement. The perturbed beam operator becomes a two-by-two operator matrix in block form.

The upper-left block is the diagonal two-by-two Ritz matrix. The lower-right block is the perturbed beam compressed to the complementary space. The lower-left block sends a trial vector into its Galerkin residual, and the upper-right block is its adjoint.

Write our exact eigenvector as a pair of coordinates: x in the trial plane and y in the complement. The eigenvalue equation gives two coupled relations.

The upper equation says the Ritz matrix applied to x, plus the adjoint residual block applied to y, equals lambda times x. The lower equation says the residual block applied to x, plus the complementary operator applied to y, equals lambda times y.

Every term is meaningful because the eigenvector belongs to the operator domain. We must keep that condition in an unbounded problem. An abstract block matrix is shorthand for the properly restricted operator action, not permission to apply the fourth derivative to arbitrary vectors.

## Solve for the out-of-plane coordinate

The complementary operator has quadratic-form lower bound greater than five hundred, while our low eigenvalue is below five hundred. The lower equation can be rearranged so that the shifted lower block, lambda minus the complementary operator, acts on y and gives the residual block applied to x.

That shifted block has a bounded inverse on the appropriate space. Formally, y equals that inverse applied to B x, where B denotes the residual block.

To prove a bound, we do not even need to write the inverse. Take the inner product of the lower equation with y. The form lower bound gives five hundred times the squared norm of y. The lambda term subtracts lambda times that squared norm. Cauchy–Schwarz controls the residual pairing by the norm of B x times the norm of y.

Cancel one factor when y is nonzero. We obtain five hundred minus lambda times the norm of y no greater than the norm of B x.

Since the full residual block has norm at most epsilon divided by square root of fifteen, the out-of-plane coordinate is of order epsilon over the large spectral gap. This gives our control of eta.

## Substitute back into the trial equation

Now substitute the formula for y into the upper equation. The result is an eigenvalue problem entirely on the two-dimensional trial plane, but with an extra correction term.

The effective matrix is the diagonal Ritz matrix plus B star times the inverse of lambda minus the complementary operator times B. Because lambda lies below the complementary spectrum, that correction is negative semidefinite.

The residual is rank one. Its Gram matrix is epsilon squared over thirty times the matrix with diagonal entries one and off-diagonal entries negative one. Consequently the Schur correction is controlled by a scalar multiple of exactly that rank-one matrix.

Let the scalar be q. Our earlier lower-block estimate gives q no greater than epsilon squared divided by thirty times five hundred minus lambda. The effective two-by-two matrix therefore has diagonal Ritz entries, shifted by a common correction, and an off-diagonal coupling of size q.

A common diagonal shift does not rotate eigenvectors. The mixing comes from the off-diagonal entry. For a real symmetric two-by-two matrix with diagonal gap Delta and off-diagonal entry q, the eigenvector rotation psi satisfies tangent of twice psi equal to two q divided by Delta, with an appropriate sign convention.

Here Delta is the Ritz gap, epsilon divided by square root of three. Therefore one half of tangent of twice psi is bounded by square root of three over thirty times epsilon divided by five hundred minus lambda.

That identifies the internal rotation explicitly. It is also why the Ritz gap matters: the out-of-plane separation protects the plane, while the internal separation identifies the individual basis vectors within the plane.

## Combine the errors

The source combines a subspace estimate for eta with this two-by-two bound for psi. One convenient common envelope has coefficient square root of seven over ten, divided by five hundred minus an upper bound on lambda, times epsilon.

The two Ritz eigenvalues have different upper bounds: the lower one is about point two one one three times epsilon, and the higher is about point seven eight eight seven times epsilon. Hence the two final eigenvector estimates carry different denominators.

In the printed numerical form, the lower eigenvector angle omega one is below approximately point zero zero zero five three epsilon divided by one minus point zero zero zero four three epsilon. The upper angle omega two has the same numerator, but denominator one minus point zero zero one six epsilon.

The precise source rational forms use slightly conservative decimals. What matters is that these are individual eigenvector angles, not principal angles between entire planes.

## The alternative one-vector route

The paper also applies its one-vector tangent theorem directly to each Ritz vector. Each recentered residual column has norm epsilon divided by square root of thirty, smaller than the norm of the full rank-one residual map.

Divide that individual residual by the appropriate gap. This yields sharper individual tangent bounds with numerator about point zero zero zero three six five two times epsilon. The denominator for the lower vector uses its lower Ritz value, while the upper vector uses the upper Ritz value.

Those estimates are statements about the angle between each fixed trial vector and the exact low spectral plane. To turn such information into pairing with an individual exact eigenvector, we still need internal spectral separation and the Schur argument. The source's final eigenvector comparison supplies that extra step.

The lesson is to keep three angles distinct: the angle of a whole subspace, the angle of one trial vector to that subspace, and the angle between a named trial vector and a named exact eigenvector.

## General method

When you want individual modes rather than a low-frequency cluster, proceed in two stages. First estimate the leakage of the entire cluster into its orthogonal complement. Then construct an effective operator on the cluster using a Schur complement. Control its off-diagonal entries relative to the internal Ritz gap.

If the internal gap closes, even a perfectly stable subspace may have unstable individual eigenvectors. The beam calculation makes this distinction measurable, and it prepares us for the open questions about what spectral separation assumptions really suffice.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a normalized eigenvector \(f=(x,y)\) of the block operator, with \(\lambda<\inf\sigma(A_1)\),
\[
B x+A_1 y=\lambda y,\qquad
(\beta-\lambda)\|y\|\le\|Bx\|,
\]
\[
\bigl[A_0+B^*(\lambda-A_1)^{-1}B\bigr]x=\lambda x.
\]
Writing \(\cos\omega=\cos\eta\cos\psi\), the source controls the complementary angle \(\eta\) and internal Ritz rotation \(\psi\) separately. In the free-beam model \(\widehat R^*\widehat R=(\varepsilon^2/30)\begin{psmallmatrix}1&-1\\-1&1\end{psmallmatrix}\), yielding a rank-one Schur correction. The final source-facing eigenvector-angle statements concern paired exact eigenvectors, whereas the one-vector tangent bounds initially concern trial vectors versus the exact low eigenspace.

## Exact Lean declaration excerpts


**`schur_complement_reduction`.** This algebraic theorem assumes a left inverse of `lambda I - A1`; the unbounded beam case additionally requires checking the block domains.

`DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean` — `schur_complement_reduction` (exact declaration header; proof body omitted):

```lean
theorem schur_complement_reduction
    (x : E) (y : F)
    (htop : A₀ x + Bstar y = lam • x)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    y = C (B x) ∧ A₀ x + Bstar (C (B x)) = lam • x :=
```


**`norm_lower_coordinate_le`.** A quadratic-form lower bound and the lower block equation yield the inverse-free estimate for the complementary eigenvector coordinate.

`DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean` — `norm_lower_coordinate_le` (exact declaration header; proof body omitted):

```lean
theorem norm_lower_coordinate_le {b w y : F} {lam β : ℝ}
    (hbottom : b + w = (lam : 𝕜) • y)
    (hform : β * ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 w y))
    (_hlt : lam < β) :
    (β - lam) * ‖y‖ ≤ ‖b‖ :=
```


**`half_tanTwoPsi_ratio_lt`.** A scalar upper bound for the rank-one Schur correction and the Ritz gap yields the exact coefficient in the half-tangent bound.

`DavisKahan/Sources/DavisKahan1970/Section9/RankOneCorrection.lean` — `half_tanTwoPsi_ratio_lt` (exact declaration header; proof body omitted):

```lean
theorem half_tanTwoPsi_ratio_lt
    {ε D q : ℝ} (hε : 0 < ε) (hD : 0 < D)
    (_hq0 : 0 ≤ q) (hq : q < ε ^ 2 / (30 * D)) :
    q / (ritzHigh ε - ritzLow ε) <
      (Real.sqrt 3 / 30) * ε / D :=
```


**`freeBeam_individualEigenvectorAngle_bounds`.** The final **paired eigenvector** result uses two distinct denominators and ordered exact eigenvalues; it is stronger in scope than a trial-vector-to-eigenspace estimate.

`DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` — `freeBeam_individualEigenvectorAngle_bounds` (exact declaration header; proof body omitted):

```lean
theorem freeBeam_individualEigenvectorAngle_bounds (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {j k : Fin 2} (hjk : j ≠ k)
    (hle : beamLowEigenvalue ε hε.le hε100 j ≤ beamLowEigenvalue ε hε.le hε100 k) :
    Real.arccos ‖inner ℂ (centeredAffineLp trialOne) (beamLowEigenvector ε hε.le hε100 j)‖
        < ((53 : ℝ) / 100000 * ε) / (1 - (43 : ℝ) / 100000 * ε) ∧
      Real.arccos ‖inner ℂ (centeredAffineLp trialTwo) (beamLowEigenvector ε hε.le hε100 k)‖
        < ((53 : ℝ) / 100000 * ε) / (1 - (1 : ℝ) / 625 * ε) :=
```


**`freeBeam_trialVector_tanAngle_bounds`.** The sharper one-column tangent conclusions apply to each specific trial vector relative to the low exact spectral subspace.

`DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` — `freeBeam_trialVector_tanAngle_bounds` (exact declaration header; proof body omitted):

```lean
theorem freeBeam_trialVector_tanAngle_bounds
    (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
        < ((913 : ℝ) / 2500000 * ε) /
            (1 - (4227 : ℝ) / 10000000 * ε) ∧
      beamTanPhi ε (centeredAffineLp trialTwo)
        < ((913 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
```
