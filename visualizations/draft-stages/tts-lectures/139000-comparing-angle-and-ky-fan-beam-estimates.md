# 139000 — Comparing angle and Ky Fan beam estimates

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `054000–059000`, `110000–127000`, `137000–138000`. **Next:** `140000`.

<!-- BEGIN SPOKEN LECTURE -->

# Comparing angle and Ky Fan beam estimates

Let A be the self-adjoint free-beam fourth-derivative operator on the unit interval, on the domain of functions with four square-integrable weak derivatives and with second and third derivatives zero at both endpoints. Its two-dimensional kernel is the affine plane, and the rest of its spectrum lies above five hundred. Let H multiply by epsilon times t, where zero is less than epsilon and epsilon is less than one hundred. An orthonormal basis of the affine trial plane is given by one over square root of two times one minus square root of three times two t minus one, and the corresponding function with a plus sign. We can use their exact residual singular values to compare several subspace perturbation bounds.

Different Davis–Kahan estimates applied to the same beam model answer different questions. A stronger residual estimate can outweigh the choice of theorem, while largest-angle and Ky Fan bounds quantify different aspects of the subspace error.

## First use the unrecentered residual

Start with the reference operator zero on the affine trial plane. Since the unperturbed fourth derivative annihilates both trial functions, the residual is H applied to the frame. For this map the Gram matrix equals epsilon squared over thirty times the symmetric matrix with diagonal entries eleven minus square root of seventy-five and eleven plus square root of seventy-five, and both off-diagonal entries negative one. Its eigenvalues are epsilon squared over thirty times eleven plus or minus square root of seventy-six. Thus the top singular value is epsilon times the square root of the quotient of eleven plus square root of seventy-six by thirty, a little smaller than point eight one one.

The high part of the perturbed beam has spectrum above five hundred. Because the trial reference value is zero, the ordered gap is at least five hundred. The directed sine theorem gives five hundred times the norm of the sine operator no greater than the residual operator norm.

Divide through. The largest sine of a principal angle is smaller than point eight one one divided by five hundred times epsilon. That is the printed bound, sine theta one less than point zero zero one six two two times epsilon, equation nine point one.

Why call it the largest principal angle? In the relevant range, the principal sine increases with the angle. Operator norm selects the largest singular value of the sine operator, hence the largest angle.

The bound assumes epsilon is positive and below one hundred. At epsilon equal to ten, this initial result says sine theta one is below about point zero one six two two. It is a useful certificate, but we can improve it considerably.

## What a two-term Ky Fan norm adds

Operator norm sees only the largest singular value. We also know the second singular value of the initial residual. Its coefficient is the square root of eleven minus square root of seventy-six, divided by thirty, about point two seven six.

Add the two coefficients and divide by five hundred. The result is below point zero zero two one eight times epsilon. So the sum of the sines of the two principal angles is bounded by that quantity. This is the paper's equation nine point three.

The Ky Fan estimate bounds the sum of the two principal sines, not each sine by half that sum; their contributions can be unequal. What the inequality controls is their cumulative rotation, measured by the first two singular values of the directed sine map.

Why can we make that inference? The Hilbert-space singular-value comparison supports a compatible invariant norm. The Ky Fan two-norm adds the two largest singular values, and both the residual and the sine map have at most two nonzero singular values because their source is two-dimensional.

The largest-angle and two-term results are complementary. If we need a guarantee for the worst single direction, the operator norm is natural. If we need the total leakage of a two-dimensional cluster, the Ky Fan sum carries more information.

## The doubled-angle alternative

The paper next applies the sine-two-theta theorem. This theorem compares two reducing subspaces of the unperturbed and perturbed operators, not simply one trial residual. In the beam example the perturbation has norm at most epsilon and the relevant separation is five hundred.

The ambient sine-two-theta estimate gives sine of twice the largest angle less than point zero zero four times epsilon. Its two-term Ky Fan version gives the sum of the doubled sines less than point zero zero eight times epsilon. These are equations nine point two and nine point four.

At first sight these coefficients look larger than the single-angle sine coefficient. But the left sides are different functions: sine of twice an angle is approximately twice the sine of that angle for small angles.

The double-angle estimate has a branch ambiguity. The sine of twice an angle can be small near zero degrees or near ninety degrees. A separate spectral-selection or small-angle argument is needed before converting it into a unique small-angle certificate. In the beam problem, the low spectral cluster is selected across a large gap, and its continuity under bounded perturbation supplies the intended branch.

The doubled-angle theorem is valuable because it uses ambient off-diagonal structure. It is not automatically the sharpest numerical estimate for this particular data.

## Recenter at the Ritz matrix

Now use the actual Rayleigh-Ritz compression rather than zero. Its diagonal entries are epsilon over two times one minus one over square root of three, and epsilon over two times one plus one over square root of three. Subtracting the compressed action from the full action leaves a rank-one residual, whose Gram matrix is epsilon squared over thirty times the matrix with diagonal entries one and off-diagonal entries negative one. The only nonzero singular value is epsilon divided by square root of fifteen.

The separation is no longer the full five hundred because the trial Ritz values are positive. But a valid lower gap is five hundred minus point seven eight eight seven times epsilon. This remains positive for the stipulated parameter range, since epsilon is below one hundred.

Apply the ordered-gap tangent theorem. Tangent of the largest principal angle is bounded by epsilon divided by square root of fifteen, divided again by five hundred minus point seven eight eight seven epsilon.

Factor five hundred out of the denominator. The resulting coefficient is approximately point zero zero zero five one six four times epsilon, divided by one minus point zero zero one five seven seven four times epsilon.

That is equation nine point six. Because the recentered residual has rank one, its operator norm and its two-term Ky Fan norm agree. Therefore the same right-hand side controls the sum of the two principal tangents, as long as the theorem is applied with that norm.

Take epsilon equal to ten again. The bound is roughly point zero zero five two five, markedly smaller than the initial sine bound of point zero one six two two. The improvement comes from removing the part of H that acts within the trial plane. We spend a little of the spectral gap but reduce the residual by a much larger proportion.

## A recentered doubled-tangent bound

There is also a tangent-two-theta estimate. Use the perturbed operator's compression to the complementary trial space. The complement remains above five hundred because the original beam is nonnegative with its high spectrum above five hundred and the perturbation is positive.

The corresponding bound for tangent of twice the largest angle has twice the numerator of the tangent estimate. Thus the paper obtains point zero zero one zero three two eight times epsilon, divided by the same denominator, one minus point zero zero one five seven seven four times epsilon.

This is equation nine point seven. As before, there is a two-term Ky Fan version with the same scalar right-hand side because the residual responsible for the estimate is rank one.

The sharp tangent-two-theta estimate applies to selected matched spectral branches under the required off-diagonal conditions. In this example, those conditions are justified by the low-high spectral split, not by the numerical fraction alone.

## Comparison at one concrete parameter

With epsilon ten, the initial largest-angle sine bound is about point zero one six two two, while the recentered tangent bound is about point zero zero five two five. The initial doubled-sine bound is point zero four, while the recentered doubled-tangent bound is about point zero one zero five.

These are not four numbers measuring an identical quantity. Yet when the angles are small, they give a coherent picture, and the recentered estimates use the information that the Ritz matrix contains.

There is one more distinction. All the results so far concern the two-dimensional low spectral subspace relative to the trial plane. They do not tell us which of the two trial functions is closest to which individual perturbed eigenvector. A basis can rotate substantially inside a plane even if the plane itself hardly moves.

To estimate an individual eigenvector rather than the low spectral plane, an additional in-plane rotation must be controlled. A two-by-two Schur complement separates that rotation from the leakage out of the trial plane.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For \(0<\varepsilon<100\), Section 9 states the rigorous decimal envelopes
\[
\sin\theta_1<0.001622\varepsilon,\qquad
\sin\theta_1+\sin\theta_2<0.00218\varepsilon,
\]
\[
\sin2\theta_1<0.004\varepsilon,\qquad
\sin2\theta_1+\sin2\theta_2<0.008\varepsilon,
\]
\[
\tan\theta_1<\frac{0.0005164\varepsilon}{1-0.0015774\varepsilon},\qquad
\tan2\theta_1<\frac{0.0010328\varepsilon}{1-0.0015774\varepsilon}.
\]
The companion two-term Ky Fan tangent bounds use the same RHS as their respective operator-norm estimates. The source-facing Lean statements invoke the genuine free-beam realization; the bound-conversion lemmas are separately proved using exact radicals and rational comparisons.

## Exact Lean declaration excerpts


**`equation_9_1_freeBeam`.** The source-facing complex-model wrapper supplies the printed largest-sine bound for the genuine beam realization; the repository also has a separately established real model. Epsilon is positive and less than 100.

`DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` — `equation_9_1_freeBeam` (exact declaration header; proof body omitted):

```lean
theorem equation_9_1_freeBeam (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTheta ε < (811 : ℝ) / 500000 * ε :=
```


**`equation_9_3_freeBeam`.** The two-term Ky Fan inequality bounds the *sum* of both principal sines, not each separately by half.

`DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` — `equation_9_3_freeBeam` (exact declaration header; proof body omitted):

```lean
theorem equation_9_3_freeBeam (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinThetaSum ε < (109 : ℝ) / 50000 * ε :=
```


**`equation_9_6_freeBeam`.** Both operator-norm tangent and Ky Fan two-term tangent bounds are included in this theorem conclusion.

`DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` — `equation_9_6_freeBeam` (exact declaration header; proof body omitted):

```lean
theorem equation_9_6_freeBeam (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) ∧
      beamTanThetaSum ε
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
```


**`equation_9_7_freeBeam`.** The doubled-tangent inequalities come from the specific source-model branch with its high block and comparison hypotheses already discharged upstream.

`DavisKahan/Sources/DavisKahan1970/Section9/NumericalResults.lean` — `equation_9_7_freeBeam` (exact declaration header; proof body omitted):

```lean
theorem equation_9_7_freeBeam (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoTheta ε
        < ((1291 : ℝ) / 1250000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) ∧
      beamTanTwoThetaSum ε
        < ((1291 : ℝ) / 1250000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
```
