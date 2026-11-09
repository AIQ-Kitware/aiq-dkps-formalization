# 066000 — Unitary and semigroup representations

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `039000–041000` exponentials and unitary flows; `063000–065000` Sylvester equations and ordered semigroups. **Next:** Rosenblum's contour method.

<!-- BEGIN SPOKEN LECTURE -->

# Two ways to transport a matrix through time

An ordered spectral gap permits a Sylvester equation to be solved by integrating decaying exponentials. For interlaced but separated spectra, the differences do not all share a sign, so we need a different construction. We study a related construction that works when the spectra are separated but their differences may have either sign.

The key change is to use unitary groups: exponentials with an imaginary unit in the exponent. These produce oscillations rather than decay. Then a scalar Fourier multiplier will turn each oscillation back into the reciprocal of its spectral difference.

We will derive the orbit identities before stating the multiplier construction. That is the mathematical reason the method works.

## The Sylvester orbit

Let A and B be bounded self-adjoint operators on complex Hilbert spaces. Let C be a bounded map from the space on which B acts into the space on which A acts.

For each real time t, define an operator U of t by exponentiating i times t times A. Define V of t using B the same way. Because the generators are self-adjoint, U and V are unitary: they preserve lengths and have their adjoints as inverses.

Now transport C by applying U of t on the left and the inverse of V of t on the right. Call the result F of t.

At time zero, both unitary maps are identities, so F of zero equals C. At any other time, F describes how C looks after a left and right unitary evolution.

We should derive its differential equation. Differentiate the exponential of i t A: its derivative is i A times that exponential. Differentiate the inverse B evolution: its derivative is negative i times the exponential followed by B. Apply the product rule.

The derivative of F is i times A F minus F B. In words, the Sylvester operator is the infinitesimal generator of the left-right transport.

If C happened to be a solution X of a homogeneous Sylvester equation, the derivative would vanish, and the orbit would be constant. That observation is another path to uniqueness under spectral separation.

## Check the orbit in diagonal coordinates

Assume for the moment that A and B are diagonal, with real eigenvalues a and b in the corresponding positions. On the matrix entry joining a to b, left unitary evolution multiplies by the exponential of i t a. Right inverse evolution multiplies by the exponential of negative i t b.

The product is the exponential of i t times a minus b. Each matrix coefficient therefore oscillates with frequency equal to its spectral difference.

Different entries can oscillate clockwise or counterclockwise depending on the sign of the difference. Unlike the ordered semigroup, there is no single exponential decay envelope.

This is why simply integrating F over positive time does not give a convergent Sylvester inverse in general. We need a weight whose oscillatory integral has exactly the reciprocal-frequency response we want.

## A scalar reciprocal multiplier

Suppose every absolute difference between a spectral value of A and one of B is at least a positive number delta. We want an integrable complex-valued function of time, call it mu, with this property: integrate mu of t times the exponential of i t omega over all real times, and the result is one over omega whenever the absolute value of omega is at least delta.

Think of the time variable as an input to the Fourier transform. We prescribe the transform of mu away from a forbidden interval around zero. Inside that interval, we have freedom, because no spectral difference we need to invert can occur there.

That freedom matters. The function one over frequency is singular at zero, and its naive inverse Fourier transform cannot be used as an absolutely integrable weight. By modifying the desired transform inside the spectral gap, we can obtain an integrable time-domain multiplier.

A scaled reciprocal Fourier kernel can be chosen so that its Fourier multiplier equals the inverse of a spectral difference on the separated sets. Its absolute integral equals pi divided by twice the gap, giving the corresponding operator-norm constant.

## Build the operator inverse

Return to the operator orbit of C. Multiply it by mu of t and integrate over all real t. Call the resulting operator Y.

In diagonal coordinates, the entry of Y joining eigenvalues a and b is the entry of C times the integral of mu of t times the exponential of i t times a minus b. The multiplier property evaluates this integral as one divided by a minus b.

Therefore the entry of Y is the entry of C divided by the spectral difference. We have reconstructed the unique entrywise Sylvester solution.

This is more than a compact notation for the finite calculation. The expression is basis independent, and its integrand is defined directly in the space of bounded operators.

Because U of t and V of t are unitary, the operator norm of their composition with C equals the operator norm of C. Multiplying by mu scales the norm by the absolute value of mu.

Thus the integrand has norm at most the absolute value of mu times the norm of C. The kernel is integrable, so Y exists as a Bochner integral in the complete normed space of bounded operators.

Apply the norm-of-integral inequality. The norm of Y is at most the integral of the absolute value of mu, multiplied by the norm of C. The exact mass of the chosen multiplier gives pi over two delta times the norm of C.

We have obtained an operator-norm bound for arbitrary pairwise-separated self-adjoint spectra. Its constant is pi over two, rather than the constant one obtained from a one-sided spectral ordering.

## Why the infinite-dimensional argument needs care

In finite dimensions we checked every coefficient in eigenbases. But a bounded self-adjoint operator on an infinite-dimensional Hilbert space may have continuous spectrum and no orthonormal basis of eigenvectors.

We cannot write an entrywise sum over eigenvalues and pretend it still covers every operator. Instead, the spectral theorem lets us approximate each self-adjoint operator by a finite spectral step operator: a finite linear combination of spectral projections, with coefficients chosen from the original spectrum.

For these finite spectral steps, the multiplier identity applies block by block. The approximations converge in operator norm. Their unitary evolutions converge at each fixed time, and the integrable majorant supplied by mu controls the limit under the integral.

Dominated convergence passes the reconstruction formula from spectral truncations to the original operators. Uniform integrable bounds on the approximating integrands justify taking the limit.

It is important that the approximate spectral representatives remain in the original spectra. Otherwise approximation might accidentally shrink the separation and invalidate the reciprocal-frequency formula.

## How the semigroup and unitary methods differ

Let us compare the two integral constructions.

When A is entirely above B by delta, the semigroup integrand decays as the exponential of negative delta times time. We integrate only over nonnegative times, and the mass of the scalar envelope is one over delta.

For general pairwise-separated spectra, some spectral differences are positive and others negative. A single decaying semigroup cannot treat them all. The unitary representation works with both signs by oscillating over all real times and inserting a Fourier multiplier. The multiplier's absolute mass produces pi over two delta.

The difference in constants comes from the geometry of the spectral configurations and the analytic representation used. We should never replace the second constant by the first without verifying stronger hypotheses.

## An example with both signs

Let A be diagonal with entries negative one and positive one, and B the one-dimensional zero operator. Let C be the column with entries two and three.

The spectral differences are negative one and positive one, so delta equals one. The Sylvester solution has entries negative two and positive three.

For the first coefficient, the unitary orbit oscillates with frequency negative one; for the second, with frequency positive one. The scalar multiplier returns negative one for the first reciprocal and positive one for the second, producing exactly the required signs.

No single choice of positive-time exponential decay using the same orientation can handle both entries. That is the simplest example of why the Fourier method adds genuine coverage.

## The generator viewpoint

There is a broader interpretation. The maps sending X to U of t X V of negative t form a one-parameter unitary group on the Hilbert space of Hilbert–Schmidt operators. Its generator is multiplication by i times the Sylvester operator.

In that Hilbert–Schmidt setting, the entire spectral calculation can be understood as functional calculus for a self-adjoint generator. This will later yield a sharper estimate in the square-summable operator norm.

For now, reconstruct the derivative of the orbit, verify the opposite-frequency example, and derive the norm estimate from the integral's absolute majorant. Those steps prepare us for another solution method that does not require self-adjointness at all: contour integration of resolvents.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For bounded self-adjoint \(A,B\), set \(U_A(t)=e^{itA}\), \(U_B(t)=e^{itB}\). Then
\[
\frac d{dt}\bigl(U_A(t)XU_B(-t)\bigr)
=iU_A(t)(AX-XB)U_B(-t).
\]
For \(\operatorname{dist}(\sigma(A),\sigma(B))\ge\delta>0\), choose \(\mu_\delta\in L^1(\mathbb R,\mathbb C)\) with
\[
\int_\mathbb R \mu_\delta(t)e^{it\omega}\,dt=\omega^{-1}
\quad(|\omega|\ge\delta),\qquad
\|\mu_\delta\|_{L^1}=\frac{\pi}{2\delta}.
\]
Then the separated-spectrum Sylvester inverse has representation
\[
X=\int_\mathbb R\mu_\delta(t)e^{itA}Ce^{-itB}\,dt,
\qquad \|X\|\le\frac\pi{2\delta}\|C\|.
\]
The source proves bounded infinite-dimensional reconstruction using finite spectral step approximations and dominated convergence. Compare `065000` for the better constant-one ordered case.

**Lean bridge (verbatim source excerpts).**

`DavisKahan/InfiniteDimensional/Sylvester/FourierSemigroup.lean` — `separatedSylvesterMultiplier_identity`:

```lean
theorem separatedSylvesterMultiplier_identity
    (d : ℝ) (hd : 0 < d) (a b : ℝ) (hab : d ≤ |a - b|) :
    (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
      Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
      (((a - b)⁻¹ : ℝ) : ℂ) := by
```

The complex Fourier identity supplies reciprocal spectral differences outside the gap.

`DavisKahan/InfiniteDimensional/Sylvester/FourierSemigroup.lean` — `l1_norm_separatedSylvesterMultiplier`:

```lean
theorem l1_norm_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) =
      Real.pi / (2 * d) := by
```

The exact scalar `L¹` mass produces the `π/2` constant; this is distinct from the ordered exponential estimate.

`DavisKahan/InfiniteDimensional/Sylvester/FourierSemigroup.lean` — `separatedSylvester_reconstruction_complex`:

```lean
theorem separatedSylvester_reconstruction_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
```

The complex Hilbert-space theorem reconstructs a known solution using unitary conjugation and a pairwise spectral gap. The finite spectral-step limit appears in its proof.

