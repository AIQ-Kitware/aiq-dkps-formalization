# 091000 — Yosida approximation and bounded truncations

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `082000` spectral cutoffs, `087000` Cayley transforms, `088000` unbounded spectral calculus, `090000` semibounded forms. **Next:** `092000` one-parameter unitary groups.

<!-- BEGIN SPOKEN LECTURE -->

# Replace an unbounded generator without losing its geometry

Unbounded operators cause a problem whenever a proof uses an ordinary matrix exponential, a power series in operator norm, or differentiation of an operator-valued function. Those operations work naturally for bounded operators. We need a way to approximate an unbounded self-adjoint operator by bounded self-adjoint ones and then recover the original action on its correct domain.

Today we will develop two approximations: spectral truncation and the symmetric Yosida approximation. Their formulas differ, but their purpose is the same. They preserve the self-adjoint structure while approaching the original operator on domain vectors.

## A first idea: cut off large spectral values

Let A be self-adjoint. For a positive radius R, let P R project onto spectral values between negative R and positive R.

Define T R to act as A on that band and as zero outside the band. Since its spectral multiplier is bounded by R, T R is a bounded self-adjoint operator on the entire Hilbert space.

If x belongs to D of A, the spectral theorem shows that T R x approaches A x. The squared norm of the difference is the integral of lambda squared over the spectral region outside the band. Because x is in D of A, that integrand is integrable, and its tail tends to zero.

But this convergence is strong on D of A. It is not convergence in operator norm to A, because A does not belong to the space of bounded operators if it is genuinely unbounded.

There is also an issue with the action on the complement of the cutoff. Setting it to zero may destroy an important lower form bound. If A has spectrum above five, for example, T R has zero on the cutoff complement, so it is no longer bounded below by five there.

We can repair that by filling the complement with a real constant. Define the filled truncation as T R plus a times identity minus P R. It agrees with A on the retained band, acts as scalar a outside, and remains bounded and self-adjoint.

Choosing a appropriately can preserve a lower or upper bound. This is useful when the final estimate depends on ordered spectra.

## A smoother regularization

Instead of deleting high spectral frequencies abruptly, apply the scalar function f n of lambda defined as N squared times lambda, divided by N squared plus lambda squared.

For each fixed positive N, this function is real and bounded. Its absolute value is at most N divided by two, since twice N times the absolute value of lambda cannot exceed N squared plus lambda squared.

The functional calculus therefore gives a bounded self-adjoint operator A N. Every input vector is legal for A N.

For a fixed spectral value lambda, the multiplier approaches lambda as N grows. Moreover its absolute value never exceeds the absolute value of lambda.

If x lies in D of A, the difference between the multiplier and lambda, squared and integrated against the spectral measure of x, tends to zero by dominated convergence. The dominating function is a constant times lambda squared, which is integrable precisely because x is in D of A.

Thus A N x approaches A x for every domain vector. The regularization is bounded at each stage, self-adjoint at each stage, and consistent with A on the original domain in the limit.

There is no claim that the norms of A N remain bounded independently of N. In fact their universal bound N divided by two grows, as it must if A is truly unbounded.

## A diagonal worked example

Let A multiply the N-th coordinate of an ell-two sequence by N. To avoid confusing the coordinate index with the approximation parameter, call the approximation parameter R.

On coordinate N, the regularized eigenvalue is R squared times N divided by R squared plus N squared.

For N much smaller than R, this is close to N. For N much larger than R, it becomes small, approximately R squared divided by N. The regularizer preserves low-frequency behavior while controlling the extreme high-frequency part.

Choose a vector with N-th coordinate one divided by N squared. This vector lies in D of A, because the coordinates of A x are one divided by N, which are square summable.

For each fixed coordinate the regularized output tends to one divided by N. The dominated-convergence argument shows convergence in the norm of the entire sequence, not merely coordinate by coordinate.

Choose instead the vector with N-th coordinate one divided by N. It belongs to ell two but not D of A. Each A R can still act on it, because A R is bounded. Yet the outputs cannot converge in ell two to a finite vector that represents A x. If they converged, closedness of A and the appropriate spectral convergence would force x into D of A, which it is not.

That illustrates the role of the domain: regularization defines legal approximating actions on all vectors, but convergence to the original unbounded action is guaranteed only where that action exists.

## Why self-adjointness survives

The symmetric Yosida multiplier is a real function of a self-adjoint operator. Applying real-valued bounded functional calculus gives a self-adjoint bounded operator automatically.

That property is not an incidental convenience. For every real time t, multiply A R by the imaginary unit and by t, then exponentiate. The result is unitary, because its exponent is skew-adjoint.

We can use the bounded exponential power series and the group law without having to confront the unbounded operator exponential directly. Each R produces a complete one-parameter unitary group.

There is a second benefit: any two Yosida approximants are functions of the same operator A. Therefore they commute. Their exponentials commute as well, and the comparison of two approximating flows becomes much simpler.

## Controlling the difference between flows

Let U R of t denote the unitary exponential of imaginary t times A R. For a vector x, compare U R of t x with U S of t x for two regularization parameters R and S.

Because the generators commute, we can differentiate an interpolating product of exponentials and integrate the derivative. The resulting Duhamel estimate bounds the length of the difference between the two flows by the absolute value of t times the length of A R x minus A S x.

We have already shown that the approximating generators form a Cauchy sequence when applied to a vector in D of A. The Duhamel estimate therefore makes the approximating flows Cauchy on that dense domain.

To extend convergence to an arbitrary vector y in H, approximate y by a domain vector x. Since each flow is unitary, replacing y by x causes an error of at most the distance between y and x. Do it for both flows and use the Cauchy estimate at x. The two approximation errors can be made as small as desired.

Completeness of H then produces a limit flow on every vector, even when the original generator is not defined there.

## Strong limits versus norm limits

The convergence just constructed is in the Hilbert-space norm for each fixed vector. This is strong operator convergence. We should not upgrade it to operator-norm convergence without a separate argument.

The distinction is visible in the diagonal example. High-frequency coordinates can rotate extremely rapidly under the unitary group. For each fixed vector, their total squared mass becomes small in the tail, so strong convergence and strong continuity remain possible. But a norm estimate that takes the supremum over all unit vectors can always select a rapidly rotating high-frequency basis vector.

The next lecture will build the limiting unitary group and identify its self-adjoint generator exactly. Yosida regularization supplies the bounded approximants that make the construction rigorous.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

A symmetric Yosida regularizer for a self-adjoint \(A\) has spectral symbol \(f_R(\lambda)=R^2\lambda/(R^2+\lambda^2)\). The bound \(|f_R(\lambda)|\le R/2\) makes \(A_R=f_R(A)\) a bounded self-adjoint operator, while \(|f_R(\lambda)|\le|\lambda|\) gives \(A_Rx\to Ax\) for \(x\in D(A)\). The unitary flow \(U_R(t)=e^{itA_R}\) is bounded and preserves norms. A Duhamel comparison of commuting approximants gives \(\|U_R(t)x-U_S(t)x\|\le|t|\|(A_R-A_S)x\|\). A filled truncation \(T_R+a(I-P_R)\) can preserve spectral lower/upper bounds on the cutoff complement. Convergence of generators is only asserted on \(D(A)\); the unitary flow limit exists strongly on all of \(H\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` — `yosidaApproximantSymSA`:

```lean
noncomputable def yosidaApproximantSymSA (hA : IsSelfAdjoint A) (n : ℕ+) (t : ℝ) :
    selfAdjoint (H →L[ℂ] H) :=
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` — `norm_expApprox_sub_le`:

```lean
theorem norm_expApprox_sub_le (hA : IsSelfAdjoint A) (m n : ℕ+) (t : ℝ) (ψ : H) :
    ‖expApprox hA m t ψ - expApprox hA n t ψ‖
      ≤ |t| * ‖A.symmetricYosidaApproximation (m : ℝ) ψ -
        A.symmetricYosidaApproximation (n : ℝ) ψ‖ := by
```

`DavisKahan/Sylvester/FilledTruncation.lean` — `filledTruncation`:

```lean
noncomputable def filledTruncation
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H →ₗ.[𝕜] H)
    (hA : IsSelfAdjoint A)
    (Pcut : SpectralCutoffInterface A hA)
    (Tcut : BoundedTruncationInterface A hA Pcut)
    (a τ : ℝ) : H →L[𝕜] H :=
```

`DavisKahan/Sylvester/FilledTruncation.lean` — `filledTruncation_lowerBound`:

```lean
theorem filledTruncation_lowerBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H →ₗ.[𝕜] H)
    (hA : IsSelfAdjoint A)
    (Pcut : SpectralCutoffInterface A hA)
    (Tcut : BoundedTruncationInterface A hA Pcut)
    {a τ : ℝ} (hτ : 0 ≤ τ)
    (ha : TauCeti.LinearPMap.SemiboundedBelow A a) :
    ∀ x, a * ‖x‖ ^ 2 ≤
      RCLike.re ⟪filledTruncation A hA Pcut Tcut a τ x, x⟫_𝕜 := by
```


**Type and hypothesis map.** `n : ℕ+` is the strictly positive regularization index; `symmetricYosidaApproximation` is a bounded continuous linear operator assembled from resolvents. `yosidaApproximantSymSA` packages its real-time multiple as an element of the self-adjoint subspace. `norm_expApprox_sub_le` is the exact vectorwise Duhamel estimate used for convergence. `filledTruncation` takes an explicit cutoff interface and the scalar used outside the spectral band; the `filledTruncation_lowerBound` theorem checks its form lower bound on all input vectors. The two families serve different approximation tasks and should not be conflated.

**Scope:** The snippets cover bounded symmetric approximants, their exponentials, the Cauchy/Duhamel estimate, and the filled-truncation construction. The scalar spectral symbol is supplied as mathematical explanation; the Lean snippets use the existing `symmetricYosidaApproximation` API rather than expanding its internal definition. These are source-verified excerpts, not new Lean code.
