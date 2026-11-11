# 091000 — Yosida approximation and bounded truncations

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `082000` spectral cutoffs, `087000` Cayley transforms, `088000` unbounded spectral calculus, `090000` semibounded forms. **Next:** `091250` resolvents and Yosida regularization.

<!-- BEGIN SPOKEN LECTURE -->

# How can bounded operators approximate an unbounded one?

Suppose an operator stretches different directions by different amounts. In a two-dimensional matrix, those stretches are always bounded: there is some largest possible amplification. But on an infinite-dimensional Hilbert space, the amplification might keep growing as we look at higher and higher directions.

That raises a practical problem. Many familiar constructions, such as taking an exponential by a power series, are easy for bounded operators. How can we use them when the operator we actually care about is unbounded?

The idea is to build bounded stand-ins. Each stand-in is allowed to have its own bound. As the approximations improve, those bounds may grow. What we want is that a fixed vector, on which the original operator is defined, eventually sees nearly the correct action.

There are two useful ways to do this for a self-adjoint operator: cut off its large spectral values, or replace them with a smooth, bounded function. The second construction is a symmetric form of Yosida approximation.

## Start with an infinite diagonal matrix

Consider ell two, the Hilbert space of infinite sequences whose squared magnitudes add to a finite number. Define an operator A as follows. Multiply the first coordinate by one, the second by two, the third by three, and in general multiply coordinate number N by N.

A is unbounded. A vector concentrated entirely in coordinate one hundred has length one, but A sends it to a vector of length one hundred. There is no single upper bound that works for every coordinate.

A also has a restricted domain. A sequence is allowed as an input precisely when, after multiplying its N-th coordinate by N, the result is still square summable.

For example, a sequence whose N-th entry is one divided by N squared belongs to the domain. After applying A, its entries are one divided by N, and their squared magnitudes still have a finite sum.

A sequence whose N-th entry is one divided by N is different. That input belongs to ell two, but applying A would produce the sequence of all ones. The output would not belong to ell two. So this vector lies outside the domain of A.

Keep those two sequences in mind. They will tell us exactly where approximation can and cannot recover the original operator.

## The simplest approximation: retain a finite spectral band

Imagine keeping only the first ten coordinate multipliers of our diagonal operator. The first coordinate is multiplied by one, the second by two, and so on through ten. Every coordinate after that is multiplied by zero.

This new operator is bounded. Its norm is ten. It is also self-adjoint, because its diagonal multipliers are real.

Increase the cutoff from ten to one hundred, then to a thousand. For a fixed coordinate, the approximation eventually acts exactly like A. For a vector in the domain of A, the entire output converges in Hilbert-space norm.

Why does the whole output converge? Because the difference is exactly the tail of A applied to that vector. We already required that A applied to the vector be square summable. The squared lengths of its tails must therefore approach zero.

That gives a straightforward spectral truncation scheme: keep the spectral values in a growing bounded interval, and replace everything outside that interval by zero. For a general self-adjoint operator, spectral projections perform the same operation without requiring an eigenvector basis.

There is, however, a drawback. Suppose the original operator has all its spectrum above five. Replacing the discarded part by zero introduces a new spectral value below five. An approximation meant to preserve a lower spectral bound has just destroyed it.

We can instead fill the discarded region with a chosen constant. On the retained spectral band, keep A. On its complement, use multiplication by a fixed real number, say five. That filled truncation is still bounded and self-adjoint. If the original spectrum lies above five, the filled operator does too.

So hard cutoffs give simple approximations, and filling the complement can preserve inequalities that matter to spectral-gap arguments.

## A smoother approximation

Hard truncation abruptly changes what happens at the cutoff. There is another construction that modifies every spectral value continuously.

Choose a positive scale R. For a spectral value s, replace s by the following number: R squared times s, divided by R squared plus s squared.

Let's use R equal to ten. The spectral value one becomes one hundred divided by one hundred and one, which is just under one. The spectral value ten becomes five. The spectral value one hundred becomes about zero point nine nine.

The last result deserves attention. This is not a clipping rule that stops at ten. Extremely large spectral values are suppressed toward zero. The rule faithfully approximates any fixed spectral value as R grows, but for a fixed R it controls the entire real line.

In fact, the magnitude of the modified value is never larger than R divided by two. At R equal to ten, the new operator has norm at most five, no matter how large the original spectral values become.

Apply this same scalar rule to the spectrum of A. The spectral theorem produces a bounded operator A sub R. Because the scalar rule is real-valued and A is self-adjoint, A sub R is self-adjoint as well.

This is called the symmetric Yosida regularization. Its formula is chosen because it has several useful properties at once: it is bounded, it preserves self-adjointness, and it approaches the original spectral value at each fixed location.

## What convergence actually means

For our diagonal example, take coordinate number N. The regularized multiplier is R squared times N divided by R squared plus N squared. As R increases without bound, that multiplier approaches N.

But convergence on each coordinate is not enough by itself. We need convergence of whole vectors in ell two.

Here is the key estimate. The magnitude of the regularized multiplier never exceeds the magnitude of the original spectral value. So when we subtract the original action from the regularized action, the size of the error on a spectral component is controlled by twice the original component's amplification.

If x belongs to the domain of A, the squares of those original amplified components have a finite sum. Dominated convergence then lets us pass from convergence at each spectral value to convergence in the norm of the whole Hilbert space.

Return to the sequence with N-th entry one divided by N squared. It belongs to the domain. The regularized outputs converge to the sequence with N-th entry one divided by N, which is exactly A applied to x.

Now use the sequence with N-th entry one divided by N. Every bounded approximant can act on it. But the outputs cannot converge to a vector in ell two. Their N-th coordinates approach one, so any coordinatewise limit would be the sequence of all ones, and that is not in ell two.

This is the domain boundary in action. Each approximation is defined everywhere. The original operator is recovered on its domain, not on arbitrary vectors.

We also should not expect convergence in operator norm. The norms of the approximants can grow with R, while a genuinely unbounded A has no finite operator norm to converge to. The meaningful statement is convergence of A sub R applied to each fixed domain vector.

## Why keeping self-adjointness helps

There is another reason to prefer the symmetric construction. A bounded self-adjoint operator can generate a unitary evolution. Multiply it by imaginary time and exponentiate. The resulting operator preserves the length of every vector.

For each R, the exponential of imaginary time times A sub R is a perfectly ordinary bounded-operator construction. Call this unitary evolution U sub R at time t.

Why should the evolutions approach one another? All our approximants come from scalar functions of the same operator A. They commute. When we compare two of their exponentials, we can interpolate between them and integrate the derivative.

The result is a useful estimate. On a vector x, the distance between the two evolved vectors is no greater than the absolute value of time multiplied by the length of the difference between the two approximate generators applied to x.

For a vector in the domain of A, that generator difference approaches zero. Consequently the unitary evolutions are Cauchy on domain vectors, uniformly over any fixed bounded interval of times.

But the domain of a self-adjoint operator is dense in the Hilbert space. Given an arbitrary vector, approximate it by a domain vector. Unitarity means that the approximation error never grows during evolution. So convergence extends from the dense domain to every vector in the Hilbert space.

Notice the change in what is defined. The original generator acts only on its domain. Yet the limiting unitary motion acts on every vector.

## The result to keep

Spectral truncation and symmetric Yosida regularization are two ways to replace an unbounded self-adjoint operator with bounded self-adjoint operators. Both recover the original action on vectors in its domain. Filled truncations can preserve one-sided spectral bounds; the symmetric regularizer is particularly convenient for building unitary evolutions.

The decisive distinction is between approximating the generator and approximating its evolution. Generator convergence is restricted to the original domain. The unitary evolutions, because they are bounded and preserve norms, can converge strongly on the entire Hilbert space.

That is how bounded tools can be used without pretending that an unbounded operator is defined everywhere.

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
