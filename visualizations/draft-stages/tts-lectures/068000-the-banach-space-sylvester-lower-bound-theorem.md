# 068000 — The Banach-space Sylvester lower-bound theorem

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `004000–005000` bounded operators and their algebra; `057000–058000` compatible operator norms; `064000–067000` Sylvester invertibility and spectral separation. **Next:** norm dependence of Sylvester bounds.

<!-- BEGIN SPOKEN LECTURE -->

# A constant-one bound from a bounded inverse

The Sylvester equation asks for an operator X satisfying A X minus X B equals C. In a Banach space, we cannot generally diagonalize A and B, yet we can still estimate X by rearranging the equation whenever one coefficient has a bounded inverse and the other is sufficiently small in comparison. Davis and Kahan state this as Theorem five point one. The theorem uses a bounded inverse of A, a bound on B, and a compatible norm on the operators that connect their spaces. These hypotheses create a contraction in the Sylvester equation.

Our goal is to derive the estimate, explain what compatible means, distinguish the printed statement from a stronger reusable variant, and connect the result to spectral intervals without assuming that mere disjointness is enough.

## Set up two Banach spaces

Let X and Y be complex or real Banach spaces. The letter X here names the input space, so to avoid confusion call the unknown operator T. It maps X into Y.

Let A be a bounded linear operator on Y, and B a bounded linear operator on X. Let C also map X to Y. We want to solve A T minus T B equals C.

Assume there are real numbers gamma and delta, with gamma nonnegative and delta strictly positive. Suppose the norm of B is at most gamma.

Now assume A has a bounded two-sided inverse, with inverse norm at most one divided by gamma plus delta.

Those inequalities encode an asymmetry. B is small compared with the scale gamma; the inverse of A is small enough that multiplying by B leaves a contraction ratio less than one.

The strict extra margin is delta. Our final lower bound will contain exactly that margin.

## What a compatible operator norm means

The standard operator norm of T is the largest possible output norm on an input of norm one. But the theorem is designed to work for more general sizes of cross-space operators.

Call such a size N of T. It must obey the norm-like rules: it is nonnegative, zero only at zero, homogeneous under scalar multiplication, and subadditive under addition.

The additional condition is compatibility with contractions. If L acts on Y and R acts on X, and both have operator norm at most one, then composing T as L T R cannot increase N of T.

This one condition implies the general two-sided ideal inequality. For arbitrary bounded L and R, normalize each nonzero one by its operator norm so that the normalized maps are contractions. Apply compatibility, then restore their scaling factors. We obtain that N of L T R is at most the norm of L times N of T times the norm of R.

If either multiplier is zero, the same inequality is immediate. This proves the ideal estimate in every case.

The ordinary operator norm satisfies compatibility by submultiplicativity. Many singular-value-based norms do as well in finite-dimensional Hilbert spaces. On general Banach spaces we cannot define a Frobenius norm from an arbitrary basis and expect the same properties, so the theorem states compatibility explicitly rather than listing all possible examples.

## Rearrange the Sylvester equation

Start from A T minus T B equals C. Move the second term to the right: A T equals C plus T B.

Now apply the bounded inverse of A on the left. Because that inverse cancels A, we get an exact fixed-point identity: T equals A inverse C plus A inverse T B.

This identity says that T is a fixed point of an affine map. One part depends only on C; the other sends T to A inverse T B.

We can estimate its effect using compatibility. The size of A inverse C is at most the norm of A inverse times N of C. The size of A inverse T B is at most the inverse norm times N of T times the norm of B.

Apply the triangle inequality to the fixed-point identity. We obtain N of T at most inverse norm times N of C, plus inverse norm times B norm times N of T.

Now insert the hypotheses. The inverse norm is at most one over gamma plus delta, and B norm is at most gamma. Therefore N of T is at most N of C divided by gamma plus delta, plus gamma over gamma plus delta times N of T.

Multiply through by gamma plus delta. The left is gamma plus delta times N of T. The right is N of C plus gamma times N of T.

Subtract gamma times N of T from both sides. The gamma terms cancel, leaving delta times N of T at most N of C.

That is Theorem five point one's principal estimate. The constant is exactly one.

## Why the hypothesis is stronger than spectral disjointness

The existence theorem we just studied needed disjoint spectra, but it did not impose a size bound on the resolvents that enter its contour formula.

Here we demand a specific bound on the inverse of A and on the norm of B. This is much more quantitative.

For arbitrary Banach operators, knowing that zero lies some distance away from A's spectrum does not in general imply that the norm of A inverse is the reciprocal of that distance. Nonnormal behavior can make inverses much larger. Thus we cannot derive the current theorem solely from a picture of two separated spectra.

In a self-adjoint Hilbert setting, the spectral theorem does give the needed inverse norm bounds. That is one important bridge from geometric spectral separation to this Banach-space argument.

## Move the spectral picture by a common shift

An important trick is that the Sylvester expression does not change if we subtract the same scalar c from both A and B.

Expand the shifted equation. On the left, A minus c identity, applied to T, gives A T minus c T. On the right, T followed by B minus c identity gives T B minus c T. Subtracting cancels the two scalar terms.

So A T minus T B equals the same expression built from A minus c identity and B minus c identity.

Suppose B is self-adjoint with spectrum inside the interval from c minus gamma to c plus gamma. Then the norm of B minus c identity is at most gamma.

Suppose A is self-adjoint and its spectrum lies outside the larger open interval centered at c with radius gamma plus delta. Then A minus c identity is invertible, and its inverse norm is at most one over gamma plus delta.

The Banach-space estimate applies to these shifted operators. Therefore delta times N of T is at most N of C.

This is the interval-versus-exterior configuration: one spectral block occupies a bounded interval, while the other avoids a surrounding gap on both sides. Unlike the purely ordered configuration, the exterior spectrum may lie to the left and right simultaneously.

## A simple example where order is absent

Let B be the scalar zero operator and A the diagonal matrix with entries negative two and positive two. Choose gamma equal to zero and delta equal to two.

B has norm zero. The inverse of A is diagonal with entries negative one half and positive one half, so its operator norm is one half. That equals one divided by gamma plus delta.

If C is any column with two entries, the solution is simply A inverse C. Its norm is exactly half the norm of C, because both diagonal entries of A inverse have absolute value one half.

This achieves the constant-one bound even though A's spectrum lies on both sides of B's spectrum. Ordered separation was not needed; a suitably bounded inverse was enough.

## A one-sided inverse is sufficient for the estimate

Read the fixed-point proof again. We used only an operator L satisfying L A equals the identity, and a norm bound on L. We never used A L equals the identity.

The inequality therefore needs only a bounded left inverse in this setting, not a two-sided inverse. When comparing it with a statement formulated using a genuine inverse, keep the hypotheses distinct.

On arbitrary Banach spaces, a lower bound on A by itself need not give an everywhere-defined bounded left inverse. The range of A may fail to be complemented. Therefore the reusable theorem assumes actual left-inverse data rather than silently manufacturing it from an inequality on vectors.

The lower bound therefore requires the stated left-inverse hypotheses; a norm lower bound alone does not supply that structure on a general Banach space.

## Does this theorem itself prove existence?

The inequality we have derived applies to any T and C satisfying the Sylvester equation. It proves a lower bound for the Sylvester operator and, in particular, uniqueness: if C is zero, the estimate forces T to be zero.

Under the bounded inverse hypotheses, we can also prove existence by a separate Neumann-series argument. Define the linear map that sends T to A inverse T B. Its operator norm is at most gamma divided by gamma plus delta, strictly less than one. Repeated application therefore produces a convergent geometric series.

Starting from A inverse C, sum its successive images under that contraction. The series converges in the complete space of bounded cross-operators, and the sum solves the fixed-point equation. Thus existence follows as an additional argument.

The estimate attributed to Theorem five point one concerns a solution that is already given. Existence and uniqueness of a solution require additional arguments, and should not be inferred from this inequality alone.

## Reconstruct the argument

There are only three algebraic moves to remember. First, shift both diagonal blocks by the same scalar when useful. Second, solve for T using a bounded left inverse of A. Third, use the two-sided ideal inequality and collect the T terms.

The final estimate has no dimension factor and no reference to eigenvectors. That is why it is so useful when a perturbation argument passes from a finite matrix to a Banach-space operator setting.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Davis–Kahan (1970), Theorem 5.1, in its printed inverse formulation: for \(T,C\in\mathcal B(X,Y)\), \(AT-TB=C\), and a compatible cross-operator norm \(N\), assume
\[
\gamma\ge0,\quad\delta>0,\quad\|B\|\le\gamma,\quad
A^{-1}\in\mathcal B(Y),\quad\|A^{-1}\|\le(\gamma+\delta)^{-1}.
\]
Then
\[
\delta N(T)\le N(C).
\]
The fixed point \(T=A^{-1}C+A^{-1}TB\) and the ideal inequality give
\[
N(T)\le(\gamma+\delta)^{-1}N(C)
+\gamma(\gamma+\delta)^{-1}N(T).
\]
The reusable strengthened theorem needs only a *bounded left inverse*; the printed statement includes a two-sided inverse. A lower bound \(\|Ay\|\ge c\|y\|\) on an arbitrary Banach space need not provide a bounded everywhere-defined left inverse without further hypotheses.

**Lean bridge (verbatim source excerpts).**

`DavisKahan/Sources/DavisKahan1970/Section5BanachSylvester.lean` — `theorem5_1_banach_sylvester_exact`:

```lean
theorem theorem5_1_banach_sylvester_exact
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A Ainv : Y →L[𝕜] Y) (B : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id 𝕜 Y)
    (_hAinv_right : A ∘L Ainv = ContinuousLinearMap.id 𝕜 Y)
    (hAinv_norm : ‖Ainv‖ ≤ (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
```

This is the printed two-sided inverse hypothesis: `Ainv` cancels `A` on both sides, `‖Ainv‖ ≤ (gamma + delta)⁻¹`, `‖B‖ ≤ gamma`, and `N` is a compatible cross-operator norm.

`DavisKahan/Sources/DavisKahan1970/Section5BanachSylvester.lean` — `theorem5_1_banach_sylvester`:

```lean
theorem theorem5_1_banach_sylvester
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A : Y →L[𝕜] Y) (B : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hleft : BoundedLeftInverseData A (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
```

The reusable result only needs the explicitly supplied **bounded left inverse** data; that is a stronger theorem than the printed version. Neither theorem requires an inner-product structure.

