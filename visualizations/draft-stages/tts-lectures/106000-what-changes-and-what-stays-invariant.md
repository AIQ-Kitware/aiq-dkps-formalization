# 106000 — What changes and what stays invariant

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `026000` finite spectral theorem; `027000` Rayleigh quotients; `031000` spectral gaps; `042000` principal angles; `105000` proof-readiness assembly. **Next:** `107000` trial spaces, exact subspaces and residuals.

<!-- BEGIN SPOKEN LECTURE -->

# Why stable eigenvalues do not guarantee stable eigenvectors

Imagine a symmetric two-by-two matrix that multiplies the horizontal coordinate by zero and the vertical coordinate by four.

Its lower eigenvalue is zero, and its lower eigenvector points horizontally. Its upper eigenvalue is four, with a vertical eigenvector. There's a spectral gap of four.

Now change only the off-diagonal entries. Put a one in the upper-right corner and a one in the lower-left corner. We haven't changed either diagonal entry, but the eigenvectors are no longer horizontal and vertical.

The eigenvalues have changed too. Yet the numerical shifts are much smaller than the rotation of the eigenvectors might lead you to expect.

This is the central tension in spectral perturbation theory. We can control how far eigenvalues move using one kind of argument. Controlling which eigenspaces they belong to, and how those spaces rotate, requires additional information about spectral separation.

## Work through the two-level example

Call the original diagonal matrix A and the perturbed matrix B. Their difference H has zeros on the diagonal and ones off the diagonal.

The operator norm of H is one: it has eigenvalues one and negative one.

To find the eigenvalues of B, solve its characteristic equation. The answer is two minus the square root of five, and two plus the square root of five.

Numerically, those are about negative zero point two three six and four point two three six. Each eigenvalue has moved by about zero point two three six from its original value.

Now look at the lower eigenvector. Write it as a unit vector making an angle theta with the horizontal axis.

Its Rayleigh quotient under B is four times sine squared theta plus two times sine theta times cosine theta.

At an eigenvector, this expression is stationary. Differentiating gives an equation involving twice the angle: four times sine of twice theta plus two times cosine of twice theta equals zero.

The lower eigenvector therefore rotates downward by about thirteen point three degrees. More precisely, its angle is negative one half of the arctangent of one half.

The perturbation had operator norm one. The eigenvalues moved by about a quarter of a unit. The lower eigendirection turned by over thirteen degrees.

These measurements describe different aspects of the perturbation. A statement about eigenvalue displacement does not directly give an angle estimate.

## Why eigenvalues have a simple stability bound

For any unit vector x, the Rayleigh quotient of B differs from the Rayleigh quotient of A by the inner product of x with H x.

Cauchy–Schwarz bounds that difference in absolute value by the operator norm of H. So every unit vector's Rayleigh quotient changes by at most one in our example.

The min–max principle identifies each ordered eigenvalue of a Hermitian matrix by optimizing these Rayleigh quotients over subspaces of the appropriate dimension.

Since every candidate Rayleigh quotient changes by at most the same amount, the minima and maxima used by the min–max principle also change by at most that amount.

Therefore the k-th ordered eigenvalue of B differs from the k-th ordered eigenvalue of A by no more than the norm of H.

This is Weyl's perturbation bound for Hermitian matrices.

The argument remains true when eigenvalues coincide. That's useful for eigenvalue estimates, but coincident eigenvalues are precisely where an individual eigenvector may cease to be uniquely determined.

## Watch a subspace selection fail at a crossing

Take the original diagonal matrix with entries zero and four again.

Now introduce a parameter t between zero and one. Increase the first diagonal entry by five t, and decrease the second by five t.

The two eigenvalues are now five t and four minus five t.

At t equals zero, the lower eigenspace is horizontal. At t equals one, it is vertical.

Where does the switch happen? Set five t equal to four minus five t. The equality occurs at t equals two fifths. At that instant, both eigenvalues equal two, and the matrix is two times the identity.

Every direction is then an eigenvector. There is no distinguished one-dimensional lower eigenspace at the crossing.

Immediately before the crossing, choosing the lower eigenvalue selects the horizontal line. Immediately after, it selects the vertical line. Those lines are perpendicular.

Yet the two eigenvalue curves themselves are continuous functions of t.

This is an exact example of why tracking the lowest eigenvector can fail when a spectral gap closes. To follow an isolated subspace continuously, we need an isolation condition that remains valid along the perturbation.

## Sometimes the right object is a whole cluster

Consider a three-dimensional diagonal matrix with entries zero, zero, and ten.

The first two coordinate directions span a two-dimensional eigenspace. But there is no preferred pair of basis vectors inside it. Any rotation within that plane gives another legitimate orthonormal basis of the same eigenspace.

Now perturb only the upper-left two-by-two block. The individual eigenvectors in that block can rotate considerably, and the repeated zero eigenvalue can split.

As long as the perturbation doesn't couple that plane to the third coordinate, the plane itself stays exactly the same invariant subspace. Its orthogonal projection is unchanged.

That gives us a more stable object to track: the whole selected spectral subspace, represented by an orthogonal projection. Principal angles compare these subspaces without requiring us to match arbitrary eigenvector bases.

## Which gap do we actually need?

A spectral gap must be attached to two specified spectral sets.

In the plane example, if our target is the lower eigenspace, the important competing spectrum is the upper eigenvalue. The distance to that unwanted part influences how easily a vector can leak into the wrong eigenspace.

In more general problems, the chosen cluster might be an interval with unwanted spectrum on either side. In another problem, the two spectral sets might be ordered, with one entirely above the other.

Those arrangements support different operator estimates. Knowing only that two spectra don't intersect is weaker than knowing the ordered separation used by a particular Sylvester theorem.

Weyl's eigenvalue bound helps us determine whether an initially isolated cluster stays isolated under a sufficiently small perturbation. Once we know which cluster is selected, subspace perturbation theory asks how its projection changes.

## The residual measures one vector's failure to be invariant

There's a second way to approach the angle question, especially when we're given an approximate eigenvector rather than two complete matrices.

Let u be a unit trial vector and mu a proposed eigenvalue. Apply the operator to u and subtract mu times u. The result is the residual.

If the residual is zero, u is an exact eigenvector with eigenvalue mu. If the residual is small, u nearly satisfies that particular eigenvalue equation.

For the perturbed matrix B in our first example, take the original horizontal vector as a trial vector and choose mu equal to its Rayleigh quotient, which is zero. Applying B gives the vertical unit vector. The residual is therefore vertical with norm one.

That vertical error is the component trying to move us out of the original target direction.

But a zero residual does not by itself say that the vector is near the *selected* eigenspace. Return to the original diagonal matrix. The vertical unit vector has zero residual when paired with its own eigenvalue four. It is nevertheless perpendicular to the lower eigenspace.

We must specify the trial spectral value and separate it from the unwanted spectrum. The residual can then be converted into a complementary-coordinate equation, and a spectral-gap bound turns that equation into an angle estimate.

The conclusion is a precise distinction. Eigenvalues of self-adjoint matrices are stable in operator norm, by the min–max principle. Eigenspaces are stable under additional conditions that keep the selected spectral component isolated. A residual measures failure of an eigenvalue equation, while a suitable gap tells us which subspace that residual can control.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `B=A+H` with self-adjoint matrices. Courant–Fischer gives `|λ_k(B)-λ_k(A)| ≤ ‖H‖`, but no analogous subspace estimate follows without separating the selected spectral sets. For `A=diag(0,4)` and `H=[[0,1],[1,0]]`, the lower eigendirection rotates through `θ=-(1/2) arctan(1/2)` and eigenvalues become `2±√5`. For `A(t)=diag(5t,4-5t)`, the lower spectral subspace changes at the collision `t=2/5`.

The exact source-backed sharpness model below supplies a distinct planar perturbation model used by the sine theorem. It is an analogy, not a formalization of both examples in this lecture.

### Worked example: eigenvalue motion and subspace crossing

Let
\[
A=\begin{pmatrix}0&0\\0&4\end{pmatrix},\qquad
H=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad B=A+H.
\]
Then \(\|H\|=1\) and \(\sigma(B)=\{2-\sqrt5,2+\sqrt5\}\), so each ordered eigenvalue moves by \(\sqrt5-2\approx0.236\). The lower eigenvector makes angle \(\theta=-\tfrac12\arctan(1/2)\) with \(e_1\), approximately \(-13.28^\circ\).

For \(A(t)=\operatorname{diag}(5t,4-5t)\), the eigenvalues collide at \(t=2/5\) and the selected lower one-dimensional eigenspace changes from \(\operatorname{span}(e_1)\) to \(\operatorname{span}(e_2)\). Individual eigenvectors are not trackable through that collision without an additional selection rule.

### Source declaration excerpts

`DavisKahan/Sources/DavisKahan1970/SineTheta/Sharpness.lean` — `planarTrialMap` (exact declaration header; body omitted):

```lean
noncomputable def planarTrialMap (theta : ℝ) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/Sharpness.lean` — `planarAmbient` (exact declaration header; body omitted):

```lean
noncomputable def planarAmbient (delta : ℝ) :
    PlanarModelSpace 𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/Sharpness.lean` — `planarResidual` (exact declaration header; body omitted):

```lean
noncomputable def planarResidual (delta theta : ℝ) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
```

**Mapping.** `planarAmbient`, `planarTrialMap` and `planarResidual` model exact and trial geometry in two coordinates. The next lectures use the source's general `residual` function for a trial map and a trial operator. The examples here are elementary matrix calculations, and no claim is made that they are literally the input values of the cited Lean declarations.
