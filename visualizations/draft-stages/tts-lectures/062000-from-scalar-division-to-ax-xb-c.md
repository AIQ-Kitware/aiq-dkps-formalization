# 062000 — From scalar division to AX−XB=C

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `008000` resolvents; `024000` eigenvalues; `026000` spectral theorem; `031000` ordered versus distance gaps; `061000` form comparisons. **Next:** diagonal Sylvester solutions.

<!-- BEGIN SPOKEN LECTURE -->

# Why a spectral gap can make an operator equation solvable

Suppose we know a number c and want to recover an unknown number x from the equation a times x minus x times b equals c.

Because numbers commute, the left side is a minus b, multiplied by x. If a and b are different, we divide by their difference and obtain one solution. If a and b agree, either there is no solution or there are infinitely many, depending on whether c is zero.

This elementary observation is the seed of the Sylvester equation, a central tool in matrix perturbation theory and, eventually, the Davis–Kahan estimates.

For operators, the corresponding equation has A acting on one side of an unknown map X, and B acting on the other. The known map C is the defect we are trying to explain. Our job today is to understand what this equation asks, why differences of eigenvalues appear, and how separation of spectra controls the inverse problem.

The scalar equation and the finite spectral theorem already explain how the Sylvester operator can be inverted under spectral separation.

## Keep the domains and codomains straight

Let E and F be finite-dimensional inner-product spaces. Let B act from E to E, and let A act from F to F. The unknown X maps E into F, and the known right-hand side C also maps E into F.

Then A followed by X is a map from E to F. So is X followed by B. Their difference is well-defined, even when E and F have different dimensions.

The Sylvester equation says that A X minus X B equals C.

This form of the equation is important. The two terms represent different actions: A acts after X in the output space, while B acts before X in the input space. We cannot factor out X as if A and B were scalar numbers living in one commutative algebra.

Instead, we treat the whole expression as a linear transformation on the vector space of maps from E to F. Call that transformation the Sylvester operator associated with A and B.

Because composing with A and B is linear in X, the Sylvester operator is linear. Its invertibility is an ordinary linear-algebra question on a new, larger vector space.

## Return to the scalar case

Let a equal five and b equal two. If c equals twelve, the equation becomes five x minus two x equals twelve. The difference is three, so x equals four.

If c changes to negative six, x becomes negative two. The solution scales linearly with c because the equation itself is linear.

Now let a approach b. If their difference is one tenth and c is one, the solution has magnitude ten. If the difference is one hundredth, the solution has magnitude one hundred.

We already see the stability issue. Even when the solution is unique, it may be very sensitive to the right-hand side when a and b are close.

The quantity one divided by the absolute value of a minus b is the norm of the scalar inverse. It tells us how large the solution can be relative to the data.

If we demand that the absolute difference be at least a positive number delta, we obtain the bound: the magnitude of x is at most the magnitude of c divided by delta.

This is the simplest spectral-gap estimate.

## Eigenvectors reveal the same denominators

Now assume A and B are self-adjoint, so the finite spectral theorem supplies orthonormal eigenbases.

Let u be an eigenvector of A with eigenvalue a. Let v be an eigenvector of B with eigenvalue b.

We want to understand the component of X that sends v toward u. Take the inner product of the Sylvester equation applied to v with u.

For the first term, A X v, self-adjointness lets us move A to u. That produces a times the coefficient of X v along u.

For the second term, X B v, the eigenvalue equation B v equals b v. That produces b times the same coefficient.

Thus the component equation is precisely a minus b times the unknown coefficient of X, equal to the corresponding coefficient of C.

The scalar denominator reappears for every pair consisting of one eigenvalue of A and one eigenvalue of B.

This is the central structural fact. Instead of one division, the matrix equation needs a division for every spectral pair.

## What spectral separation means

The spectrum of a finite self-adjoint matrix is the finite set of its real eigenvalues. If A and B have no common eigenvalue, every spectral difference a minus b is nonzero.

Since there are only finitely many pairs, the smallest absolute difference is a positive number. Call it delta.

In this setting, the Sylvester equation has one solution for every right-hand side C.

If the spectra overlap, at least one denominator vanishes. On the corresponding pair of eigenspaces, the Sylvester operator cannot recover an arbitrary component of C. A nonzero right-hand-side component there makes the equation inconsistent. A zero component leaves the corresponding part of X undetermined.

So the spectral condition has two logical jobs. Nonzero differences give existence and uniqueness; a uniform positive lower bound on their magnitudes gives quantitative stability.

For finite self-adjoint matrices, disjoint spectra automatically provide a positive separation. For infinite spectra, a pair may have no common point and still approach arbitrarily close. There, the existence of a positive gap is genuinely stronger than set disjointness.

## Ordered gaps and mere distance gaps

Remember the distinction between ordered spectral sets. One hypothesis says every eigenvalue of A lies at least delta above every eigenvalue of B. That is an ordered gap.

A weaker hypothesis says every eigenvalue of A is at least delta away from every eigenvalue of B, without requiring A to lie entirely above or below B. That is a distance gap, also called pairwise spectral separation.

Either condition makes every scalar denominator nonzero. But the ordered condition also gives those denominators a common sign.

That sign coherence can support a simple integral formula for the Sylvester inverse: an exponential applied on the left decays while another exponential applied on the right compensates, and their combined decay is governed by delta.

With interlaced eigenvalues, the denominators can have opposite signs. The entrywise solution still exists, but a single one-sided decaying exponential formula does not capture all terms at once.

This distinction will matter when we ask how sharply the operator norm of X is bounded by the operator norm of C. A pairwise gap immediately gives a sharp Frobenius estimate in finite dimensions. A constant-one estimate for the operator norm follows under the stronger ordered-gap hypothesis; it does not follow from entrywise division alone for arbitrary interlaced spectra.

## The new operator on matrices

We can represent X by an m-by-n matrix. The entire space of such matrices has dimension m times n.

For each pair of eigenvectors u and v, consider the rank-one map that takes an input's component along v and sends it in the direction u. There are m times n such maps, and they form an orthonormal basis of the matrix space when it is equipped with the Frobenius inner product.

The Sylvester operator acts on that rank-one map by multiplication by the scalar a minus b. This is because left composition with A contributes a, and right composition with B contributes b.

Therefore the Sylvester operator is diagonal in this natural basis of matrix units. Its eigenvalues are all the pairwise differences between the eigenvalues of A and B, counted with multiplicities coming from the eigenvalue lists.

We have turned an operator equation into an ordinary diagonal linear system on the space of matrices.

This also makes the kernel transparent. Each zero spectral difference contributes a free matrix coefficient. If there are no zero differences, the Sylvester operator is invertible.

## Why we will need this in perturbation theory

Suppose we have two spectral subspaces and want to quantify the extent to which a perturbation couples them. A residual block may measure the failure of an approximate eigenspace to be invariant.

The desired correction block often obeys a Sylvester equation. The operators A and B represent restrictions to two spectral regions, and C represents the known residual.

If those spectral regions are separated, we can hope to solve for X and bound it in terms of C and the gap. This explains, at a structural level, why spectral separation appears in subspace perturbation estimates.

The eigenvalue differences are not decorative assumptions. They are the denominators of the inverse problem.

Next we will carry out the entire calculation in diagonal coordinates, including a numerical example, the exact compatibility condition when denominators vanish, and the Frobenius bound.

## What to reconstruct

Begin with the scalar equation and classify the cases a different from b and a equal to b. Verify the domain and codomain of every composition in A X minus X B.

Then use orthonormal eigenvectors u and v to derive the scalar coefficient equation. Explain how the spectral difference becomes an eigenvalue of the Sylvester operator acting on rank-one matrix units.

Finally, distinguish three claims: the spectra do not intersect, their pairwise distance has a positive lower bound, and they are ordered on opposite sides of a gap. Identify which claim is strongest and why the distinction affects operator-norm estimates.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For \(A:F\to F\), \(B:E\to E\) and \(X,C:E\to F\), define \(\mathcal S_{A,B}(X)=AX-XB\). If \(Au_i=a_i u_i\) and \(Bv_j=b_j v_j\), then in orthonormal eigenbases,
\[
\langle u_i,\mathcal S_{A,B}(X)v_j\rangle=(a_i-b_j)\langle u_i,Xv_j\rangle.
\]
The finite Sylvester operator is invertible iff \(a_i\ne b_j\) for every pair. Ordered spectral separation yields stronger integral representations than arbitrary pairwise separation; a sharp Frobenius bound holds in finite dimension under the latter.

**Lean bridge (verbatim excerpts).**

`DavisKahan/Sylvester/FiniteBlockReconstruction.lean`:

```lean
theorem finiteDiagonal_sylvester_block
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (X : E →L[ℂ] F) (i : Fin m) (j : Fin n) :
    P i ∘L (finiteDiagonalOperator P a ∘L X -
      X ∘L finiteDiagonalOperator Q b) ∘L Q j =
      (((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j) := by
```

A rectangular spectral block of the Sylvester defect equals its cross-eigenvalue difference times the corresponding block of the unknown map.

`DavisKahan/InfiniteDimensional/Sylvester/Basic.lean`:

```lean
theorem norm_sylvester_le_of_orderedSeparation
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec} {X C : Ec →L[ℂ] Fc}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : ContinuousLinearMap.sylvester A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
```

This source theorem states the sharp constant-one operator-norm bound under ordered spectral separation. It does not assert the same constant for interlaced arbitrary pairwise gaps.

**Reconstruction exercise:** Reprove the principal displayed identity from the spoken lecture, then identify the exact source/target types and extra assumptions in each displayed Lean declaration.
