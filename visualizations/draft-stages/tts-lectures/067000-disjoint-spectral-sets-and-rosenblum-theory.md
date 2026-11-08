# 067000 — Disjoint spectral sets and Rosenblum theory

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `008000` resolvents; `030000` spectral projections; `063000–066000` Sylvester inversion and integral representations. **Next:** the Banach-space Theorem 5.1 lower bound.

<!-- BEGIN SPOKEN LECTURE -->

# Solve a Sylvester equation without self-adjointness

Our recent Sylvester proofs used self-adjoint operators. That allowed us to talk about real spectra, unitary groups, and ordered semigroups. Today we remove the self-adjoint assumption and replace it with a complex-analytic construction.

The central question is whether the spectra of two bounded operators are disjoint. For bounded complex operators on Banach spaces, this is enough for the Sylvester operator to have a bounded inverse. The method is associated with Rosenblum, and its engine is a contour integral of resolvents.

We will derive the algebraic identity that makes the contour work, first in scalar form and then for operators. We will also distinguish the theorem proved by a single circular contour from its more general version using a collection of contours.

## Recall the resolvent

Let A be a bounded operator. For a complex number z outside its spectrum, the operator z times the identity minus A has a bounded inverse. We call that inverse the resolvent of A at z.

The resolvent is a function of z. It is analytic away from the spectrum, and integrating it around a closed contour can select spectral components of the operator.

For a one-by-one matrix consisting of scalar a, the resolvent is just one over z minus a. Its integral around a positively oriented circle is two pi i if the circle encloses a and zero otherwise, after dividing by the usual normalization.

Thus contour integration can detect whether a spectral value lies inside a curve. In finite dimensions this follows from the residue theorem. For bounded Banach-space operators it is expressed by Riesz spectral projections.

## The two-resolvent integrand

Let A act on a Banach space Y and B act on another Banach space X. Our right-hand side C maps X to Y.

For a complex number z outside both spectra, form the resolvent of A at z, followed by C, followed by the resolvent of B at z. Call this operator K of z.

Notice the order. The right resolvent acts first on a vector in X, C sends that vector into Y, and the left resolvent then acts on Y. Every composition is type-correct even though the two Banach spaces need not be the same.

The proposed solution is the contour integral of K, divided by two pi i, over a positively oriented closed contour that encloses all of A's spectrum and none of B's spectrum.

Let's work out why this solves the Sylvester equation.

## The cancellation identity

Write R A for the resolvent of A and R B for the resolvent of B, evaluated at the same z.

Because z identity minus A multiplied by R A is the identity, we can rearrange to obtain A R A equals z R A minus the identity.

Similarly, R B multiplied by B equals z R B minus the identity. These identities do not require A or B to be self-adjoint.

Apply the Sylvester operator to K of z. The first term is A R A C R B. The second is R A C R B B.

Substitute the resolvent identities. The first becomes z R A C R B minus C R B. The second becomes z R A C R B minus R A C.

Subtracting cancels the z-dependent terms. What remains is R A C minus C R B.

That is the key cancellation. The complicated product of two resolvents has turned into the difference of two single-resolvent terms, which contour integration can evaluate.

## Integrate around the spectra

Assume first that a single circle contains all of A's spectrum strictly inside and contains no spectral value of B even in its closed disk.

Integrate the cancellation identity around that circle and divide by two pi i. The integral of the A resolvent becomes the identity operator, because the circle encloses all of A's spectrum. The integral of the B resolvent becomes zero, because B has no spectrum inside the circle.

Hence the integral of R A C minus C R B equals C. Because bounded composition commutes with the operator-valued contour integral, we obtain A times the proposed solution minus the proposed solution times B equals C.

Existence is proved. The formula is constructive, although it is an analytic construction rather than an entrywise division.

## Why uniqueness comes from the same computation

Suppose an arbitrary map X is given and let its Sylvester residual be A X minus X B.

Insert that residual into the same two-resolvent integrand. Using the resolvent identities in the opposite direction, one finds that R A times the residual times R B equals R A X minus X R B.

Integrate. The first term gives identity times X, and the second gives X times zero. The result is X itself.

Thus the contour construction is a left inverse of the Sylvester map as well as a right inverse. It follows that every C has exactly one solution. The Sylvester operator is an isomorphism of Banach spaces, because the contour integral defines a bounded linear map of C.

The norm of this inverse can be estimated using the length of the contour and the largest resolvent norms along it. But for nonnormal operators, resolvent norms can be large even when the contour remains a positive distance from the spectrum. So this argument alone does not produce a universal sharp constant depending only on spectral distance.

## Check the scalar case

Let A multiply by a and B multiply by b, with a different from b. Choose a circle containing a and excluding b. The integrand is C divided by the product of z minus a and z minus b.

The integrand has a simple pole at a inside the contour. Its residue is C divided by a minus b. The normalized contour integral therefore gives exactly that value.

We have recovered the scalar equation a X minus X b equals C, solved by division by a minus b. The contour formula is the complex-analytic version of that division.

For a diagonal matrix, the same residue calculation can be performed in every spectral block. The benefit of the contour method is that it continues to work for operators that are not diagonalizable, and even for bounded operators acting on infinite-dimensional Banach spaces.

## When one circle is not enough

A careful distinction is needed here. Disjoint compact spectra do not always admit one circle that encloses all of A's spectrum while excluding all of B's spectrum.

For example, let A have eigenvalues negative two and positive two, and let B have eigenvalue zero. The spectra are disjoint. Any closed disk containing both endpoints contains their midpoint zero, by convexity. So no single circle can contain all of A's spectrum inside its disk while excluding B's spectral value.

What do we do? Use a contour made from several positively oriented loops that together enclose A's spectral pieces but avoid B's spectrum. In finite dimensions, small disjoint circles around A's distinct eigenvalues suffice. For compact spectral subsets of the complex plane, one can construct an appropriate finite contour within the resolvent region, possibly using multiple components.

The same resolvent cancellation identity holds on each loop. Summing their integrals gives the full Riesz projection for A, which is the identity, and the zero projection for B. This proves the general bounded-operator Rosenblum result.

The specific Lean theorem used in our appendix proves existence and uniqueness with a separating circle. That theorem must not be presented as if its hypotheses already express every possible disjoint spectral arrangement. The broader contour extension is the mathematical generalization we have just explained.

## Connection to spectral projections

We met spectral projections earlier by selecting eigenspaces of a self-adjoint matrix. Riesz projections generalize that selection to operators with possibly complex spectra and nontrivial Jordan structure.

A Riesz projection associated with a contour is the normalized integral of the resolvent around that contour. It commutes with the original operator and projects onto the spectral component enclosed by the contour. Unlike an orthogonal spectral projection, it need not be self-adjoint for a nonnormal operator.

This explains why the Rosenblum proof is so flexible. It needs analytic resolvents and projection identities, not orthogonal eigenvectors or Hilbert geometry.

## What this lesson establishes

The Sylvester map is invertible for bounded complex Banach-space operators with disjoint spectra. The proof is based on resolvent cancellation, contour spectral projections, and the recovery of any unknown map from its own residual.

But there is a separate quantitative problem. How can we prove an explicit estimate for the size of a solution in a useful operator norm? When the spectra have additional separation geometry, an elementary inverse-based argument can give a constant-one bound even on Banach spaces.

That is the subject of the next lecture. Before moving on, derive the cancellation identity on paper and evaluate the scalar contour integral. Those two computations are the proof's core.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For \(R_A(z)=(zI-A)^{-1}\) and \(R_B(z)=(zI-B)^{-1}\),
\[
A\bigl(R_A(z)CR_B(z)\bigr)-\bigl(R_A(z)CR_B(z)\bigr)B
=R_A(z)C-CR_B(z).
\]
If a positively oriented contour \(\Gamma\) lies in the common resolvent set, encloses \(\sigma(A)\) and excludes \(\sigma(B)\), then
\[
X=\frac1{2\pi i}\oint_\Gamma R_A(z)CR_B(z)\,dz,
\qquad AX-XB=C.
\]
The complementary identity \(R_A(z)(AX-XB)R_B(z)=R_A(z)X-XR_B(z)\) proves uniqueness. The cited Lean existence/uniqueness theorem uses one positively oriented separating **circle**; general disjoint compact spectra may require a union of contour components, not covered by that exact theorem statement.

**Lean bridge (verbatim source excerpts).**

`DavisKahan/Sylvester/RosenblumExistence.lean` — `rosenblumSolution`:

```lean
noncomputable def rosenblumSolution (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (C : F →L[ℂ] E) (center radius : ℝ) : F →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∮ z in C((center : ℂ), radius), rosenblumIntegrand A B C z
```

The concrete contour solver uses circle integrals and bounded complex Banach-space operators.

`DavisKahan/Sylvester/RosenblumExistence.lean` — `existsUnique_comp_sub_comp_eq`:

```lean
theorem existsUnique_comp_sub_comp_eq (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    ∃! S : F →L[ℂ] E, A ∘L S - S ∘L B = C := by
```

The theorem proves both existence and uniqueness when **one circle** encloses the spectrum of `A` and its closed disk excludes the spectrum of `B`. It does not directly state the arbitrary-contour version.

