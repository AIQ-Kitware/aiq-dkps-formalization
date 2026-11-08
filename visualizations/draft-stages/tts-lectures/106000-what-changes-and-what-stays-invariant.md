# 106000 — What changes and what stays invariant

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `026000` finite spectral theorem; `027000` Rayleigh quotients; `031000` spectral gaps; `042000` principal angles; `105000` proof-readiness assembly. **Next:** `107000` trial spaces, exact subspaces and residuals.

<!-- BEGIN SPOKEN LECTURE -->

# What changes and what stays invariant

Perturbation theory asks how the spectral data of a self-adjoint operator change when the operator is modified. Eigenvalues may shift, eigenspaces may rotate, and individual eigenvectors may lose their identity when eigenvalues coincide. We will formulate the stable objects and the assumptions needed to control them.

There are two separate quantities to track. An eigenvalue is a number. An eigenspace is a geometric object. A numerical bound on moving eigenvalues does not, by itself, control the angle between the eigenspaces. We will see both claims in two-by-two matrices, prove an elementary eigenvalue stability estimate, and discover why spectral separation is indispensable for controlling subspaces.

## Begin with two energy levels

Take the plane with coordinates e one and e two. Let the original operator A multiply the first coordinate by zero and the second by four. Its lower eigenspace is the horizontal axis. Its upper eigenspace is the vertical axis. The spectral gap is four.

Now add a symmetric perturbation H whose diagonal entries are zero and whose off-diagonal entries are both one. The new operator B has diagonal entries zero and four and off-diagonal entries one.

To see how its eigenspaces rotate, take a unit vector that makes an angle theta with the horizontal axis. Its coordinates are cosine theta and sine theta. The Rayleigh quotient of B on this vector is four times sine squared theta plus two times sine theta times cosine theta.

Differentiate with respect to theta. The stationary directions obey a double-angle equation. Equivalently, diagonalizing the symmetric two-by-two matrix gives an acute rotation whose magnitude satisfies tangent of twice theta equals one half. Thus the lower eigenvector rotates by approximately thirteen point three degrees in magnitude. Its orientation can be chosen negative, since the positive off-diagonal coupling bends the lower eigenvector slightly below the horizontal axis.

The two eigenvalues are two minus the square root of five, and two plus the square root of five. Neither eigenvalue is still exactly zero or four. But both the eigenvalues and the eigendirections have moved continuously because a gap persists.

The size of H in operator norm is one. The two eigenvalue displacements each have magnitude the square root of five minus two, approximately zero point two three six. Notice that the eigenvectors moved in angle even though the eigenvalues moved by considerably less than one. Eigenvalue displacement and eigenvector rotation are different measurements.

## Prove the elementary eigenvalue bound

For a unit vector x, the difference between the Rayleigh quotients of A and B is its inner product with H x. Cauchy–Schwarz gives an absolute value at most the operator norm of H.

Apply that observation to the min–max characterization of the kth eigenvalue. Every minimum over subspaces and every maximum over unit vectors shifts by at most the same number. Consequently, when the ordered eigenvalues of A and B are paired in increasing order, the kth eigenvalue of B differs from the kth eigenvalue of A by at most the norm of H.

That is a version of Weyl's perturbation inequality. It makes no claim that the individual eigenvectors associated with those ordered numbers remain close. The inequality also remains valid at repeated eigenvalues, precisely where individual eigenvectors can become ambiguous.

## Watch a gap close and an eigenspace swap

Now change only the diagonal entries. Let A again be diagonal with entries zero and four. For a parameter t between zero and one, add t times the diagonal matrix with entries five and negative five. The resulting eigenvalues, before ordering, are five t and four minus five t.

At t equals zero, the lower eigenspace is the horizontal axis. At t equals one, the lower eigenspace is the vertical axis. Those two lines are perpendicular.

Where does the change occur? Set five t equal to four minus five t. The equality occurs at t equals two fifths. At that parameter the operator is a scalar multiple of the identity, so every line is an eigenspace. There is no uniquely distinguished lower one-dimensional eigenspace to follow through the crossing.

This shows why a theorem about subspace rotation needs a separation hypothesis. Merely knowing the size of the perturbation does not promise that a labeled spectral cluster remains isolated. Here the eigenvalues vary continuously, but the selection rule 'choose the lower eigenvector' jumps from one axis to the other at the collision.

The problem is not restricted to changing coordinates: the two exact spectral projections really are different. Before the crossing, the lower spectral projection sends a vector to its first coordinate. After the crossing, it sends a vector to its second coordinate.

## Stable clusters are more intrinsic than individual eigenvectors

Suppose an operator has a cluster containing two eigenvalues, perhaps repeated or nearly equal, and another cluster far away. Inside the first cluster the eigenvectors may mix freely. If those first two eigenvalues become equal, any orthonormal basis of their joint eigenspace is legitimate.

Tracking a particular eigenvector therefore depends on a choice that the mathematics does not always specify. Tracking the whole invariant subspace is more robust. Its orthogonal projection is independent of the basis chosen inside it.

For example, consider a three-dimensional diagonal operator with diagonal entries zero, zero, and ten. Its first two coordinates form a two-dimensional eigenspace. Rotating the basis inside that plane does not change the plane or its projection. If we perturb the two-by-two block slightly while leaving the third coordinate isolated, its individual eigenvectors may change greatly while the plane itself stays exactly fixed.

We should therefore formulate our target questions using subspaces, projections, and their principal angles. Those are the objects that continue to make sense through eigenvalue multiplicities within an isolated cluster.

## What separation must be maintained?

Imagine a selected interval containing the target eigenvalues of A and separated from the rest of its spectrum by a positive distance. Weyl's bound tells us that eigenvalues of B cannot travel farther than the perturbation norm. In finite dimensions, if the perturbation is sufficiently small relative to that separating distance, a contour or interval boundary can still isolate the corresponding number of eigenvalues of B.

That statement helps identify the appropriate perturbed cluster. But there are several different gap conditions in the literature. An ordered gap means one spectral set lies wholly to one side of another. A pairwise distance gap means every point of one set is some distance from every point of the other, without imposing order. Those conditions do not support every Sylvester norm estimate with the same constant.

We will always state which two operators are being separated, and whether the separation is ordered, interval-versus-exterior, or merely pairwise. This will prevent us from confusing a distance between an approximate eigenvalue and the nearest target eigenvalue with the distance to the exact complementary spectrum that actually appears in a sine theorem.

## The residual previews the answer

There is one more quantity to introduce before we state a perturbation theorem. Let u be a unit trial vector and let mu be a proposed eigenvalue. Its residual is A u minus mu times u. If that residual vanishes, u is an exact eigenvector with eigenvalue mu. If it is small, u is approximately invariant, but its angle to a particular eigenspace can still be large unless mu is spectrally separated from the unwanted eigenvalues.

In the first two-level example, choose the original horizontal basis vector as a trial vector for the perturbed operator B, and choose mu equal to its Rayleigh quotient, zero. The residual is exactly the vertical unit vector. Its norm is one. Its location in the complementary direction explains why the eigenvector rotates.

We will derive a matrix residual, compress it onto the exact complementary subspace, and turn it into a Sylvester equation. The operator on the other side of that equation will be the directed sine of a principal angle.

So our question is now precise. Given an exact reducing subspace, a trial subspace, a measurable residual, and an appropriate spectral gap, how large can the subspace angle be? The answer is a quantitative inequality, and we will prove it rather than memorize it.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `B=A+H` with self-adjoint matrices. Courant–Fischer gives `|λ_k(B)-λ_k(A)| ≤ ‖H‖`, but no analogous subspace estimate follows without separating the selected spectral sets. For `A=diag(0,4)` and `H=[[0,1],[1,0]]`, the lower eigendirection rotates through `θ=-(1/2) arctan(1/2)` and eigenvalues become `2±√5`. For `A(t)=diag(5t,4-5t)`, the lower spectral subspace changes at the collision `t=2/5`.

The exact source-backed sharpness model below supplies a distinct planar perturbation model used by the sine theorem. It is an analogy, not a formalization of both examples in this lecture.

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
